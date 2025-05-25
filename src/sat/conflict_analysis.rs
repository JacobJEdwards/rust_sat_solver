#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
//! Defines functions and structures related to conflict analysis in a SAT solver.
//!
//! Conflict analysis is a cornerstone of modern CDCL (Conflict-Driven Clause Learning)
//! SAT solvers. When a conflict (a clause where all literals are false under the
//! current assignment) is detected, the solver analyses the chain of implications
//! (the "implication graph") that led to the conflict. This analysis aims to:
//! 1. Identify a "learnt clause" that explains the conflict and can prevent similar
//!    conflicts in the future. This clause is typically asserting, meaning it will
//!    become unit after backtracking.
//! 2. Determine a backtrack level: the decision level to which the solver should
//!    backtrack to resolve the conflict and continue the search.
//!
//! This module provides:
//! - The `Conflict` enum to represent different outcomes of conflict analysis.
//! - The `Analyser` struct, which encapsulates the state and logic for performing
//!   conflict analysis (using the 1UIP - First Unique Implication Point scheme).

use crate::sat::assignment::Assignment;
use crate::sat::clause::Clause;
use crate::sat::clause_storage::LiteralStorage;
use crate::sat::cnf::Cnf;
use crate::sat::literal::{Literal, Variable};
use crate::sat::trail::{Reason, Trail};
use bit_vec::BitVec;
use smallvec::SmallVec;

/// Represents the outcome of a conflict analysis.
///
/// This enum categorises the result of analysing a conflict, which guides the solver's
/// next actions (e.g. learning a clause, backtracking, restarting).
///
/// # Type Parameters
///
/// * `T`: The type of `Literal` used in clauses.
/// * `S`: The `LiteralStorage` type used within clauses.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub enum Conflict<T: Literal, S: LiteralStorage<T>> {
    /// A conflict at decision level 0 (ground level) was found.
    /// This means the original formula is unsatisfiable. No clause is learnt.
    #[default]
    Ground,
    /// A unit clause was learnt from the conflict.
    /// This clause will propagate a literal immediately after backtracking.
    Unit(Clause<T, S>),
    /// A non-unit clause was learnt.
    /// The `usize` is the index of the asserting literal within the learnt clause.
    /// The `Learned` variant indicates the clause is asserting at some backtrack level.
    Learned(usize, Clause<T, S>),
    /// The conflict analysis suggests a restart is beneficial.
    Restart(Clause<T, S>),
}

/// Encapsulates the state and methods for performing conflict analysis.
///
/// Using a struct allows for reusing allocations (like `seen` and `to_bump`)
/// across multiple conflict analyses, which can improve performance.
///
/// # Type Parameters
///
/// * `T`: The type of `Literal`.
/// * `S`: The `LiteralStorage` type for clauses.
/// * `N`: A compile-time constant for the inline capacity of `to_bump` `SmallVec`.
///   Defaults to 12, a common small size for literals involved in resolution steps.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Analyser<T: Literal, S: LiteralStorage<T>, const N: usize = 12> {
    /// A bit vector to mark variables that have been "seen" (processed)
    /// during the current conflict analysis. Size is `num_vars`.
    seen: BitVec,
    /// Counts the number of literals in the current resolvent (conflict clause being built)
    /// that belong to the current decision level. This helps find the 1UIP.
    path_c: usize,
    /// A small vector to store literals from clauses involved in the conflict.
    /// These literals might be used to bump variable activities (VSIDS heuristic).
    to_bump: SmallVec<[T; N]>,
    /// Phantom data to associate the generic types `T` and `S` with the struct.
    data: std::marker::PhantomData<*const (T, S)>,

    /// A counter for the number of conflicts analysed for statistics.
    pub count: usize,
}

impl<T: Literal, S: LiteralStorage<T>, const N: usize> Analyser<T, S, N> {
    /// Initialises a new `Analyser`.
    ///
    /// # Arguments
    ///
    /// * `num_vars`: The total number of variables in the formula, used to size the `seen` vector.
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            seen: BitVec::from_elem(num_vars, false),
            path_c: 0,
            to_bump: SmallVec::with_capacity(N),
            data: std::marker::PhantomData,
            count: 0,
        }
    }

    /// Checks if a variable (identified by its `Variable` ID) has been marked as seen.
    ///
    /// # Arguments
    ///
    /// * `var_id`: The `Variable` ID to check.
    ///
    /// # Safety
    ///
    /// Uses `get_unchecked` assuming `var_id` (cast to `usize`) is a valid index into `seen`.
    /// This is generally safe if `num_vars` was correctly provided at construction and
    /// `var_id` is always less than `num_vars`.
    #[inline]
    fn is_seen(&self, var_id: Variable) -> bool {
        unsafe { self.seen.get_unchecked(var_id as usize) }
    }

    /// Marks a variable as seen.
    ///
    /// # Arguments
    ///
    /// * `var_id`: The `Variable` ID to mark.
    ///
    /// # Safety
    ///
    /// Uses `get_unchecked_mut` with similar safety assumptions as `is_seen`.
    #[inline]
    fn set_seen(&mut self, var_id: Variable) {
        unsafe {
            *self.seen.get_unchecked_mut(var_id as usize) = true;
        }
    }

    /// Marks a variable as not seen (resets its seen status).
    ///
    /// # Arguments
    ///
    /// * `var_id`: The `Variable` ID to unmark.
    ///
    /// # Safety
    ///
    /// Uses `get_unchecked_mut` with similar safety assumptions as `is_seen`.
    #[inline]
    fn unset_seen(&mut self, var_id: Variable) {
        unsafe {
            *self.seen.get_unchecked_mut(var_id as usize) = false;
        }
    }

    /// Performs a resolution step in the conflict analysis.
    ///
    /// Given a current conflict clause `c` (resolvent) and another clause `o` (the antecedent
    /// of a literal `pivot_lit` in `c`), this function resolves `c` with `o` on the variable `pivot_var`.
    /// The literal corresponding to `pivot_var` in `c` is removed, and literals from `o`
    /// (excluding `pivot_lit.negated()`) are added to `c` if they are not already effectively present
    /// (i.e. their variable is not seen, and they are false under current assignment at a lower level).
    ///
    /// # Arguments
    ///
    /// * `c`: Mutable reference to the current resolvent clause.
    /// * `o`: Reference to the antecedent clause.
    /// * `assignment`: The current variable assignment, to check literal values.
    /// * `pivot_var`: The variable of the literal being resolved out of `c`.
    /// * `c_idx_of_pivot_lit`: The index of the literal (related to `pivot_var`) in `c` to be removed.
    /// * `trail`: The assignment trail, to check decision levels.
    fn resolve(
        &mut self,
        c: &mut Clause<T, S>,
        o: &Clause<T, S>,
        assignment: &impl Assignment,
        pivot_var: Variable,
        c_idx_of_pivot_lit: usize,
        trail: &Trail<T, S>,
    ) {
        c.remove_literal(c_idx_of_pivot_lit);
        self.path_c = self.path_c.saturating_sub(1);
        self.unset_seen(pivot_var);

        for &lit_from_o in o.iter() {
            let var_from_o = lit_from_o.variable();
            if !self.is_seen(var_from_o) && assignment.literal_value(lit_from_o) == Some(false) {
                self.set_seen(var_from_o);
                self.to_bump.push(lit_from_o);
                c.push(lit_from_o);

                if trail.level(var_from_o) >= trail.decision_level() {
                    self.path_c = self.path_c.wrapping_add(1);
                }
            }
        }
    }

    /// Chooses the next literal from the trail to resolve with.
    ///
    /// Iterates backwards on the trail from current position `i`.
    /// Finds the most recently assigned literal on the trail whose variable is currently "seen"
    /// (i.e. present in the resolvent `c`). This literal will be the next pivot for resolution.
    ///
    /// # Arguments
    ///
    /// * `c`: The current resolvent clause.
    /// * `trail`: The assignment trail.
    /// * `i`: Mutable reference to the current index on the trail (updated by this function).
    ///
    /// # Returns
    ///
    /// `Some(k)` where `k` is the index of the chosen pivot literal in `c`.
    /// `None` if no suitable literal is found (e.g. trail exhausted before 1UIP condition met).
    fn choose_literal(
        &self,
        c: &Clause<T, S>,
        trail: &Trail<T, S>,
        i: &mut usize,
    ) -> Option<usize> {
        while *i > 0 {
            *i -= 1;
            let current_trail_entry = &trail[*i];
            let var_on_trail = current_trail_entry.lit.variable();

            if self.is_seen(var_on_trail) {
                for k in 0..c.len() {
                    if var_on_trail == c[k].variable() {
                        return Some(k);
                    }
                }
            }
        }
        None
    }

    /// Performs conflict analysis starting from a conflicting clause.
    ///
    /// This implements a 1UIP (First Unique Implication Point) learning scheme.
    /// It iteratively resolves the conflicting clause with antecedents of literals
    /// on the trail until a learnt clause is derived.
    ///
    /// # Arguments
    ///
    /// * `cnf`: The CNF formula, to get antecedent clauses.
    /// * `trail`: The assignment trail.
    /// * `assignment`: The current variable assignments.
    /// * `conflicting_clause_ref`: Index of the initially conflicting clause in `cnf`.
    ///
    /// # Returns
    ///
    /// A tuple `(Conflict<T, S>, SmallVec<[T; N]>)`:
    /// - The `Conflict` outcome (e.g. learnt clause, ground, restart).
    /// - A `SmallVec` of literals involved in the conflict, for activity bumping.
    pub(crate) fn analyse_conflict(
        &mut self,
        cnf: &Cnf<T, S>,
        trail: &Trail<T, S>,
        assignment: &impl Assignment,
        conflicting_clause_ref: usize,
    ) -> (Conflict<T, S>, SmallVec<[T; N]>) {
        self.count = self.count.wrapping_add(1);
        self.reset_for_analysis(cnf.num_vars);

        let current_decision_level = trail.decision_level();

        let mut resolvent_clause = cnf[conflicting_clause_ref].clone();
        self.path_c = 0;

        for &lit in resolvent_clause.iter() {
            let var = lit.variable();
            self.set_seen(var);
            self.to_bump.push(lit);
            if trail.level(var) >= current_decision_level {
                self.path_c = self.path_c.wrapping_add(1);
            }
        }

        let mut trail_idx = trail.len();

        while self.path_c > usize::from(current_decision_level != 0) {
            let Some(idx_in_resolvent_of_pivot) =
                self.choose_literal(&resolvent_clause, trail, &mut trail_idx)
            else {
                break;
            };

            let antecedent_reason = trail[trail_idx].reason;
            let antecedent_clause = match antecedent_reason {
                Reason::Clause(ante_idx) | Reason::Unit(ante_idx) => cnf[ante_idx].clone(),
                Reason::Decision => break,
            };

            let pivot_var = trail[trail_idx].lit.variable();

            self.resolve(
                &mut resolvent_clause,
                &antecedent_clause,
                assignment,
                pivot_var,
                idx_in_resolvent_of_pivot,
                trail,
            );
        }

        // was having problems with teh constructed clause being not all false
        debug_assert!(
            resolvent_clause
                .iter()
                .all(|&lit| assignment.literal_value(lit) == Some(false)),
            "Learnt clause not entirely false under current assignment!"
        );

        let literals_to_bump = self.to_bump.clone();

        if resolvent_clause.is_empty() {
            (Conflict::Ground, literals_to_bump)
        } else if resolvent_clause.is_unit() {
            (Conflict::Unit(resolvent_clause), literals_to_bump)
        } else {
            if current_decision_level > 0 && self.path_c != 1 {
                return (Conflict::Restart(resolvent_clause), literals_to_bump);
            }

            let mut asserting_lit_idx_in_clause: usize = 0;
            let mut max_trail_pos_at_dl = 0;

            for k in 0..resolvent_clause.len() {
                let var = resolvent_clause[k].variable();
                if trail.level(var) == current_decision_level {
                    let pos_on_trail = trail.lit_to_pos[var as usize];
                    if pos_on_trail > max_trail_pos_at_dl {
                        max_trail_pos_at_dl = pos_on_trail;
                        asserting_lit_idx_in_clause = k;
                    }
                }
            }
            (
                Conflict::Learned(asserting_lit_idx_in_clause, resolvent_clause),
                literals_to_bump,
            )
        }
    }

    /// Resets the analyser's state for a new conflict analysis.
    /// Clears `seen` bits, `path_c`, and `to_bump` list.
    /// This should be called before `analyse_conflict`.
    fn reset_for_analysis(&mut self, num_vars: usize) {
        if self.seen.len() == num_vars {
            self.seen.clear();
        } else {
            self.seen = BitVec::from_elem(num_vars, false);
        }
        self.path_c = 0;
        self.to_bump.clear();
    }
}

#[cfg(test)]
mod tests {
    // use super::*;
    // use crate::sat::assignment::{Assignment, VecAssignment};
    // use crate::sat::clause::Clause;
    // use crate::sat::cnf::Cnf;
    // use crate::sat::literal::PackedLiteral;
    // use crate::sat::trail::{Reason, Trail};
    // use smallvec::SmallVec;
    // 
    // type TestLiteral = PackedLiteral;
    // type TestClauseStorage = SmallVec<[TestLiteral; 8]>;
    // type TestAnalyser = Analyser<TestLiteral, TestClauseStorage, 12>;
    // 
    // #[test]
    // fn test_analyse_ground_conflict() {
    //     let mut cnf = Cnf::<TestLiteral, TestClauseStorage>::default();
    //     cnf.clauses.push(Clause::from(vec![1]));
    //     cnf.clauses.push(Clause::from(vec![-1]));
    //     cnf.num_vars = 2;
    //     cnf.non_learnt_idx = 2;
    // 
    //     let mut assignment = VecAssignment::default();
    //     assignment.set(1, true);
    // 
    //     let mut trail = Trail::new(cnf.clauses.as_ref(), cnf.num_vars);
    //     trail.push(TestLiteral::new(1, true), 0, Reason::Decision);
    //     trail.push(TestLiteral::new(1, false), 0, Reason::Clause(0));
    // 
    //     let mut analyser = TestAnalyser::new(cnf.num_vars);
    //     let (conflict_type, _to_bump) = analyser.analyse_conflict(&cnf, &trail, &assignment, 1);
    // 
    //     match conflict_type {
    //         Conflict::Unit(learnt_clause) => {
    //             assert_eq!(learnt_clause.len(), 1);
    //             assert_eq!(learnt_clause[0], TestLiteral::from_i32(-1));
    //         }
    //         Conflict::Ground => {}
    //         other => panic!("Expected Ground or Unit conflict, got {other:?}"),
    //     }
    //     assert_eq!(analyser.count, 1);
    // }
    // 
    // #[test]
    // fn test_analyse_simple_1uip_conflict() {
    //     let mut cnf = Cnf::<TestLiteral, TestClauseStorage>::default();
    //     cnf.clauses.push([-1, 2].into_iter().collect::<Clause<_>>());
    //     cnf.clauses.push([-1, 3].into_iter().collect::<Clause<_>>());
    //     cnf.clauses
    //         .push([-2, -3].into_iter().collect::<Clause<_>>());
    //     cnf.num_vars = 4;
    //     cnf.non_learnt_idx = 3;
    // 
    //     let mut assignment = VecAssignment::default();
    //     assignment.set(1, true);
    //     assignment.set(2, true);
    //     assignment.set(3, true);
    // 
    //     let mut trail = Trail::new(cnf.clauses.as_ref(), cnf.num_vars);
    //     trail.push(TestLiteral::new(1, true), 0, Reason::Decision);
    //     trail.push(TestLiteral::new(2, true), 0, Reason::Decision);
    //     trail.push(TestLiteral::new(3, true), 0, Reason::Clause(1));
    // 
    //     let mut analyser = TestAnalyser::new(cnf.num_vars);
    //     let (conflict_type, to_bump) = analyser.analyse_conflict(&cnf, &trail, &assignment, 2);
    // 
    //     match conflict_type {
    //         Conflict::Unit(learnt_clause) => {
    //             assert_eq!(learnt_clause.len(), 1);
    //             assert_eq!(learnt_clause[0], TestLiteral::from_i32(-1));
    //         }
    //         other => panic!("Expected Unit conflict, got {other:?}"),
    //     }
    // 
    //     assert!(to_bump.contains(&TestLiteral::from_i32(-1)));
    //     assert!(to_bump.contains(&TestLiteral::from_i32(-2)));
    //     assert!(to_bump.contains(&TestLiteral::from_i32(-3)));
    //     assert_eq!(to_bump.len(), 3);
    //     assert_eq!(analyser.count, 1);
    // }
}
