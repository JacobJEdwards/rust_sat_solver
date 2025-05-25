#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
//! Defines traits and implementations for literal propagation in a SAT solver.
//!
//! Propagation is the process of deducing new assignments based on the current
//! partial assignment and the clauses of the formula. The most common form is
//! Unit Propagation: if a clause becomes unit (all but one of its literals are
//! false, and the remaining one is unassigned), then that remaining literal
//! must be assigned true to satisfy the clause.
//!
//! This module provides:
//! - The `Propagator` trait, defining a common interface for different propagation strategies.
//! - `WatchedLiterals`: An efficient implementation of unit propagation using the
//!   watched literals scheme. Each clause watches two of its non-false literals.
//!   Propagation only needs to occur when one of these watched literals becomes false.
//! - `UnitSearch`: A simpler, less optimised propagator that iterates through all clauses
//!   to find unit clauses or conflicts.
//! - `UnitPropagationWithPureLiterals`: A propagator that combines unit propagation
//!   with the heuristic of assigning pure literals (literals that appear with only
//!   one polarity in the remaining active formula).

use crate::sat::assignment::Assignment;
use crate::sat::clause::Clause;
use crate::sat::clause_storage::LiteralStorage;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use crate::sat::literal::Variable;
use crate::sat::preprocessing::PureLiteralElimination;
use crate::sat::trail::{Reason, Trail};
use itertools::Itertools;
use smallvec::SmallVec;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

/// Trait defining the interface for a literal propagation mechanism.
///
/// Implementors of this trait are responsible for identifying and applying
/// consequences of the current partial assignment (e.g. unit propagation).
///
/// # Type Parameters
///
/// * `L`: The `Literal` type.
/// * `S`: The `LiteralStorage` type for clauses.
/// * `A`: The `Assignment` type managing variable states.
pub trait Propagator<L: Literal, S: LiteralStorage<L>, A: Assignment>: Debug + Clone {
    /// Creates a new propagator instance
    ///
    /// # Arguments
    ///
    /// * `cnf`: A reference to the `Cnf` formula.
    fn new(cnf: &Cnf<L, S>) -> Self;

    /// Informs the propagator about a new clause being added to the formula.
    /// This is particularly relevant for watched literal schemes to set up watches.
    ///
    /// # Arguments
    ///
    /// * `clause`: The clause being added.
    /// * `idx`: The index of the clause in the `Cnf`'s clause list.
    fn add_clause(&mut self, clause: &Clause<L, S>, idx: usize);

    /// Performs propagation based on the current assignments in the `trail`.
    ///
    /// It iterates through newly assigned literals on the `trail` (those not yet processed
    /// by `propagate`) and deduces further assignments. Enqueued assignments are added
    /// to the `trail` and `assignment` state.
    ///
    /// # Arguments
    ///
    /// * `trail`: Mutable reference to the `Trail`, where new propagations are enqueued.
    /// * `assignment`: Mutable reference to the `Assignment` state.
    /// * `cnf`: Mutable reference to the `Cnf` formula (e.g. for clause access, modification for watched literals).
    ///
    /// # Returns
    ///
    /// - `Some(clause_idx)` if a conflict is detected (clause at `clause_idx` is falsified).
    /// - `None` if propagation completes without conflict.
    fn propagate(
        &mut self,
        trail: &mut Trail<L, S>,
        assignment: &mut A,
        cnf: &mut Cnf<L, S>,
    ) -> Option<usize>;

    /// Returns the total number of propagations performed by this instance.
    fn num_propagations(&self) -> usize;

    /// Helper function to add a propagated literal to the trail.
    ///
    /// This is a static method often used by propagator implementations.
    /// The propagated literal is assigned at the current decision level of the trail.
    ///
    /// # Arguments
    ///
    /// * `lit`: The literal being propagated.
    /// * `clause_idx`: The index of the clause that forced this propagation (the reason).
    /// * `trail`: Mutable reference to the `Trail`.
    fn add_propagation(lit: L, clause_idx: usize, trail: &mut Trail<L, S>) {
        trail.push(lit, trail.decision_level(), Reason::Clause(clause_idx));
    }

    /// Cleans up internal propagator state related to learnt clauses.
    ///
    /// When learnt clauses are removed or re-indexed during clause database cleaning,
    /// the propagator (especially watched literals) needs to update its references.
    ///
    /// # Arguments
    ///
    /// * `learnt_idx`: An index used to determine which watches to clean. For example,
    ///   watches to clauses with indices `>= learnt_idx` might be removed if
    ///   that part of the clause database was rebuilt.
    fn cleanup_learnt(&mut self, learnt_idx: usize);
}

/// Implements unit propagation using the watched literals scheme (also known as two-watched literals or 2WL).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct WatchedLiterals<L: Literal, S: LiteralStorage<L>, A: Assignment, const N: usize = 8> {
    watches: Vec<SmallVec<[usize; N]>>,
    num_propagations: usize,
    marker: PhantomData<*const (L, S, A)>,
}

impl<L: Literal, S: LiteralStorage<L> + Debug, A: Assignment, const N: usize> Propagator<L, S, A>
    for WatchedLiterals<L, S, A, N>
{
    fn new(cnf: &Cnf<L, S>) -> Self {
        let num_literal_indices = if cnf.num_vars == 0 {
            0
        } else {
            cnf.num_vars * 2
        };
        let st = vec![SmallVec::new(); num_literal_indices];

        let mut wl = Self {
            watches: st,
            num_propagations: 0,
            marker: PhantomData,
        };

        for (i, clause) in cnf
            .iter()
            .enumerate()
            .filter(|(_, c)| c.len() >= 2 && !c.is_unit() && !c.is_deleted())
        {
            wl.add_clause(clause, i);
        }
        wl
    }

    fn add_clause(&mut self, clause: &Clause<L, S>, idx: usize) {
        if clause.len() < 2 || clause.is_deleted() {
            return;
        }
        let a = clause[0];
        let b = clause[1];
        debug_assert_ne!(
            a.variable(),
            b.variable(),
            "Clause {idx}: Attempting to watch two \
        literals of the same variable: {a:?} and {b:?}"
        );

        self[a].push(idx);
        self[b].push(idx);
    }

    fn propagate(
        &mut self,
        trail: &mut Trail<L, S>,
        assignment: &mut A,
        cnf: &mut Cnf<L, S>,
    ) -> Option<usize> {
        while trail.curr_idx < trail.len() {
            let lit = trail[trail.curr_idx].lit;
            trail.curr_idx = trail.curr_idx.wrapping_add(1);
            assignment.assign(lit);
            self.num_propagations = self.num_propagations.wrapping_add(1);

            let watch_list_clone = self[lit.negated().index()].clone();
            if let Some(idx) = self.propagate_watch(&watch_list_clone, trail, assignment, cnf) {
                return Some(idx);
            }
        }
        None
    }

    fn num_propagations(&self) -> usize {
        self.num_propagations
    }

    fn cleanup_learnt(&mut self, learnt_idx: usize) {
        for i in &mut self.watches {
            i.retain(|&mut j| j < learnt_idx);
        }
    }
}

impl<L: Literal, S: LiteralStorage<L> + Debug, A: Assignment, const N: usize>
    WatchedLiterals<L, S, A, N>
{
    pub fn propagate_watch(
        &mut self,
        indices: &[usize],
        trail: &mut Trail<L, S>,
        assignment: &A,
        cnf: &mut Cnf<L, S>,
    ) -> Option<usize> {
        indices
            .iter()
            .find_map(|&idx| self.process_clause(idx, trail, assignment, cnf))
    }

    pub fn process_clause(
        &mut self,
        clause_idx: usize,
        trail: &mut Trail<L, S>,
        assignment: &A,
        cnf: &mut Cnf<L, S>,
    ) -> Option<usize> {
        let clause = &mut cnf[clause_idx];

        let first = clause[0];
        let second = clause[1];

        let first_value = assignment.literal_value(first);

        if first_value == Some(true) {
            return None;
        }

        let second_value = assignment.literal_value(second);

        match (first_value, second_value) {
            (Some(false), Some(false)) => {
                debug_assert!(
                    clause
                        .iter()
                        .all(|&l| assignment.literal_value(l) == Some(false)),
                    "Clause: {clause:?} is not false, Values: {:?}, idx: {clause_idx}, trail: \
                    {:?}",
                    clause
                        .iter()
                        .map(|&l| assignment.literal_value(l))
                        .collect_vec(),
                    trail,
                );
                Some(clause_idx)
            }
            (None, Some(false)) => {
                self.handle_false(first, clause_idx, assignment, cnf, trail);
                None
            }
            (Some(false), None) => {
                clause.swap(0, 1);
                self.handle_false(second, clause_idx, assignment, cnf, trail);
                None
            }
            (_, Some(true)) => {
                clause.swap(0, 1);
                None
            }
            (Some(true), _) | (None, None) => None,
        }
    }

    fn handle_false(
        &mut self,
        other_lit: L,
        clause_idx: usize,
        assignment: &A,
        cnf: &mut Cnf<L, S>,
        trail: &mut Trail<L, S>,
    ) {
        if let Some(new_lit_idx) = Self::find_new_watch(clause_idx, cnf, assignment) {
            self.handle_new_watch(clause_idx, new_lit_idx, cnf);
        } else {
            debug_assert!(
                assignment.literal_value(other_lit).is_none(),
                "In handle_false, \
            other_lit ({other_lit:?}) was expected to be unassigned but is {:?}. Clause idx \
            {clause_idx}",
                assignment.literal_value(other_lit)
            );
            Self::add_propagation(other_lit, clause_idx, trail);
        }
    }

    fn find_new_watch(clause_idx: usize, cnf: &Cnf<L, S>, assignment: &A) -> Option<usize> {
        let clause = &cnf[clause_idx];
        clause
            .iter()
            .skip(2)
            .position(|&l| assignment.literal_value(l) != Some(false))
            .map(|i| i.wrapping_add(2))
    }

    fn handle_new_watch(&mut self, clause_idx: usize, new_lit_idx: usize, cnf: &mut Cnf<L, S>) {
        debug_assert!(new_lit_idx >= 2);

        let new_lit = cnf[clause_idx][new_lit_idx];
        let prev_lit = cnf[clause_idx][1];

        cnf[clause_idx].swap(1, new_lit_idx);

        self[new_lit].push(clause_idx);

        if let Some(pos) = self[prev_lit].iter().position(|&i| i == clause_idx) {
            self[prev_lit].swap_remove(pos);
        }
    }
}

impl<L: Literal, S: LiteralStorage<L>, A: Assignment, const N: usize> Index<usize>
    for WatchedLiterals<L, S, A, N>
{
    type Output = SmallVec<[usize; N]>;
    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.watches.get_unchecked(index) }
    }
}

impl<L: Literal, S: LiteralStorage<L>, A: Assignment, const N: usize> IndexMut<usize>
    for WatchedLiterals<L, S, A, N>
{
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { self.watches.get_unchecked_mut(index) }
    }
}

impl<L: Literal, S: LiteralStorage<L>, A: Assignment, const N: usize> Index<Variable>
    for WatchedLiterals<L, S, A, N>
{
    type Output = SmallVec<[usize; N]>;
    #[inline]
    fn index(&self, index: Variable) -> &Self::Output {
        &self[index as usize]
    }
}

impl<L: Literal, S: LiteralStorage<L>, A: Assignment, const N: usize> IndexMut<Variable>
    for WatchedLiterals<L, S, A, N>
{
    #[inline]
    fn index_mut(&mut self, index: Variable) -> &mut Self::Output {
        &mut self[index as usize]
    }
}

impl<L: Literal, S: LiteralStorage<L>, A: Assignment, const N: usize> Index<L>
    for WatchedLiterals<L, S, A, N>
{
    type Output = SmallVec<[usize; N]>;
    #[inline]
    fn index(&self, index: L) -> &Self::Output {
        &self[index.index()]
    }
}

impl<L: Literal, S: LiteralStorage<L>, A: Assignment, const N: usize> IndexMut<L>
    for WatchedLiterals<L, S, A, N>
{
    #[inline]
    fn index_mut(&mut self, index: L) -> &mut Self::Output {
        &mut self[index.index()]
    }
}

/// A simple unit propagation strategy that iterates through all clauses.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct UnitSearch<L: Literal, S: LiteralStorage<L>, A: Assignment>(
    usize, // num_propagations
    PhantomData<(L, S, A)>,
);

impl<L: Literal, S: LiteralStorage<L>, A: Assignment> Propagator<L, S, A> for UnitSearch<L, S, A> {
    fn new(_: &Cnf<L, S>) -> Self {
        Self(0, PhantomData)
    }

    fn add_clause(&mut self, _: &Clause<L, S>, _: usize) {}

    fn propagate(
        &mut self,
        trail: &mut Trail<L, S>,
        assignment: &mut A,
        cnf: &mut Cnf<L, S>,
    ) -> Option<usize> {
        loop {
            let mut new_propagations_this_scan = false;
            while trail.curr_idx < trail.len() {
                let lit = trail[trail.curr_idx].lit;
                trail.curr_idx = trail.curr_idx.wrapping_add(1);
                assignment.assign(lit);
                self.0 = self.0.wrapping_add(1);
            }

            match Self::process_cnf_scan(trail, assignment, cnf) {
                Some(ScanResult::Conflict(idx)) => return Some(idx),
                Some(ScanResult::Propagated) => new_propagations_this_scan = true,
                None => {}
            }

            if !new_propagations_this_scan && trail.curr_idx == trail.len() {
                return None;
            }
        }
    }

    fn num_propagations(&self) -> usize {
        self.0
    }

    fn cleanup_learnt(&mut self, _: usize) {}
}

enum UnitSearchResult<L: Literal> {
    Unsat(usize),
    Unit(L),
    Continue,
}

enum ScanResult {
    Conflict(usize),
    Propagated,
}

impl<L: Literal, S: LiteralStorage<L>, A: Assignment> UnitSearch<L, S, A> {
    fn process_cnf_scan(
        trail: &mut Trail<L, S>,
        assignment: &A,
        cnf: &Cnf<L, S>,
    ) -> Option<ScanResult> {
        let mut propagated_in_scan = false;
        for (idx, clause) in cnf.iter().enumerate() {
            if clause.is_deleted() {
                continue;
            }
            match Self::process_clause_eval(clause, assignment, idx) {
                UnitSearchResult::Unsat(idx) => return Some(ScanResult::Conflict(idx)),
                UnitSearchResult::Unit(lit) => {
                    if assignment.var_value(lit.variable()).is_none() {
                        Self::add_propagation(lit, idx, trail);
                        propagated_in_scan = true;
                    }
                }
                UnitSearchResult::Continue => {}
            }
        }
        if propagated_in_scan {
            Some(ScanResult::Propagated)
        } else {
            None
        }
    }

    fn process_clause_eval(
        clause: &Clause<L, S>,
        assignment: &A,
        idx: usize,
    ) -> UnitSearchResult<L> {
        let mut unassigned_lit_opt = None;
        let mut num_unassigned = 0;

        for &lit in clause.iter() {
            match assignment.literal_value(lit) {
                Some(true) => return UnitSearchResult::Continue,
                Some(false) => {}
                None => {
                    num_unassigned += 1;
                    if unassigned_lit_opt.is_none() {
                        unassigned_lit_opt = Some(lit);
                    }
                    if num_unassigned > 1 {
                        return UnitSearchResult::Continue;
                    }
                }
            }
        }

        if num_unassigned == 1 {
            UnitSearchResult::Unit(
                unassigned_lit_opt
                    .expect("num_unassigned is 1, so unassigned_lit_opt must be Some"),
            )
        } else if num_unassigned == 0 {
            UnitSearchResult::Unsat(idx)
        } else {
            UnitSearchResult::Continue
        }
    }
}

/// A propagator that combines `UnitSearch` with periodic pure literal assignment.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct UnitPropagationWithPureLiterals<L: Literal, S: LiteralStorage<L>, A: Assignment>(
    UnitSearch<L, S, A>,
);

impl<L: Literal, S: LiteralStorage<L>, A: Assignment> Propagator<L, S, A>
    for UnitPropagationWithPureLiterals<L, S, A>
{
    fn new(cnf: &Cnf<L, S>) -> Self {
        Self(UnitSearch::new(cnf))
    }

    fn add_clause(&mut self, clause: &Clause<L, S>, idx: usize) {
        self.0.add_clause(clause, idx);
    }

    fn propagate(
        &mut self,
        trail: &mut Trail<L, S>,
        assignment: &mut A,
        cnf: &mut Cnf<L, S>,
    ) -> Option<usize> {
        loop {
            if let Some(idx) = self.0.propagate(trail, assignment, cnf) {
                return Some(idx);
            }

            let trail_len_before_pures = trail.len();
            let curr_idx_before_pures = trail.curr_idx;

            Self::find_pure_literals_assign(trail, assignment, cnf);

            if curr_idx_before_pures == trail.len() && trail_len_before_pures == trail.len() {
                return None;
            }
        }
    }

    fn num_propagations(&self) -> usize {
        self.0.num_propagations()
    }

    fn cleanup_learnt(&mut self, learnt_idx: usize) {
        self.0.cleanup_learnt(learnt_idx);
    }
}

impl<L: Literal, S: LiteralStorage<L>, A: Assignment> UnitPropagationWithPureLiterals<L, S, A> {
    fn find_pure_literals_assign(trail: &mut Trail<L, S>, assignment: &A, cnf: &Cnf<L, S>) {
        let pures = PureLiteralElimination::find_pures(&cnf.clauses);
        for &lit in &pures {
            if assignment.var_value(lit.variable()).is_none() {
                Self::add_propagation(lit, 0, trail);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::assignment::VecAssignment;
    use crate::sat::literal::PackedLiteral;

    type TestLiteral = PackedLiteral;
    type TestClauseStorage = SmallVec<[TestLiteral; 8]>;
    type TestCnf = Cnf<TestLiteral, TestClauseStorage>;
    type TestAssignment = VecAssignment;
    type TestTrail = Trail<TestLiteral, TestClauseStorage>;

    fn lit(val: i32) -> TestLiteral {
        TestLiteral::from_i32(val)
    }

    fn setup_test_environment(
        clauses_dimacs: Vec<Vec<i32>>,
        num_total_vars: usize,
    ) -> (TestCnf, TestTrail, TestAssignment) {
        let mut cnf = TestCnf::new(clauses_dimacs);
        let effective_num_vars = cnf.num_vars.max(num_total_vars);
        cnf.num_vars = effective_num_vars;

        let trail = TestTrail::new(&cnf.clauses, effective_num_vars);
        let assignment = TestAssignment::new(effective_num_vars);
        (cnf, trail, assignment)
    }

    #[test]
    fn test_watched_literals_new_and_add_clause() {
        let (cnf, _trail, _assignment) =
            setup_test_environment(vec![vec![1, 2, -3], vec![-1, 4]], 5);
        let propagator = WatchedLiterals::<_, _, TestAssignment>::new(&cnf);

        assert_eq!(propagator.watches.len(), cnf.num_vars * 2);

        assert!(propagator[lit(1)].contains(&0));
        assert!(propagator[lit(2)].contains(&0));
        assert!(!propagator[lit(-3)].contains(&0));

        assert!(propagator[lit(-1)].contains(&1));
        assert!(propagator[lit(4)].contains(&1));
    }

    #[test]
    fn test_watched_literals_simple_propagation() {
        let (mut cnf, mut trail, mut assignment) =
            setup_test_environment(vec![vec![-1, 2], vec![-2, 3]], 4);
        let mut propagator = WatchedLiterals::<_, _, TestAssignment>::new(&cnf);

        trail.push(lit(1), 1, Reason::Decision);

        let conflict = propagator.propagate(&mut trail, &mut assignment, &mut cnf);
        assert!(conflict.is_none());

        assert_eq!(trail.len(), 3);
        assert_eq!(trail.t[0].lit, lit(1));
        assert_eq!(trail.t[1].lit, lit(2));
        assert_eq!(trail.t[1].reason, Reason::Clause(0));
        assert_eq!(trail.t[2].lit, lit(3));
        assert_eq!(trail.t[2].reason, Reason::Clause(1));

        assert_eq!(assignment.literal_value(lit(1)), Some(true));
        assert_eq!(assignment.literal_value(lit(2)), Some(true));
        assert_eq!(assignment.literal_value(lit(3)), Some(true));
        assert_eq!(propagator.num_propagations(), 3);
    }

    #[test]
    fn test_watched_literals_conflict() {
        let (mut cnf, mut trail, mut assignment) =
            setup_test_environment(vec![vec![-1, 2], vec![-1, -2]], 3);
        let mut propagator = WatchedLiterals::<_, _, TestAssignment>::new(&cnf);

        trail.push(lit(1), 1, Reason::Decision);

        let conflict_idx = propagator.propagate(&mut trail, &mut assignment, &mut cnf);
        assert!(conflict_idx.is_some());
        assert_eq!(conflict_idx.unwrap(), 1);
    }

    #[test]
    fn test_watched_literals_find_new_watch() {
        let (mut cnf, mut trail, mut assignment) =
            setup_test_environment(vec![vec![-1, 2, 3, -4]], 5);
        let mut propagator = WatchedLiterals::<_, _, TestAssignment>::new(&cnf);

        trail.push(lit(1), 1, Reason::Decision);

        let conflict = propagator.propagate(&mut trail, &mut assignment, &mut cnf);
        assert!(conflict.is_none());

        assert!(propagator[lit(2)].contains(&0));
        assert!(propagator[lit(3)].contains(&0));
        assert!(!propagator[lit(-1)].contains(&0));
        assert!(!propagator[lit(-4)].contains(&0));
    }

    #[test]
    fn test_unit_search_simple_propagation() {
        let (mut cnf, mut trail, mut assignment) =
            setup_test_environment(vec![vec![-1, 2], vec![-2, 3]], 4);
        let mut propagator = UnitSearch::new(&cnf);

        trail.push(lit(1), 1, Reason::Decision);
        let conflict = propagator.propagate(&mut trail, &mut assignment, &mut cnf);

        assert!(conflict.is_none());
        assert_eq!(trail.len(), 3);
        assert_eq!(trail.t[0].lit, lit(1));
        assert_eq!(trail.t[1].lit, lit(2));
        assert_eq!(trail.t[2].lit, lit(3));
        assert_eq!(assignment.var_value(lit(3).variable()), Some(true));
        assert_eq!(propagator.num_propagations(), 3);
    }

    #[test]
    fn test_unit_search_conflict() {
        let (mut cnf, mut trail, mut assignment) =
            setup_test_environment(vec![vec![-1, 2], vec![-1, -2]], 3);
        let mut propagator = UnitSearch::new(&cnf);
        trail.push(lit(1), 1, Reason::Decision);
        let conflict_idx = propagator.propagate(&mut trail, &mut assignment, &mut cnf);
        assert!(conflict_idx.is_some());
        assert_eq!(conflict_idx.unwrap(), 1);
    }

    #[test]
    fn test_unit_prop_with_pures() {
        let (mut cnf, mut trail, mut assignment) =
            setup_test_environment(vec![vec![-1, 2], vec![3]], 4);
        let mut propagator = UnitPropagationWithPureLiterals::new(&cnf);

        trail.push(lit(1), 1, Reason::Decision);
        let conflict = propagator.propagate(&mut trail, &mut assignment, &mut cnf);

        assert!(conflict.is_none());
        assert_eq!(trail.len(), 3);

        assert_eq!(assignment.var_value(lit(3).variable()), Some(true));
    }

    #[test]
    fn test_watched_literals_empty_cnf() {
        let (cnf, _trail, _assignment) = setup_test_environment(vec![], 1);
        let propagator = WatchedLiterals::<_, _, TestAssignment>::new(&cnf);
        assert_eq!(propagator.watches.len(), 2);
    }

    #[test]
    fn test_watched_literals_unit_clause_in_cnf() {
        let (cnf, _trail, _assignment) = setup_test_environment(vec![vec![1], vec![-2, 3]], 4);
        let propagator = WatchedLiterals::<_, _, TestAssignment>::new(&cnf);
        assert!(!propagator[lit(1)].contains(&0));
        assert!(propagator[lit(-2)].contains(&1));
        assert!(propagator[lit(3)].contains(&1));
    }
}
