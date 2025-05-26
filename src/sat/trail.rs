#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
use crate::sat::assignment::Assignment;
use crate::sat::clause::Clause;
use crate::sat::clause_storage::LiteralStorage;
use crate::sat::literal::Literal;
use crate::sat::solver::Solutions;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

/// The reason for a literal being in the trail.
///
/// This enum specifies why a particular literal was assigned.
#[derive(Debug, Clone, PartialEq, Eq, Default, Copy, Hash, PartialOrd, Ord)]
pub enum Reason {
    /// The literal was assigned as a decision by the solver.
    #[default]
    Decision,
    /// The literal was assigned because it was part of an initial unit clause.
    /// The `usize` stores the index of this unit clause in the original clause database.
    Unit(usize),
    /// The literal was assigned due to an implication from another clause.
    /// The `usize` stores the index of the implying clause.
    Clause(usize),
}

/// A step of the trail, representing a single literal assignment.
///
/// Each `Part` stores the assigned literal, the decision level at which
/// it was assigned, and the reason for the assignment.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Part<L: Literal> {
    /// The literal that was assigned.
    pub(crate) lit: L,
    /// The decision level at which this literal was assigned.
    /// Level 0 is for pre-assigned literals (e.g. from unit clauses).
    /// Subsequent levels correspond to solver decisions.
    decision_level: usize,
    /// The reason for this literal's assignment.
    pub(crate) reason: Reason,
}

/// The trail itself, storing the sequence of assignments and related metadata.
///
/// The trail is a fundamental data structure in a CDCL SAT solver. It maintains
/// the current partial assignment, the reasons for implications, and decision levels.
/// `L` is the literal type, and `S` is the literal storage type used by clauses.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Trail<L: Literal, S: LiteralStorage<L>> {
    /// The sequence of assignments (parts) forming the trail.
    pub(crate) t: Vec<Part<L>>,
    /// Index pointing to the next literal to be propagated in `t`.
    /// Assignments from `t[0]` to `t[curr_idx - 1]` have been processed (propagated).
    /// Assignments from `t[curr_idx]` onwards are pending propagation.
    pub curr_idx: usize,
    /// Maps a variable (by its `u32` ID) to the decision level at which it was assigned.
    /// `lit_to_level[var_id] = decision_level`.
    /// Stores 0 if the variable is unassigned or assigned at level 0.
    lit_to_level: Vec<usize>,
    /// Maps a variable (by its `u32` ID) to its position (index) in the `t` vector.
    /// `lit_to_pos[var_id] = index_in_t`.
    /// Stores 0 if the variable is unassigned (as `t[0]` is a valid position, this relies on
    /// checking `lit_to_level` or other means to confirm assignment for var at pos 0).
    /// More accurately, a non-zero value means it's assigned and on the trail.
    pub lit_to_pos: Vec<usize>,
    /// `PhantomData` to use the generic type `S` (`LiteralStorage`).
    marker: PhantomData<*const S>,
    /// Index separating original (non-learnt) clauses from learnt clauses.
    /// Clauses with an index less than `cnf_non_learnt_idx` are considered original.
    /// Clauses with an index greater than or equal to `cnf_non_learnt_idx` are learnt.
    /// This is used by `remap_clause_indices`.
    cnf_non_learnt_idx: usize,
}

impl<L: Literal, S: LiteralStorage<L>> Index<usize> for Trail<L, S> {
    type Output = Part<L>;

    /// Accesses a `Part` of the trail by its index.
    ///
    /// # Panics
    /// This method will panic if `index` is out of bounds.
    ///
    /// # Safety
    /// The `unsafe` block is used for a potential micro-optimisation by using
    /// `get_unchecked`.
    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.t.get_unchecked(index) }
    }
}

impl<L: Literal, S: LiteralStorage<L>> IndexMut<usize> for Trail<L, S> {
    /// Mutably accesses a `Part` of the trail by its index.
    ///
    /// # Panics
    /// This method will panic if `index` is out of bounds.
    ///
    /// # Safety
    /// Similar to `Index::index`, this uses `get_unchecked_mut`.
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { self.t.get_unchecked_mut(index) }
    }
}

impl<L: Literal, S: LiteralStorage<L>> Trail<L, S> {
    /// Returns the current decision level.
    ///
    /// The decision level is determined by the last assignment on the trail.
    /// If the trail is empty or only contains assignments at level 0, it returns 0.
    /// Otherwise, it returns the decision level of the assignment at `curr_idx - 1`.
    #[must_use]
    pub fn decision_level(&self) -> usize {
        if self.curr_idx == 0 {
            return 0;
        }

        let index = self.curr_idx - 1;
        self[index].decision_level
    }

    /// Returns the total number of assignments currently on the trail.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.t.len()
    }

    /// Checks if the trail is empty (contains no assignments).
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.t.is_empty()
    }

    /// Returns the decision level at which variable `v` was assigned.
    /// Returns 0 if the variable is unassigned or was assigned at level 0.
    ///
    /// # Safety
    /// This function uses `get_unchecked` and assumes `v` (cast to `usize`)
    /// is a valid index into `lit_to_level`. This means `v` must be less than
    /// `num_vars` used to initialise the `Trail`.
    #[must_use]
    pub fn level(&self, v: u32) -> usize {
        unsafe { *self.lit_to_level.get_unchecked(v as usize) }
    }

    /// Constructs a `Solutions` object from the current assignments on the trail.
    /// This represents a complete model if the solver found satisfiability.
    #[must_use]
    pub fn solutions(&self) -> Solutions {
        let literals = self.t.iter().map(|p| p.lit.to_i32()).collect_vec();
        Solutions::new(&literals)
    }

    /// Creates a new `Trail`.
    ///
    /// Initialises the trail, potentially adding assignments from unit clauses
    /// found in the initial `clauses` set. These initial assignments are at decision level 0.
    ///
    /// # Arguments
    /// * `clauses`: A slice of initial clauses. Unit clauses from this set will be
    ///   added to the trail.
    /// * `num_vars`: The total number of variables in the problem. This is used to
    ///   size internal mapping vectors.
    ///
    /// # Safety
    /// The internal initialisation of `lit_to_pos` for unit clauses uses `get_unchecked_mut`.
    /// This is safe if `lit.variable()` from a unit clause is less than `num_vars`.
    #[must_use]
    pub fn new(clauses: &[Clause<L, S>], num_vars: usize) -> Self {
        let mut lit_to_pos = vec![0; num_vars];

        let mut vec = Vec::with_capacity(num_vars);

        vec.extend(
            clauses
                .iter()
                .filter(|c| c.is_unit())
                .enumerate()
                .map(|(i, c)| {
                    let lit = c[0];
                    unsafe {
                        *lit_to_pos.get_unchecked_mut(lit.variable() as usize) = i;
                    }

                    Part {
                        lit,
                        decision_level: 0,
                        reason: Reason::Unit(i),
                    }
                }),
        );

        Self {
            t: vec,
            curr_idx: 0,
            lit_to_level: vec![0; num_vars],
            lit_to_pos,
            marker: PhantomData,
            cnf_non_learnt_idx: clauses.len(),
        }
    }

    /// Pushes a new assignment (literal) onto the trail.
    ///
    /// If the variable of the literal is already assigned, this function does nothing.
    /// Otherwise, it adds a new `Part` to the trail and updates `lit_to_level` and `lit_to_pos`.
    ///
    /// # Arguments
    /// * `lit`: The literal being assigned.
    /// * `decision_level`: The decision level at which this assignment occurs.
    /// * `reason`: The reason for this assignment.
    ///
    /// # Safety
    /// Uses `get_unchecked` to check `lit_to_pos` and `get_unchecked_mut` to update
    /// `lit_to_level` and `lit_to_pos`.
    pub fn push(&mut self, lit: L, decision_level: usize, reason: Reason) {
        unsafe {
            if *self.lit_to_pos.get_unchecked(lit.variable() as usize) != 0 {
                return;
            }
        }

        let pos = self.t.len();
        self.t.push(Part {
            lit,
            decision_level,
            reason,
        });
        let var = lit.variable() as usize;

        unsafe {
            *self.lit_to_level.get_unchecked_mut(var) = decision_level;
            *self.lit_to_pos.get_unchecked_mut(var) = pos;
        }
    }

    /// Resets the trail to an empty state.
    ///
    /// Clears all assignments and resets `curr_idx`, `lit_to_level`, and `lit_to_pos`.
    /// This is used during solver restarts.
    pub fn reset(&mut self) {
        self.t.clear();
        self.curr_idx = 0;
        self.lit_to_level.fill(0);
        self.lit_to_pos.fill(0);
    }

    /// Backtracks assignments to a specified decision level.
    ///
    /// Removes all assignments made at decision levels greater than or equal to `level`.
    /// For each removed assignment, it unassigns the corresponding variable in the `Assignment` object `a`.
    /// Updates `curr_idx` to point to the new end of the (propagated) trail.
    ///
    /// # Arguments
    /// * `a`: A mutable reference to the `Assignment` object to update.
    /// * `level`: The decision level to backtrack to. Assignments at this level and higher will be removed.
    ///
    /// # Safety
    /// Uses `get_unchecked` and `get_unchecked_mut` on `lit_to_level` and `lit_to_pos`.
    /// Assumes variable IDs from `self[i].lit.variable()` are valid indices.
    pub fn backstep_to<A: Assignment>(&mut self, a: &mut A, level: usize) {
        let mut truncate_at = 0;

        for i in (0..self.len()).rev() {
            let var = self[i].lit.variable();
            unsafe {
                if *self.lit_to_level.get_unchecked(var as usize) >= level {
                    a.unassign(var);
                    *self.lit_to_level.get_unchecked_mut(var as usize) = 0;
                    *self.lit_to_pos.get_unchecked_mut(var as usize) = 0;
                } else {
                    truncate_at = i;
                    break;
                }
            }
        }

        self.curr_idx = truncate_at;
        self.t.truncate(truncate_at);
    }

    /// Returns a list of clause indices that are "locked".
    ///
    /// A clause is considered locked if one of its literals is on the trail,
    /// and that literal was assigned as a result of an implication (i.e. `Reason::Clause`).
    /// Such clauses cannot be removed during database cleaning if the literal they implied
    /// is still on the trail, as they are part of the justification for the current assignment.
    #[must_use]
    pub fn get_locked_clauses(&self) -> SmallVec<[usize; 16]> {
        let mut locked = SmallVec::<[usize; 16]>::new();
        for part in &self.t {
            if let Reason::Clause(c_ref) = part.reason {
                locked.push(c_ref);
            }
        }
        locked.sort_unstable();
        locked.dedup();
        locked
    }

    /// Remaps clause indices stored in `Reason::Clause` variants on the trail.
    ///
    /// This is necessary after clause database cleanup operations (like removing
    /// redundant learnt clauses) where clause indices might change.
    /// Only indices of learnt clauses (those with original index `>= self.cnf_non_learnt_idx`)
    /// are considered for remapping.
    ///
    /// # Arguments
    /// * `map`: A hash map where keys are old clause indices and values are new clause indices.
    pub fn remap_clause_indices(&mut self, map: &FxHashMap<usize, usize>) {
        for part in &mut self.t {
            if let Reason::Clause(ref mut c_ref) = part.reason {
                if *c_ref >= self.cnf_non_learnt_idx {
                    if let Some(new_ref) = map.get(c_ref) {
                        *c_ref = *new_ref;
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::literal::{Literal as LiteralTrait, PackedLiteral};

    const NUM_VARS: usize = 5;

    type MockLit = PackedLiteral;
    type MockLiteralStorage = SmallVec<[PackedLiteral; 8]>;
    type MockClause = Clause<MockLit, MockLiteralStorage>;

    #[test]
    fn test_new_empty() {
        let clauses: [MockClause; 0] = [];
        let trail = Trail::<MockLit, MockLiteralStorage>::new(&clauses, NUM_VARS);
        assert!(trail.is_empty());
        assert_eq!(trail.curr_idx, 0);
        assert_eq!(trail.lit_to_level.len(), NUM_VARS);
        assert_eq!(trail.lit_to_pos.len(), NUM_VARS);
        assert!(trail.lit_to_level.iter().all(|&lvl| lvl == 0));
        assert!(trail.lit_to_pos.iter().all(|&pos| pos == 0));
        assert_eq!(trail.cnf_non_learnt_idx, 0);
    }

    fn l(lit: i32) -> PackedLiteral {
        PackedLiteral::from_i32(lit)
    }

    #[test]
    fn test_new_with_unit_clauses() {
        let clauses = [
            std::iter::once(1).collect::<MockClause>(),
            std::iter::once(-2).collect::<MockClause>(),
            [1, 3].into_iter().collect::<MockClause>(),
        ];
        let trail = Trail::<MockLit, MockLiteralStorage>::new(&clauses, NUM_VARS);

        assert_eq!(trail.len(), 2);
        assert_eq!(trail.curr_idx, 0);

        assert_eq!(trail[0].lit, l(1));
        assert_eq!(trail[0].decision_level, 0);
        assert_eq!(trail[0].reason, Reason::Unit(0));
        assert_eq!(trail.level(0), 0);
        assert_eq!(trail.lit_to_pos[0], 0);

        assert_eq!(trail[1].lit, l(-2));
        assert_eq!(trail[1].decision_level, 0);
        assert_eq!(trail[1].reason, Reason::Unit(1));
        assert_eq!(trail.level(1), 0);
        assert_eq!(trail.lit_to_pos[1], 0);

        assert_eq!(trail.level(2), 0);
        assert_eq!(trail.lit_to_pos[2], 1);

        assert_eq!(trail.cnf_non_learnt_idx, 3);
    }

    #[test]
    fn test_push_simple() {
        let mut trail = Trail::<MockLit, MockLiteralStorage>::new(&[], NUM_VARS);
        trail.reset();

        let lit1 = l(1);
        trail.push(lit1, 1, Reason::Decision);

        assert_eq!(trail.len(), 1);
        assert_eq!(trail[0].lit, lit1);
        assert_eq!(trail[0].decision_level, 1);
        assert_eq!(trail[0].reason, Reason::Decision);
        assert_eq!(trail.level(0), 0);
        assert_eq!(trail.lit_to_pos[0], 0);

        let lit2 = l(-2);
        trail.push(lit2, 1, Reason::Clause(0));

        assert_eq!(trail.len(), 2);
        assert_eq!(trail[1].lit, lit2);
        assert_eq!(trail[1].decision_level, 1);
        assert_eq!(trail[1].reason, Reason::Clause(0));
        assert_eq!(trail.level(1), 1);
        assert_eq!(trail.lit_to_pos[1], 0);
    }

    #[test]
    fn test_push_already_assigned_due_to_pos_not_zero() {
        let mut trail = Trail::<MockLit, MockLiteralStorage>::new(&[], NUM_VARS);
        trail.reset();

        trail.push(l(1), 1, Reason::Decision);
        assert_eq!(trail.len(), 1);

        trail.push(l(2), 1, Reason::Decision);
        assert_eq!(trail.len(), 2);
        assert_eq!(trail.lit_to_pos[1], 0);

        trail.push(l(2), 1, Reason::Decision);
        assert_eq!(trail.len(), 2);

        trail.push(l(1), 1, Reason::Decision);
        assert_eq!(
            trail.len(),
            3,
            "Bug: Re-pushed var 0 because lit_to_pos[0] == 0"
        );
    }

    #[test]
    fn test_decision_level() {
        let mut trail = Trail::<MockLit, MockLiteralStorage>::new(&[], NUM_VARS);
        assert_eq!(trail.decision_level(), 0);

        trail.push(l(1), 1, Reason::Decision);
        trail.curr_idx = 1;
        assert_eq!(trail.decision_level(), 1);

        trail.push(l(2), 1, Reason::Clause(0));
        trail.curr_idx = 2;
        assert_eq!(trail.decision_level(), 1);

        trail.push(l(3), 2, Reason::Decision);
        trail.curr_idx = 3;
        assert_eq!(trail.decision_level(), 2);

        trail.curr_idx = 0;
        assert_eq!(trail.decision_level(), 0);
    }

    #[test]
    fn test_len_is_empty() {
        let mut trail = Trail::<MockLit, MockLiteralStorage>::new(&[], NUM_VARS);
        assert_eq!(trail.len(), 0);
        assert!(trail.is_empty());

        trail.push(l(1), 1, Reason::Decision);
        assert_eq!(trail.len(), 1);
        assert!(!trail.is_empty());
    }

    #[test]
    fn test_level() {
        let mut trail = Trail::<MockLit, MockLiteralStorage>::new(&[], NUM_VARS);
        trail.reset();

        assert_eq!(trail.level(0), 0);

        trail.push(l(1), 1, Reason::Decision);
        assert_eq!(trail.level(0), 0);
        assert_eq!(trail.level(1), 1);

        trail.push(l(-3), 2, Reason::Decision);
        assert_eq!(trail.level(2), 0);
    }

    #[test]
    fn test_solutions() {
        let mut trail = Trail::<MockLit, MockLiteralStorage>::new(&[], NUM_VARS);
        trail.reset();

        let sol_empty = trail.solutions();
        assert!(sol_empty.is_empty());
    }

    #[test]
    fn test_reset() {
        let clauses = [std::iter::once(1).collect::<MockClause>()];
        let mut trail = Trail::<MockLit, MockLiteralStorage>::new(&clauses, NUM_VARS);

        assert_eq!(trail.len(), 1);
        assert_eq!(trail.level(0), 0);
        assert_eq!(trail.lit_to_pos[0], 0);

        trail.push(l(2), 1, Reason::Decision);
        assert_eq!(trail.len(), 2);
        assert_eq!(trail.level(1), 0);
        assert_eq!(trail.lit_to_pos[1], 0);

        trail.reset();
        assert!(trail.is_empty());
        assert_eq!(trail.curr_idx, 0);
        assert!(trail.lit_to_level.iter().all(|&lvl| lvl == 0));
        assert!(trail.lit_to_pos.iter().all(|&pos| pos == 0));
    }

    #[test]
    fn test_remap_clause_indices() {
        let mut trail = Trail::<MockLit, MockLiteralStorage>::new(&[], NUM_VARS);
        trail.reset();
        trail.cnf_non_learnt_idx = 50;

        trail.push(l(1), 1, Reason::Clause(10));
        trail.push(l(2), 1, Reason::Clause(100));
        trail.push(l(3), 1, Reason::Clause(101));
        trail.push(l(4), 1, Reason::Clause(102));

        let mut map = FxHashMap::default();
        map.insert(100, 70);
        map.insert(101, 71);

        trail.remap_clause_indices(&map);

        assert_eq!(trail[0].reason, Reason::Clause(10));
        assert_eq!(trail[1].reason, Reason::Clause(70));
        assert_eq!(trail[2].reason, Reason::Clause(71));
        assert_eq!(trail[3].reason, Reason::Clause(102));
    }
}
