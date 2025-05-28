#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
//! This module defines strategies for managing the clause database in a SAT solver.
//!
//! Clause management is crucial for the performance of modern SAT solvers, especially
//! Conflict-Driven Clause Learning (CDCL) solvers. As solvers learn new clauses
//! during conflict analysis, the clause database can grow very large. Effective
//! management strategies aim to:
//! - Periodically remove less useful learnt clauses to keep the database size manageable.
//! - Prioritise keeping "high-quality" clauses (e.g. those with low LBD or high activity).
//! - Decay clause activities to reflect their recent involvement in conflicts.
//!
//! This module provides a `ClauseManagement` trait that abstracts these strategies,
//! along with concrete implementations like `LbdClauseManagement` (which uses
//! Literal Blocks Distance and activity scores) and `NoClauseManagement` (a no-op strategy).

use crate::sat::assignment::Assignment;
use crate::sat::clause::Clause;
use crate::sat::clause_management::ClauseManagementImpls::LbdActivityClauseManagement;
use crate::sat::clause_storage::LiteralStorage;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use crate::sat::propagation::Propagator;
use crate::sat::trail::Trail;
use clap::ValueEnum;
use rustc_hash::{FxHashMap, FxHashSet};
use std::fmt::{Debug, Display};

/// A constant factor used to decay clause activities.
const DECAY_FACTOR: f64 = 0.95;

/// Trait defining the interface for clause database management strategies.
///
/// Implementors of this trait control when and how the clause database (specifically
/// learnt clauses) is pruned or maintained.
///
/// # Type Parameters
///
/// * `L`: The type of `Literal` used in clauses.
/// * `S`: The `LiteralStorage` type used within clauses.
pub trait ClauseManagement: Clone + Debug + Default {
    /// Creates a new instance of the clause management strategy.
    ///
    /// # Arguments
    ///
    /// * `clauses`: An initial slice of clauses. This might be used to initialise
    ///   internal structures
    fn new<L: Literal, S: LiteralStorage<L>>(clauses: &[Clause<L, S>]) -> Self;

    /// Called by the solver after a conflict occurs and a new clause might have been learnt.
    ///
    /// This method allows the strategy to update its internal state, such as
    /// incrementing conflict counters or decaying clause activities.
    ///
    /// # Arguments
    ///
    /// * `cnf`: A mutable reference to the `Cnf` formula, allowing modification of clause activities.
    fn on_conflict<L: Literal, S: LiteralStorage<L>>(&mut self, cnf: &mut Cnf<L, S>);

    /// Determines whether the clause database should be cleaned.
    ///
    /// This is typically based on a conflict counter reaching a certain interval.
    ///
    /// # Returns
    ///
    /// `true` if the database cleaning process should be triggered, `false` otherwise.
    fn should_clean_db(&self) -> bool;

    /// Performs the clause database cleaning operation.
    ///
    /// This method identifies and removes learnt clauses deemed less useful.
    /// It needs to coordinate with other solver components like the `Trail` (to handle
    /// reasons for assignments) and the `Propagator` (to update watched literals).
    ///
    /// # Arguments
    ///
    /// * `cnf`: A mutable reference to the `Cnf` formula, from which clauses will be removed.
    /// * `trail`: A mutable reference to the `Trail`, to update clause indices used as reasons.
    /// * `propagator`: A mutable reference to the `Propagator`, to update its internal clause references.
    /// * `assignment`: A mutable reference to the `Assignment` (currently unused by `LbdClauseManagement`).
    fn clean_clause_db<L: Literal, S: LiteralStorage<L>, P: Propagator<L, S, A>, A: Assignment>(
        &mut self,
        cnf: &mut Cnf<L, S>,
        trail: &mut Trail<L, S>,
        propagator: &mut P,
        assignment: &mut A,
    );

    /// Bumps the activity of clauses involved in deriving a new learnt clause.
    ///
    /// Typically, the learnt clause itself and potentially clauses used in its resolution
    /// have their activity increased.
    ///
    /// # Arguments
    ///
    /// * `cnf`: A mutable reference to the `Cnf` formula, to access and modify the clause.
    /// * `c_ref`: The index of the clause whose activity should be bumped (often the newly learnt clause).
    fn bump_involved_clause_activities<L: Literal, S: LiteralStorage<L>>(
        &mut self,
        cnf: &mut Cnf<L, S>,
        c_ref: usize,
    );

    /// Returns the total number of clauses removed by this management strategy so far.
    fn num_removed(&self) -> usize;
}

/// A clause management strategy based on Literal Blocks Distance (LBD) and activity.
///
/// This strategy periodically cleans the learnt clause database by:
/// 1. Identifying candidate learnt clauses for removal (those not locked by the trail).
/// 2. Sorting candidates: clauses with LBD <= 2 are prioritised to be kept.
///    Among others, clauses with lower LBD are preferred, and then lower activity (as less active clauses are removed).
/// 3. Removing roughly half of the worst-ranking candidates.
/// 4. Clause activities are decayed after each conflict.
///
/// # Type Parameters
///
/// * `L`: The type of `Literal`.
/// * `S`: The `LiteralStorage` type.
/// * `N`: A compile-time constant defining the conflict interval at which database cleaning is considered.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct LbdClauseManagement<const N: usize> {
    /// The interval (number of conflicts) between database cleaning attempts.
    interval: usize,
    /// Counter for conflicts since the last database cleanup.
    conflicts_since_last_cleanup: usize,
    /// Total number of clauses removed by this strategy.
    num_removed: usize,

    /// Buffer for storing candidates for removal: (`original_index`, lbd, activity).
    candidates: Vec<(usize, u32, f64)>,
    /// Set of original indices of clauses selected for removal.
    indices_to_remove: FxHashSet<usize>,
    /// Buffer for storing learnt clauses that are kept after cleaning.
    new_learnt_clauses: Vec<Vec<i32>>,
    /// Map from old clause indices to new clause indices after compaction.
    old_to_new_idx_map: FxHashMap<usize, usize>,
}

impl<const N: usize> ClauseManagement for LbdClauseManagement<N> {
    /// Creates a new `LbdClauseManagement` instance.
    ///
    /// Initialises internal buffers and sets the cleaning interval based on `N`.
    /// The initial `clauses` slice is used to estimate initial capacities but not directly stored.
    fn new<L: Literal, S: LiteralStorage<L>>(clauses: &[Clause<L, S>]) -> Self {
        let initial_capacity = clauses.len();
        let candidates = Vec::with_capacity(initial_capacity);

        let mut indices_to_remove = FxHashSet::default();
        indices_to_remove.reserve(initial_capacity);

        let new_learnt_clauses = Vec::with_capacity(initial_capacity);

        let mut old_to_new_idx_map = FxHashMap::default();
        old_to_new_idx_map.reserve(initial_capacity);

        Self {
            interval: N,
            conflicts_since_last_cleanup: 0,
            num_removed: 0,
            candidates,
            indices_to_remove,
            new_learnt_clauses,
            old_to_new_idx_map,
        }
    }

    /// Increments the conflict counter and decays activities of all learnt clauses.
    fn on_conflict<L: Literal, S: LiteralStorage<L>>(&mut self, cnf: &mut Cnf<L, S>) {
        self.conflicts_since_last_cleanup = self.conflicts_since_last_cleanup.wrapping_add(1);
        Self::decay_clause_activities(cnf);
    }

    /// Returns `true` if `conflicts_since_last_cleanup` has reached the `interval`.
    fn should_clean_db(&self) -> bool {
        self.conflicts_since_last_cleanup >= self.interval
    }

    /// Cleans the learnt clause database.
    ///
    /// - Selects learnt clauses not locked by the trail as removal candidates.
    /// - Sorts candidates:
    ///   - Clauses with LBD <= 2 are strongly preferred (kept).
    ///   - Otherwise, lower LBD is better (kept).
    ///   - For equal LBD, lower activity is worse (removed).
    /// - Removes approximately half of the "worst" candidates.
    /// - Rebuilds the learnt part of the `Cnf`'s clause list.
    /// - Updates `Trail` and `Propagator` with remapped clause indices.
    /// - Resets the conflict counter.
    ///
    /// The `assignment` parameter is currently unused by this implementation.
    fn clean_clause_db<L: Literal, S: LiteralStorage<L>, P: Propagator<L, S, A>, A: Assignment>(
        &mut self,
        cnf: &mut Cnf<L, S>,
        trail: &mut Trail<L, S>,
        propagator: &mut P,
        _assignment: &mut A,
    ) {
        let learnt_start_idx = cnf.non_learnt_idx;
        if cnf.len() <= learnt_start_idx {
            return;
        }

        self.candidates.clear();
        let locked_clauses = trail.get_locked_clauses();

        for idx in learnt_start_idx..cnf.len() {
            if !locked_clauses.contains(&idx) {
                let clause = &cnf[idx];
                self.candidates.push((idx, clause.lbd, clause.activity()));
            }
        }

        if self.candidates.is_empty() {
            return;
        }

        let num_candidates = self.candidates.len();
        let num_to_remove = num_candidates / 2;

        if num_to_remove == 0 {
            return;
        }

        let comparison = |a: &(usize, u32, f64), b: &(usize, u32, f64)| {
            let (_, lbd_a, act_a) = a;
            let (_, lbd_b, act_b) = b;

            let keep_a_heuristic = *lbd_a <= 2;
            let keep_b_heuristic = *lbd_b <= 2;

            if keep_a_heuristic && !keep_b_heuristic {
                return std::cmp::Ordering::Greater;
            }
            if !keep_a_heuristic && keep_b_heuristic {
                return std::cmp::Ordering::Less;
            }

            match lbd_a.cmp(lbd_b) {
                // lower LBD is better
                std::cmp::Ordering::Equal => act_a
                    .partial_cmp(act_b)
                    .unwrap_or(std::cmp::Ordering::Equal),
                other_lbd_cmp => other_lbd_cmp.reverse(),
            }
        };

        self.candidates
            .select_nth_unstable_by(num_to_remove, comparison);

        self.indices_to_remove.clear();
        for (idx, _, _) in self.candidates.iter().take(num_to_remove) {
            self.indices_to_remove.insert(*idx);
        }

        let mut new_learnt_clauses = Vec::with_capacity(num_to_remove);
        self.old_to_new_idx_map.clear();

        let mut current_new_idx = learnt_start_idx;
        for old_idx in learnt_start_idx..cnf.len() {
            if !self.indices_to_remove.contains(&old_idx) {
                new_learnt_clauses.push(cnf[old_idx].clone());
                self.old_to_new_idx_map.insert(old_idx, current_new_idx);
                current_new_idx = current_new_idx.wrapping_add(1);
            }
        }

        let new_learnt_count = self.new_learnt_clauses.len();
        let new_total_len = learnt_start_idx.wrapping_add(new_learnt_count);

        // update CNF by replacing old learnt clauses with the filtered list
        cnf.clauses.truncate(learnt_start_idx);
        cnf.clauses.append(&mut new_learnt_clauses);

        trail.remap_clause_indices(&self.old_to_new_idx_map);

        propagator.cleanup_learnt(learnt_start_idx);
        for new_idx in learnt_start_idx..new_total_len {
            // add watches for kept learnt clauses
            propagator.add_clause(&cnf[new_idx], new_idx);
        }

        self.conflicts_since_last_cleanup = 0;
        self.num_removed = self.num_removed.wrapping_add(num_to_remove);
    }

    /// Bumps the activity of the specified clause.
    ///
    /// In this strategy, only the referenced clause itself has its activity bumped by a fixed amount (1.0).
    fn bump_involved_clause_activities<L: Literal, S: LiteralStorage<L>>(
        &mut self,
        cnf: &mut Cnf<L, S>,
        c_ref: usize,
    ) {
        let clause = &mut cnf[c_ref];
        clause.bump_activity(1.0);
    }

    /// Returns the total number of clauses removed so far.
    fn num_removed(&self) -> usize {
        self.num_removed
    }
}

impl<const N: usize> LbdClauseManagement<N> {
    /// Decays the activity of all learnt clauses by a fixed factor.
    /// This is called after each conflict.
    fn decay_clause_activities<L: Literal, S: LiteralStorage<L>>(cnf: &mut Cnf<L, S>) {
        for clause in &mut cnf.clauses[cnf.non_learnt_idx..] {
            clause.decay_activity(DECAY_FACTOR);
        }
    }
}

/// A clause management strategy that performs no operations.
///
/// This strategy does not clean the clause database, bump activities, or decay them.
///
/// # Type Parameters
///
/// * `L`: The type of `Literal`.
/// * `S`: The `LiteralStorage` type.
#[derive(Debug, Clone, Default, PartialEq, Copy, Eq)]
pub struct NoClauseManagement;

impl ClauseManagement for NoClauseManagement {
    /// Creates a new `NoClauseManagement` instance.
    /// The `clauses` argument is ignored.
    fn new<L: Literal, S: LiteralStorage<L>>(_clauses: &[Clause<L, S>]) -> Self {
        Self
    }

    /// This is a no-op for `NoClauseManagement`.
    fn on_conflict<L: Literal, S: LiteralStorage<L>>(&mut self, _cnf: &mut Cnf<L, S>) {}

    /// Always returns `false` as this strategy never cleans the database.
    fn should_clean_db(&self) -> bool {
        false
    }

    /// This is a no-op for `NoClauseManagement`.
    fn clean_clause_db<L: Literal, S: LiteralStorage<L>, P: Propagator<L, S, A>, A: Assignment>(
        &mut self,
        _cnf: &mut Cnf<L, S>,
        _trail: &mut Trail<L, S>,
        _propagator: &mut P,
        _assignment: &mut A,
    ) {
    }

    /// This is a no-op for `NoClauseManagement`.
    fn bump_involved_clause_activities<L: Literal, S: LiteralStorage<L>>(
        &mut self,
        _cnf: &mut Cnf<L, S>,
        _c_ref: usize,
    ) {
    }

    /// Always returns `0` as no clauses are ever removed.
    fn num_removed(&self) -> usize {
        0
    }
}

/// Possible clause management implementations
#[derive(Debug, Clone, PartialEq)]
pub enum ClauseManagementImpls<const N: usize> {
    /// No clause management variant
    NoClauseManagement(NoClauseManagement),
    /// LBD and activity variant
    LbdActivityClauseManagement(LbdClauseManagement<N>),
}

impl<const N: usize> Default for ClauseManagementImpls<N> {
    fn default() -> Self {
        Self::NoClauseManagement(NoClauseManagement)
    }
}

impl<const N: usize> ClauseManagement for ClauseManagementImpls<N> {
    fn new<L: Literal, S: LiteralStorage<L>>(clauses: &[Clause<L, S>]) -> Self {
        LbdActivityClauseManagement(LbdClauseManagement::new(clauses))
    }

    fn on_conflict<L: Literal, S: LiteralStorage<L>>(&mut self, cnf: &mut Cnf<L, S>) {
        match self {
            LbdActivityClauseManagement(m) => m.on_conflict(cnf),
            Self::NoClauseManagement(m) => m.on_conflict(cnf),
        }
    }

    fn should_clean_db(&self) -> bool {
        match self {
            LbdActivityClauseManagement(l) => l.should_clean_db(),
            Self::NoClauseManagement(m) => m.should_clean_db(),
        }
    }

    fn clean_clause_db<L: Literal, S: LiteralStorage<L>, P: Propagator<L, S, A>, A: Assignment>(
        &mut self,
        cnf: &mut Cnf<L, S>,
        trail: &mut Trail<L, S>,
        propagator: &mut P,
        assignment: &mut A,
    ) {
        match self {
            LbdActivityClauseManagement(m) => m.clean_clause_db(cnf, trail, propagator, assignment),
            Self::NoClauseManagement(m) => m.clean_clause_db(cnf, trail, propagator, assignment),
        }
    }

    fn bump_involved_clause_activities<L: Literal, S: LiteralStorage<L>>(
        &mut self,
        cnf: &mut Cnf<L, S>,
        c_ref: usize,
    ) {
        match self {
            LbdActivityClauseManagement(m) => m.bump_involved_clause_activities(cnf, c_ref),
            Self::NoClauseManagement(m) => m.bump_involved_clause_activities(cnf, c_ref),
        }
    }

    fn num_removed(&self) -> usize {
        match self {
            LbdActivityClauseManagement(m) => m.num_removed(),
            Self::NoClauseManagement(m) => m.num_removed(),
        }
    }
}

/// Enum representing the type of clause management strategy to use in a SAT solver.
#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, Default, ValueEnum)]
pub enum ClauseManagementType {
    /// No clause management strategy
    NoClauseManagement,
    /// LBD and activity-based clause management strategy
    #[default]
    LbdActivityClauseManagement,
}

impl Display for ClauseManagementType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoClauseManagement => write!(f, "No Clause Management"),
            Self::LbdActivityClauseManagement => write!(f, "LBD and Activity Clause Management"),
        }
    }
}

impl ClauseManagementType {
    /// Converts the `ClauseManagementType` to a concrete `ClauseManagementImpls`.
    pub fn to_impl<L: Literal, S: LiteralStorage<L>, const N: usize>(
        &self,
        clauses: &[Clause<L, S>],
    ) -> ClauseManagementImpls<N> {
        match self {
            Self::NoClauseManagement => {
                ClauseManagementImpls::NoClauseManagement(NoClauseManagement::new(clauses))
            }
            Self::LbdActivityClauseManagement => {
                LbdActivityClauseManagement(LbdClauseManagement::<N>::new(clauses))
            }
        }
    }
}
