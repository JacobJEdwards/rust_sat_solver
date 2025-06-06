//! Implements the core Conflict-Driven Clause Learning (CDCL) SAT solver.
//!
//! The `Cdcl` struct orchestrates various components like variable selection,
//! propagation, conflict analysis, and clause learning to determine the
//! satisfiability of a given Conjunctive Normal Form (CNF) formula.
//! It follows the typical CDCL algorithm structure, including decision-making,
//! boolean constraint propagation (BCP), conflict analysis, clause learning,
//! non-chronological backtracking, and restarts.

use crate::sat::assignment::Assignment;
use crate::sat::clause::Clause;
use crate::sat::clause_management::ClauseManagement;
use crate::sat::clause_storage::LiteralStorage;
use crate::sat::cnf::Cnf;
use crate::sat::conflict_analysis::{Analyser, Conflict};
use crate::sat::literal::Literal;
use crate::sat::propagation::Propagator;
use crate::sat::restarter::Restarter;
use crate::sat::solver::{DefaultConfig, SolutionStats, Solutions, Solver, SolverConfig};
use crate::sat::trail::Reason;
use crate::sat::trail::Trail;
use crate::sat::variable_selection::VariableSelection;
use crate::sat::{cnf, variable_selection};
use std::fmt::Debug;

/// Represents a CDCL SAT solver instance.
///
/// The solver iteratively makes decisions (assigns a truth value to a variable),
/// propagates their logical consequences, and if a conflict (a clause that becomes
/// false under the current assignment) arises, it analyses the conflict to learn
/// a new clause. This learned clause helps prune the search space and guide the
/// solver towards a solution or a proof of unsatisfiability.
///
/// The solver's behavior can be customised via the `Config` generic parameter,
/// which defines the specific implementations for various components like
/// literal representation, assignment tracking, propagation engine, variable
/// selection heuristic, restart strategies, and clause database management.
#[derive(Debug, Clone)]
pub struct Cdcl<Config: SolverConfig = DefaultConfig> {
    /// Tracks the current assignment of truth values (True, False, Undefined) to variables.
    assignment: Config::Assignment,

    /// Handles unit propagation, which is the process of
    /// deducing further variable assignments implied by the current partial assignment
    /// and unit clauses.
    propagator: Config::Propagator,

    /// The Conjunctive Normal Form (CNF) formula being solved.
    /// This stores both the original clauses provided by the user and clauses
    /// learned by the solver during conflict analysis.
    pub cnf: Cnf<Config::Literal, Config::LiteralStorage>,

    /// Implements the variable selection heuristic (e.g. VSIDS) responsible for
    /// choosing the next unassigned variable to make a decision on.
    selector: Config::VariableSelector,

    /// The current decision level in the search tree.
    /// Level 0 is for initial propagations from unit clauses in the input.
    /// Each new decision increments this level.
    decision_level: cnf::DecisionLevel,

    /// The trail records the sequence of assigned literals, their decision levels,
    /// and the reasons for their assignment (either a decision or an implication
    /// from a clause). It is crucial for backtracking and conflict analysis.
    trail: Trail<Config::Literal, Config::LiteralStorage>,

    /// Manages the restart strategy. Restarts involve clearing the current
    /// assignment (except for level 0 assignments) and restarting the search,
    /// potentially using different heuristics or learned information.
    restarter: Config::Restarter,

    /// Analyses conflicts encountered during propagation to produce learned clauses
    /// (lemmas) and determine the appropriate decision level to backtrack to.
    conflict_analysis: Analyser<Config::Literal, Config::LiteralStorage>,

    /// Manages the database of learned clauses, including strategies for periodically
    /// removing less useful learned clauses to save memory and keep propagation efficient.
    manager: Config::ClauseManager,
}

impl<Config: SolverConfig> Cdcl<Config> {
    /// Checks if all variables in the CNF have been assigned a truth value.
    ///
    /// The number of variables is determined by `self.cnf.num_vars`, which typically
    /// corresponds to the highest variable index used in the problem + 1.
    /// The trail length (`self.trail.len()`) reflects the number of currently
    /// assigned literals.
    ///
    /// # Returns
    ///
    /// `true` if the number of assigned literals in the trail equals the total
    /// number of variables considered by the solver, `false` otherwise.
    pub const fn all_assigned(&self) -> bool {
        self.trail.len() == self.cnf.num_vars
    }

    /// Determines if the solver should perform a restart.
    ///
    /// A restart is advised under two conditions:
    /// 1. The `Restarter` component itself signals that a restart is due (e.g. based on a Luby sequence or fixed conflict count).
    /// 2. The "conflict rate" (number of restarts divided by trail length) exceeds a threshold (0.1).
    ///    The trail length serves as a rough proxy for the amount of search effort. A high rate
    ///    might indicate thrashing or a poor search path.
    ///
    /// Division by zero (if trail length is 0) results in `f64::INFINITY` for the rate if
    /// `num_restarts > 0`, correctly triggering a restart. If `num_restarts` is also 0,
    /// the rate is `f64::NAN`, which does not trigger the rate-based restart.
    ///
    /// # Returns
    ///
    /// `true` if a restart is advised, `false` otherwise.
    fn should_restart(&mut self) -> bool {
        #[allow(clippy::cast_precision_loss)]
        let conflict_rate = if !self.trail.is_empty() {
            self.restarter.num_restarts() as f64 / self.trail.len() as f64
        } else if self.restarter.num_restarts() > 0 {
            f64::INFINITY
        } else {
            0.0
        };
        self.restarter.should_restart() || conflict_rate > 0.1
    }

    /// Adds a propagated literal to the trail along with its reason and decision level.
    ///
    /// This method is called when a literal is implied by a clause (unit propagation).
    /// The literal, current decision level, and the index of the implying clause (reason)
    /// are recorded on the trail. This information is vital for conflict analysis and backtracking.
    ///
    /// # Arguments
    ///
    /// * `lit`: The literal that was propagated (e.g. variable `x` is True).
    /// * `c_ref`: The index (reference) of the clause that became unit and caused this propagation.
    fn add_propagation(&mut self, lit: Config::Literal, c_ref: usize) {
        self.trail
            .push(lit, self.decision_level, Reason::Clause(c_ref));
    }

    /// Adds a new clause to the solver's CNF database.
    ///
    /// Clauses that are empty (and thus trivially unsatisfiable if encountered this way)
    /// or tautological (e.g. `(x OR -x OR y)`) are typically ignored as they provide
    /// no useful constraints or can be simplified.
    /// The new clause is added to the `Cnf` store and then registered with the `Propagator`
    /// (e.g. for setting up watched literals).
    ///
    /// # Arguments
    ///
    /// * `clause`: The clause to add.
    pub fn add_clause(&mut self, clause: Clause<Config::Literal, Config::LiteralStorage>) {
        if clause.is_empty() || clause.is_tautology() {
            return;
        }

        let c_ref = self.cnf.len();

        self.cnf.add_clause(clause);
        self.propagator.add_clause(&self.cnf[c_ref], c_ref);
    }
}

impl<Config: SolverConfig> Solver<Config> for Cdcl<Config> {
    /// Creates a new `Cdcl` solver instance for the given CNF formula.
    ///
    /// Initialises all internal components of the solver:
    /// - `Assignment`: To store variable assignments (initialised to Undefined).
    /// - `Trail`: To track decisions and propagations.
    /// - `Propagator`: Set up with the initial clauses for watched literal schemes.
    /// - `Cnf`: Stores the clauses of the problem.
    /// - `VariableSelector`: Initialised with variable information (e.g. for VSIDS).
    /// - `Restarter`: Initialised with default restart strategy parameters.
    /// - `Analyser`: For conflict analysis.
    /// - `ClauseManager`: For managing learned clauses.
    ///   The decision level is initialised to 0.
    ///
    /// # Arguments
    ///
    /// * `cnf`: The Conjunctive Normal Form (CNF) formula to be solved.
    fn new<L: Literal, S: LiteralStorage<L>>(cnf: Cnf<L, S>) -> Self {
        let cnf = cnf.convert();

        let propagator = Propagator::new(&cnf);
        let vars = &cnf.lits;
        let selector = Config::VariableSelector::new(cnf.num_vars, vars, &cnf.clauses);
        let restarter = Restarter::new();
        let conflict_analysis = Analyser::new(cnf.num_vars);
        let manager = Config::ClauseManager::new(&cnf.clauses);

        Self {
            assignment: Assignment::new(cnf.num_vars),
            trail: Trail::new(&cnf.clauses, cnf.num_vars),
            propagator,
            cnf,
            selector,
            restarter,
            decision_level: 0,
            conflict_analysis,
            manager,
        }
    }

    fn from_parts<L: Literal, S: LiteralStorage<L>>(
        cnf: Cnf<L, S>,
        assignment: Config::Assignment,
        manager: Config::ClauseManager,
        propagator: Config::Propagator,
        restarter: Config::Restarter,
        selector: Config::VariableSelector,
    ) -> Self {
        let cnf = cnf.convert();
        let conflict_analysis = Analyser::new(cnf.num_vars);

        Self {
            trail: Trail::new(&cnf.clauses, cnf.num_vars),
            assignment,
            propagator,
            cnf,
            selector,
            conflict_analysis,
            restarter,
            manager,
            decision_level: 0,
        }
    }

    /// Attempts to solve the SAT problem for the loaded CNF formula using the CDCL algorithm.
    ///
    /// The main loop proceeds as follows:
    /// 1. **Initial Check & Propagation**:
    ///    - If the CNF is empty, it's trivially SAT.
    ///    - Perform initial unit propagation (BCP) at decision level 0. If a conflict occurs, the formula is UNSAT.
    ///    - If any clause becomes empty (after initial setup or propagation), formula is UNSAT.
    /// 2. **Main Loop**:
    ///    a. **Propagation**: Propagate assignments based on the current partial assignment.
    ///       - If propagation leads to a conflict (a clause becomes falsified):
    ///         i.   Notify `ClauseManager` about the conflict (e.g. to adjust clause activities).
    ///         ii.  Perform `ConflictAnalysis`:
    ///         - Generate a learned clause (lemma).
    ///              - Determine variables involved for activity bumping (e.g. VSIDS).
    ///
    ///         iii. Handle the conflict result:
    ///         - `Conflict::Ground`: Conflict at level 0 implies the formula is UNSAT.
    ///              - `Conflict::Restart` or `Conflict::Unit`: These might also indicate UNSAT or special handling.
    ///              - `Conflict::Learned(assert_idx, learned_clause)`:
    ///                  - The learned clause is processed (e.g. LBD calculation, activity bump).
    ///                  - Determine backtrack level (`bt_level`) from the learned clause.
    ///                  - Bump activities of clauses involved in the conflict.
    ///                  - Backtrack: Undo assignments on the trail up to `bt_level`. Update `decision_level`.
    ///                  - Add the learned clause to the database.
    ///                  - Enqueue the asserting literal from the learned clause for propagation.
    ///                  - Optionally, clean the clause database (`manager.clean_clause_db`).
    ///
    ///         iv.  Update variable selection heuristics (`selector.bumps`, `selector.decay`).
    ///         v.   Check for restart (`should_restart`). If so, reset trail, assignments, and decision level.
    ///
    ///    b. **Decision (No Conflict)**:
    ///    i.   Increment `decision_level`.
    ///    ii.  Check if all variables are assigned (`all_assigned`). If yes, a model is found; return SAT.
    ///    iii. Select an unassigned variable using `selector.pick()`.
    ///    - If a literal is picked, push it onto the trail as a decision.
    ///      - If no literal can be picked (e.g. all assigned but `all_assigned` was false, or selector gives up),
    ///        it might imply a solution is found (though `all_assigned` should be the primary check).
    ///        Return current solutions.
    ///
    /// The loop continues until a satisfying assignment is found (returns `Some(Solutions)`)
    /// or the formula is proven unsatisfiable (returns `None`).
    ///
    /// # Returns
    ///
    /// * `Some(Solutions)`: If a satisfying assignment is found. Contains the model.
    /// * `None`: If the formula is unsatisfiable.
    fn solve(&mut self) -> Option<Solutions> {
        if self.cnf.is_empty() {
            return Some(Solutions::default());
        }

        if self
            .propagator
            .propagate(&mut self.trail, &mut self.assignment, &mut self.cnf)
            .is_some()
        {
            return None;
        }

        if self.cnf.iter().any(Clause::is_empty) {
            return None;
        }

        loop {
            if let Some(c_ref) = // c_ref is the index of the conflict clause
                self.propagator.propagate(
                    &mut self.trail,
                    &mut self.assignment,
                    &mut self.cnf,
                )
            {
                self.manager.on_conflict(&mut self.cnf);

                let (conflict, to_bump) = self.conflict_analysis.analyse_conflict(
                    &self.cnf,
                    &self.trail,
                    &self.assignment,
                    c_ref,
                );

                match conflict {
                    Conflict::Unit(_) | Conflict::Restart(_) | Conflict::Ground => {
                        return None;
                    }
                    Conflict::Learned(assert_idx, mut clause) => {
                        clause.swap(0, assert_idx);

                        let asserting_lit = clause[0];

                        let bt_level = clause
                            .iter()
                            .skip(1)
                            .map(|lit| self.trail.level(lit.variable()))
                            .max()
                            .unwrap_or(0);

                        clause.calculate_lbd(&self.trail);
                        clause.is_learnt = true;

                        clause.bump_activity(1.0);

                        self.manager
                            .bump_involved_clause_activities(&mut self.cnf, c_ref);

                        self.trail.backstep_to(&mut self.assignment, bt_level);
                        self.decision_level = bt_level;

                        let new_clause_idx = self.cnf.len();
                        self.add_clause(clause);

                        self.add_propagation(asserting_lit, new_clause_idx);

                        if self.manager.should_clean_db() {
                            self.manager.clean_clause_db(
                                &mut self.cnf,
                                &mut self.trail,
                                &mut self.propagator,
                                &mut self.assignment,
                            );
                        }
                    }
                }

                self.selector.bumps(to_bump);
                self.selector.decay(variable_selection::VSIDS_DECAY_FACTOR);

                if self.should_restart() {
                    // would be better to not reset the initial unit clauses, but no way round now
                    self.trail.reset();
                    self.assignment.reset();
                    self.decision_level = 0;
                }
            } else {
                self.decision_level = self.decision_level.wrapping_add(1);

                if self.all_assigned() {
                    return Some(self.solutions());
                }

                let lit_option = self.selector.pick(&self.assignment);

                if let Some(lit) = lit_option {
                    self.trail.push(lit, self.decision_level, Reason::Decision);
                } else {
                    return Some(self.solutions());
                }
            }
        }
    }

    /// Retrieves the current satisfying assignment if one has been found.
    ///
    /// This method should typically be called after `solve()` returns `Some(_)`.
    /// If called before solving, or if the formula is unsatisfiable, the returned
    /// assignment might be incomplete, empty, or reflect some intermediate state.
    /// The `Solutions` object usually maps variable indices to their truth values.
    ///
    /// # Returns
    ///
    /// A `Solutions` object representing the variable assignments in a model.
    fn solutions(&self) -> Solutions {
        self.assignment.get_solutions()
    }

    /// Gathers statistics about the solving process.
    ///
    /// These statistics can be useful for analysing solver performance and heuristics.
    ///
    /// # Returns
    ///
    /// A `SolutionStats` struct containing:
    /// - `conflicts`: Total number of conflicts encountered.
    /// - `decisions`: Total number of decisions made.
    /// - `propagations`: Total number of propagations performed.
    /// - `restarts`: Total number of restarts performed.
    /// - `learnt_clauses`: Number of clauses currently in the learnt clause database.
    /// - `removed_clauses`: Number of learnt clauses removed during database cleaning.
    fn stats(&self) -> SolutionStats {
        SolutionStats {
            conflicts: self.conflict_analysis.count,
            decisions: self.selector.decisions(),
            propagations: self.propagator.num_propagations(),
            restarts: self.restarter.num_restarts(),
            learnt_clauses: self.cnf.len() - self.cnf.non_learnt_idx,
            removed_clauses: self.manager.num_removed(),
        }
    }

    /// Placeholder for a debugging function.
    ///
    /// This function is intended for future use, possibly to print internal solver state
    /// or enable more verbose logging for debugging purposes. Currently, it is unimplemented.
    fn debug(&mut self) {
        todo!()
    }
}
