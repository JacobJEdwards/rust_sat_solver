//! Defines the main DPLL (Davis-Putnam-Logemann-Loveland) SAT solver.
//!
//! This module provides the `Dpll` struct, which implements a classical DPLL
//! algorithm for solving Boolean Satisfiability (SAT) problems. The solver
//! takes a Conjunctive Normal Form (CNF) formula as input and determines
//! whether it's satisfiable. If satisfiable, it can also provide a model
//! (an assignment of truth values to variables that satisfies the formula).
//!
//! The `Dpll` solver is generic over a `SolverConfig` trait, allowing
//! different underlying data structures and strategies (e.g., for variable
//! selection, literal representation) to be plugged in. A `DefaultConfig`
//! is provided for common use cases.
//!
//! The core logic involves:
//! 1.  **Unit Propagation:** If a clause is a unit clause (contains only one
//!     unassigned literal), that literal must be assigned a value to make the
//!     clause true. This assignment may, in turn, create new unit clauses.
//! 2.  **Decision:** If no more unit propagations can be made and the formula is
//!     neither clearly satisfied nor falsified, an unassigned variable is chosen,
//!     and the algorithm recursively tries assigning it true and then false.
//! 3.  **Backtracking:** Implicitly handled by the recursive calls and cloning. If a branch
//!     leads to a conflict (a clause becomes unsatisfiable), that branch is abandoned.

use crate::sat::assignment::Assignment;
use crate::sat::cnf;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use crate::sat::propagation::Propagator;
use crate::sat::solver::{DefaultConfig, SolutionStats, Solutions, Solver, SolverConfig};
use crate::sat::trail::Trail;
use crate::sat::variable_selection::VariableSelection;

/// Represents a DPLL SAT solver.
///
/// This struct encapsulates the state of the solver, including the CNF formula,
/// current assignment, decision level, and components for propagation and
/// variable selection. It is generic over `Config`, which defines the specific
/// types and strategies used by the solver.
#[derive(Debug, Clone)]
pub struct Dpll<Config: SolverConfig + Clone = DefaultConfig> {
    /// The trail of assignments and decisions made by the solver.
    /// It's used by the propagator to manage assignments and detect conflicts.
    pub trail: Trail<Config::Literal, Config::LiteralStorage>,
    /// The current assignment of truth values to variables.
    pub assignment: Config::Assignment,
    /// The current decision level in the DPLL search tree.
    /// Incremented each time a new variable is chosen for branching.
    pub decision_level: cnf::DecisionLevel,
    /// The Conjunctive Normal Form (CNF) formula being solved.
    pub cnf: Cnf<Config::Literal, Config::LiteralStorage>,
    /// The variable selection heuristic.
    /// Used to pick the next unassigned variable for a decision.
    pub selector: Config::VariableSelector,
    /// The unit propagator.
    /// Responsible for performing unit propagation based on the current assignment.
    pub propagator: Config::Propagator,
}

impl<Config: SolverConfig + Clone> Solver<Config> for Dpll<Config> {
    /// Creates a new DPLL solver instance for the given CNF formula.
    ///
    /// # Arguments
    ///
    /// * `cnf`: The CNF formula to be solved.
    ///
    /// # Returns
    ///
    /// A new `Dpll` instance initialized with the provided formula and
    /// default components (propagator, assignment tracker, trail, variable selector)
    /// based on the `Config`.
    fn new(cnf: Cnf<Config::Literal, Config::LiteralStorage>) -> Self {
        let lits = &cnf.lits;
        let propagator = Propagator::new(&cnf);
        let assignment = Assignment::new(cnf.num_vars);
        let trail = Trail::new(&cnf.clauses, cnf.num_vars);
        let selector = Config::VariableSelector::new(cnf.num_vars, lits, &cnf.clauses);

        Self {
            trail,
            assignment,
            decision_level: 0,
            cnf,
            selector,
            propagator,
        }
    }

    /// Attempts to solve the SAT formula.
    ///
    /// This method implements the core DPLL algorithm:
    /// 1.  It first performs unit propagation (`self.propagate()`).
    /// 2.  Then, it checks if the formula is already satisfied (`self.is_sat()`). If so,
    ///     it returns the current assignment.
    /// 3.  It checks if the formula is unsatisfiable (`self.is_unsat()`) due to a conflict.
    ///     If so, it returns `None`.
    /// 4.  If the formula is neither satisfied nor unsatisfiable, it selects an unassigned
    ///     variable using `self.selector.pick()`.
    /// 5.  It increments the decision level.
    /// 6.  It creates two branches: one where the chosen variable is assigned `true`,
    ///     and one where it's assigned `false`. These branches are explored recursively
    ///     by calling `solve()` on cloned solver states.
    /// 7.  If the 'true' branch finds a solution, it's returned.
    /// 8.  Otherwise, if the 'false' branch finds a solution, it's returned.
    /// 9.  If neither branch finds a solution, the formula is unsatisfiable from the
    ///     current state, and `None` is returned.
    ///
    /// # Returns
    ///
    /// * `Some(Solutions)`: If the formula is satisfiable, containing the satisfying assignment.
    /// * `None`: If the formula is unsatisfiable.
    fn solve(&mut self) -> Option<Solutions> {
        self.propagate();

        if self.is_sat() {
            return Some(self.solutions());
        }

        if self.is_unsat() {
            return None;
        }

        let var = self.selector.pick(&self.assignment)?;

        self.decision_level = self.decision_level.wrapping_add(1);

        let mut true_branch = self.clone();
        let mut false_branch = self.clone();

        true_branch
            .assignment
            .assign(Config::Literal::new(var.variable(), true));
        false_branch
            .assignment
            .assign(Config::Literal::new(var.variable(), false));

        if let Some(solutions) = true_branch.solve() {
            return Some(solutions);
        }

        false_branch.solve()
    }

    /// Returns the current satisfying assignment if the formula is SAT.
    ///
    /// This method should typically be called after `solve()` returns `Some(...)`.
    /// It retrieves the model (variable assignments) from the `assignment` component.
    /// Variables not assigned a value in the model might be "don't care" variables.
    fn solutions(&self) -> Solutions {
        self.assignment.get_solutions()
    }

    /// Returns statistics about the solving process.
    ///
    /// Note: Some statistics, like `propagations`, might be estimations or
    /// specific to this simple DPLL implementation rather than a general count
    /// of propagation steps.
    /// `conflicts`, `restarts`, `learnt_clauses`, `removed_clauses` are currently placeholders.
    fn stats(&self) -> SolutionStats {
        SolutionStats {
            conflicts: 0, // Placeholder, not actively counted in this basic DPLL
            decisions: self.decision_level,
            // This is a rough heuristic: total variables minus decisions made.
            // It doesn't count individual propagation steps accurately.
            propagations: self
                .cnf
                .num_vars
                .saturating_sub(self.decision_level as usize),
            restarts: 0,        // Placeholder
            learnt_clauses: 0,  // Placeholder
            removed_clauses: 0, // Placeholder
        }
    }

    /// Placeholder for a debugging function.
    ///
    /// Currently, this function is not implemented and will panic if called.
    fn debug(&mut self) {
        todo!()
    }
}

impl<Config: SolverConfig + Clone> Dpll<Config> {
    /// Performs unit propagation.
    ///
    /// This method delegates to the configured `propagator` to find and
    /// apply unit clauses, updating the `trail` and `assignment` accordingly.
    /// If propagation leads to a conflict, the `trail` will be marked,
    /// and subsequent `is_unsat()` calls should detect this.
    fn propagate(&mut self) {
        self.propagator
            .propagate(&mut self.trail, &mut self.assignment, &mut self.cnf);
    }

    /// Checks if the CNF formula is satisfied under the current assignment.
    ///
    /// A formula is satisfied if all its clauses are satisfied. A clause is
    /// satisfied if at least one of its literals is true under the current
    /// assignment.
    ///
    /// # Returns
    ///
    /// `true` if all clauses are satisfied, `false` otherwise.
    /// Returns `true` for an empty CNF (a CNF with no clauses).
    fn is_sat(&self) -> bool {
        self.cnf.iter().all(|clause| {
            clause
                .iter()
                .any(|lit| self.assignment.literal_value(*lit) == Some(true))
        })
    }

    /// Checks if the CNF formula is unsatisfiable under the current assignment.
    ///
    /// A formula is unsatisfiable if at least one of its clauses is falsified.
    /// A clause is falsified if all of its literals are false under the current
    /// assignment. This state indicates a conflict.
    ///
    /// # Returns
    ///
    /// `true` if any clause is falsified, `false` otherwise.
    /// Returns `true` if the CNF contains an empty clause.
    fn is_unsat(&self) -> bool {
        self.cnf.iter().any(|clause| {
            clause
                .iter()
                .all(|lit| self.assignment.literal_value(*lit) == Some(false))
        })
    }
}
