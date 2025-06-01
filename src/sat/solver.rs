#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
//! Defines common types and traits for SAT solvers, including solver configurations,
//! solution representation, and statistics.
//!
//! This module provides:
//! - `SolutionStats`: A struct to hold statistics about a solver's run (conflicts, decisions, etc.).
//! - `Solutions`: A struct to represent a satisfying assignment (a model) for a formula.
//! - `SolverConfig`: A trait to define a configuration for a SAT solver, specifying the
//!   types for various components like literals, assignment management, variable selection,
//!   propagation, restart strategy, and clause management.
//! - `solver_config!`: A macro to easily create concrete implementations of `SolverConfig`.
//! - `DefaultConfig`: A pre-defined default solver configuration using common component choices.
//! - `Solver`: A trait defining the general interface for a SAT solver.

use crate::sat::assignment::{AssignmentImpls, VecAssignment};
use crate::sat::clause_management::{ClauseManagementImpls, LbdClauseManagement};
use crate::sat::cnf::Cnf;
use crate::sat::literal::{Literal, LiteralImpls, PackedLiteral};
use crate::sat::propagation::{PropagatorImpls, WatchedLiterals};
use crate::sat::restarter::{Luby, RestarterImpls};
use crate::sat::variable_selection::{VariableSelectionImpls, Vsids};
use clap::ValueEnum;
use itertools::Itertools;
use rustc_hash::FxHashSet;
use smallvec::SmallVec;
use std::fmt::{Debug, Display, Formatter};
use std::num::NonZeroI32;

/// Contains statistics about a SAT solver's execution.
///
/// These statistics provide insights into the solver's performance and behavior
/// during the search for a solution.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SolutionStats {
    /// The total number of conflicts encountered during the search.
    pub conflicts: usize,
    /// The total number of decisions made (variables chosen and assigned a value heuristically).
    pub decisions: usize,
    /// The total number of propagations (literals assigned due to unit propagation).
    pub propagations: usize,
    /// The total number of times the solver restarted its search.
    pub restarts: usize,
    /// The total number of clauses learnt during conflict analysis.
    pub learnt_clauses: usize,
    /// The total number of learnt clauses removed by clause database cleaning.
    pub removed_clauses: usize,
}

/// Represents a satisfying assignment (a model) for a CNF formula.
///
/// The assignments are stored as a set of `NonZeroI32`, where:
/// - A positive integer `v` means variable `v` is assigned true.
/// - A negative integer `-v` means variable `v` is assigned false.
///   This aligns with the DIMACS convention for representing literals.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Solutions {
    /// A set of non-zero integers representing the truth assignments of variables.
    /// Positive `v` means variable `v` is true; negative `-v` means variable `v` is false.
    pub assignments: FxHashSet<NonZeroI32>,
}

impl Display for Solutions {
    /// Formats the solution as a space-separated string of assigned literals.
    /// For example: "1 -2 3" means x1=true, x2=false, x3=true.
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let assignments_str: Vec<String> = self
            .assignments
            .iter()
            .sorted_by(|left, right| Ord::cmp(&left.abs(), &right.abs()))
            .map(|&val| val.get().to_string())
            .collect();

        write!(f, "{}", assignments_str.join(" "))
    }
}

impl Solutions {
    /// Creates a new `Solutions` instance from a slice of `i32` (DIMACS literals).
    /// Zero values in the input slice are ignored, as `NonZeroI32` cannot be zero.
    #[must_use]
    pub fn new(s: &[i32]) -> Self {
        Self {
            assignments: s.iter().copied().filter_map(NonZeroI32::new).collect(),
        }
    }

    /// Returns an iterator over the assigned literals (`&NonZeroI32`).
    pub fn iter(&self) -> impl Iterator<Item = &NonZeroI32> {
        self.assignments.iter()
    }

    /// Checks if a given literal (represented by `NonZeroI32`) is part of the solution.
    /// For example, `check(NonZeroI32::new(1).unwrap())` checks if variable 1 is true.
    /// `check(NonZeroI32::new(-2).unwrap())` checks if variable 2 is false.
    #[must_use]
    pub fn check(&self, i: NonZeroI32) -> bool {
        self.assignments.contains(&i)
    }

    /// Returns the number of variables assigned in this solution.
    #[must_use]
    pub fn len(&self) -> usize {
        self.assignments.len()
    }

    /// Returns `true` if this solution assigns no variables.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.assignments.is_empty()
    }

    /// Adds a literal assignment to the solution set.
    pub fn add(&mut self, i: NonZeroI32) {
        self.assignments.insert(i);
    }
}

/// A trait that defines the configuration for a SAT solver.
///
/// This trait uses associated types to specify the concrete types for various
/// components of a SAT solver. This allows for a highly generic `Solver` trait
/// that can be instantiated with different underlying implementations for its parts.
pub trait SolverConfig: Debug + Clone {
    /// The type used for managing variable assignments (e.g. `VecAssignment`).
    /// Must implement `crate::sat::assignment::Assignment`.
    type Assignment: crate::sat::assignment::Assignment;
    /// The type used for the variable selection heuristic (e.g. `Vsids`, `Random`).
    /// Must implement `crate::sat::variable_selection::VariableSelection`.
    type VariableSelector: crate::sat::variable_selection::VariableSelection<Self::Literal>;
    /// The type used to represent literals (e.g. `PackedLiteral`, `StructLiteral`).
    /// Must implement `crate::sat::literal::Literal`.
    type Literal: Literal;
    /// The type used for storing literals within a clause (e.g. `Vec<L>`, `SmallVec<[L; N]>`).
    /// Must implement `crate::sat::clause_storage::LiteralStorage`.
    type LiteralStorage: LiteralStorage<Self::Literal>;
    /// The type used for the restart strategy (e.g. `Luby`, `Geometric`).
    /// Must implement `crate::sat::restarter::Restarter`.
    type Restarter: crate::sat::restarter::Restarter;
    /// The type used for the unit propagation mechanism (e.g. `WatchedLiterals`, `UnitSearch`).
    /// Must implement `crate::sat::propagation::Propagator`.
    type Propagator: crate::sat::propagation::Propagator<Self::Literal, Self::LiteralStorage, Self::Assignment>;
    /// The type used for managing the clause database (e.g. `LbdClauseManagement`).
    /// Must implement `crate::sat::clause_management::ClauseManagement`.
    type ClauseManager: crate::sat::clause_management::ClauseManagement;
}

/// A macro to conveniently define a struct that implements `SolverConfig`.
///
/// This reduces boilerplate when creating new solver configurations.
///
/// # Usage
///
/// ## Without generic parameters:
/// ```rust
/// # use crate::sat::solver_types::{solver_config, SolverConfig};
/// # use crate::sat::literal::PackedLiteral;
/// # use smallvec::SmallVec;
/// # use crate::sat::assignment::VecAssignment;
/// # use crate::sat::variable_selection::Vsids;
/// # use crate::sat::propagation::WatchedLiterals;
/// # use crate::sat::restarter::Fixed;
/// # use crate::sat::clause_management::NoClauseManagement;
/// # #[derive(Debug, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)] pub struct MyLitStore;
/// # impl crate::sat::clause_storage::LiteralStorage<PackedLiteral> for MyLitStore {
/// #   fn push(&mut self, l: PackedLiteral) {} fn len(&self) -> usize {0} fn is_empty(&self) -> bool {true}
/// #   fn iter(&self) -> std::slice::Iter<PackedLiteral> { [].iter() }
/// #   fn iter_mut(&mut self) -> std::slice::IterMut<PackedLiteral> { [].iter_mut() }
/// #   fn remove(&mut self, i: usize) -> PackedLiteral { PackedLiteral::default() } fn clear(&mut self) {}
/// #   fn swap(&mut self, a: usize, b: usize) {}
/// #   unsafe fn get_unchecked(&self, i: usize) -> &PackedLiteral { &PackedLiteral::default() }
/// #   unsafe fn get_unchecked_mut(&mut self, i: usize) -> &mut PackedLiteral { panic!() }
/// # }
/// # impl FromIterator<PackedLiteral> for MyLitStore { fn from_iter<T: IntoIterator<Item=PackedLiteral>>(iter: T) -> Self { MyLitStore } }
/// # impl From<Vec<PackedLiteral>> for MyLitStore { fn from(v: Vec<PackedLiteral>) -> Self { MyLitStore } }
/// # impl std::ops::Index<usize> for MyLitStore { type Output = PackedLiteral; fn index(&self, i: usize) -> &Self::Output { &PackedLiteral::default() }}
/// # impl std::ops::IndexMut<usize> for MyLitStore { fn index_mut(&mut self, i: usize) -> &mut Self::Output { panic!() }}
/// # impl Extend<PackedLiteral> for MyLitStore { fn extend<T: IntoIterator<Item=PackedLiteral>>(&mut self, iter: T) {} }
/// # impl AsRef<[PackedLiteral]> for MyLitStore { fn as_ref(&self) -> &[PackedLiteral] { &[] } }
///
/// solver_config!(MyCoolConfig {
///     Literal = PackedLiteral,
///     LiteralStorage = MyLitStore, // Using a placeholder for brevity
///     Assignment = VecAssignment,
///     VariableSelector = Vsids,
///     Propagator = WatchedLiterals<PackedLiteral, MyLitStore, VecAssignment>,
///     Restarter = Fixed<100>,
///     ClauseManager = NoClauseManagement<PackedLiteral, MyLitStore>,
/// });
/// ```
///
/// ## With generic parameters:
/// ```rust
/// # use crate::sat::solver_types::{solver_config, SolverConfig};
/// # use crate::sat::literal::{Literal, PackedLiteral};
/// # use crate::sat::clause_storage::LiteralStorage;
/// # use smallvec::SmallVec;
/// # use crate::sat::assignment::{Assignment, VecAssignment};
/// # use crate::sat::variable_selection::{VariableSelection, Vsids};
/// # use crate::sat::propagation::{Propagator, WatchedLiterals};
/// # use crate::sat::restarter::{Restarter, Fixed};
/// # use crate::sat::clause_management::{ClauseManagement, NoClauseManagement};
/// # use std::fmt::Debug;
/// # use std::hash::Hash;
///
/// solver_config!(
///     <L: Literal, S: LiteralStorage<L>, A: Assignment>
///     GenericTestConfig {
///         Literal = L,
///         LiteralStorage = S,
///         Assignment = A,
///         VariableSelector = Vsids<L>,
///         Propagator = WatchedLiterals<L, S, A>,
///         Restarter = Fixed<100>,
///         ClauseManager = NoClauseManagement<L, S>,
///     }
/// );
/// ```
#[macro_export]
macro_rules! solver_config {
    ($name:ident {
        Literal = $literal:ty,
        LiteralStorage = $storage:ty,
        Assignment = $assignment:ty,
        VariableSelector = $selector:ty,
        Propagator = $propagator:ty,
        Restarter = $restarter:ty,
        ClauseManager = $manager:ty $(,)?
    }) => {
        /// Generated solver configuration.
        #[derive(Debug, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name;

        impl SolverConfig for $name {
            type Literal = $literal;
            type LiteralStorage = $storage;
            type Assignment = $assignment;
            type VariableSelector = $selector;
            type Propagator = $propagator;
            type Restarter = $restarter;
            type ClauseManager = $manager;
        }
    };

    (
        <$($param:ident $(: $bound:path)?),* $(,)?>
        $name:ident {
            Literal = $literal:ty,
            LiteralStorage = $storage:ty,
            Assignment = $assignment:ty,
            VariableSelector = $selector:ty,
            Propagator = $propagator:ty,
            Restarter = $restarter:ty,
            ClauseManager = $manager:ty $(,)?
        }
    ) => {
        /// Generated solver configuration with generic parameters.
        #[derive(Debug, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name<$($param $(: $bound)?),*> {
            _marker: std::marker::PhantomData<($($param,)*)>,
        }

        impl<$($param $(: $bound)?),*> SolverConfig for $name<$($param),*> {
            type Literal = $literal;
            type LiteralStorage = $storage;
            type Assignment = $assignment;
            type VariableSelector = $selector;
            type Propagator = $propagator;
            type Restarter = $restarter;
            type ClauseManager = $manager;
        }
    };
}

use crate::sat::cdcl::Cdcl;
use crate::sat::clause_storage::{LiteralStorage, LiteralStorageImpls};
use crate::sat::dpll::Dpll;
pub use solver_config;

solver_config!(
    DefaultConfig {
        Literal = PackedLiteral,
        LiteralStorage = SmallVec<[PackedLiteral; 8]>,
        Assignment = VecAssignment,
        VariableSelector = Vsids,
        Propagator = WatchedLiterals<PackedLiteral, SmallVec<[PackedLiteral; 8]>, VecAssignment>,
        Restarter = Luby<2>,
        ClauseManager = LbdClauseManagement<10>,
    }
);

solver_config!(
    DynamicConfig {
        Literal = LiteralImpls,
        LiteralStorage = LiteralStorageImpls<LiteralImpls, 12>,
        Assignment = AssignmentImpls,
        VariableSelector = VariableSelectionImpls,
        Propagator = PropagatorImpls<LiteralImpls, LiteralStorageImpls<LiteralImpls, 12>, AssignmentImpls>,
        Restarter = RestarterImpls<3>,
        ClauseManager = ClauseManagementImpls<10>,
    }
);

/// A trait that defines the general interface for a SAT solver.
///
/// This trait is generic over a configuration `C` which must implement `SolverConfig`.
/// This allows different solver implementations to adhere to a common API while being
/// configurable with various underlying strategies and data structures.
pub trait Solver<C: SolverConfig = DefaultConfig> {
    /// Creates a new instance of the solver, initialised with the given CNF formula.
    ///
    /// # Arguments
    ///
    /// * `cnf`: The `Cnf` formula to be solved.
    fn new<L: Literal, S: LiteralStorage<L>>(cnf: Cnf<L, S>) -> Self;

    /// Creates a solver instance from its components.
    ///
    /// # Arguments
    ///
    /// * `cnf`: The `Cnf` formula to be solved.
    /// * `assignment`: The assignment data structure.
    /// * `manager`: The clause management scheme.
    /// * `propagator`: The unit propagation scheme.
    /// * `restarter`: The restart strategy.
    /// * `selector`: The variable selection strategy.
    fn from_parts<L: Literal, S: LiteralStorage<L>>(
        cnf: Cnf<L, S>,
        assignment: C::Assignment,
        manager: C::ClauseManager,
        propagator: C::Propagator,
        restarter: C::Restarter,
        selector: C::VariableSelector,
    ) -> Self;

    /// Attempts to solve the CNF formula provided at construction.
    ///
    /// # Returns
    ///
    /// - `Some(Solutions)` if a satisfying assignment (model) is found.
    /// - `None` if the formula is determined to be unsatisfiable.
    fn solve(&mut self) -> Option<Solutions>;

    /// Returns the current satisfying assignment if one has been found.
    ///
    /// If `solve()` has not been called, or if it returned `None` (unsatisfiable),
    /// the returned `Solutions` object might be empty or reflect some solver-internal state.
    /// It's typically called after `solve()` returns `Some`.
    fn solutions(&self) -> Solutions;

    /// Returns statistics about the solver's last execution of `solve()`.
    fn stats(&self) -> SolutionStats;

    /// Provides a way to debug the solver's internal state.
    /// The exact output or behavior is implementation-defined.
    #[allow(dead_code)]
    fn debug(&mut self);
}

/// An enum representing different implementations of SAT solvers.
#[derive(Debug, Clone)]
pub enum SolverImpls<C: SolverConfig = DynamicConfig> {
    /// A DPLL-based SAT solver.
    Dpll(Box<Dpll<C>>),
    /// A CDCL-based SAT solver.
    Cdcl(Box<Cdcl<C>>),
}

impl<C: SolverConfig> Solver<C> for SolverImpls<C> {
    fn new<L: Literal, S: LiteralStorage<L>>(cnf: Cnf<L, S>) -> Self {
        let cnf: Cnf<C::Literal, C::LiteralStorage> = cnf.convert();
        let cdcl = Cdcl::new(cnf);
        Self::Cdcl(Box::new(cdcl))
    }

    fn from_parts<L: Literal, S: LiteralStorage<L>>(
        cnf: Cnf<L, S>,
        assignment: C::Assignment,
        manager: C::ClauseManager,
        propagator: C::Propagator,
        restarter: C::Restarter,
        selector: C::VariableSelector,
    ) -> Self {
        let cnf: Cnf<C::Literal, C::LiteralStorage> = cnf.convert();
        let cdcl = Cdcl::from_parts(cnf, assignment, manager, propagator, restarter, selector);
        Self::Cdcl(Box::new(cdcl))
    }

    fn solve(&mut self) -> Option<Solutions> {
        match self {
            Self::Dpll(solver) => solver.solve(),
            Self::Cdcl(solver) => solver.solve(),
        }
    }

    fn solutions(&self) -> Solutions {
        match self {
            Self::Dpll(solver) => solver.solutions(),
            Self::Cdcl(solver) => solver.solutions(),
        }
    }

    fn stats(&self) -> SolutionStats {
        match self {
            Self::Dpll(solver) => solver.stats(),
            Self::Cdcl(solver) => solver.stats(),
        }
    }

    fn debug(&mut self) {
        match self {
            Self::Dpll(solver) => solver.debug(),
            Self::Cdcl(solver) => solver.debug(),
        }
    }
}

/// An enum representing the types of SAT solvers available.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord, ValueEnum)]
pub enum SolverType {
    /// A DPLL-based SAT solver.
    Dpll,
    /// A CDCL-based SAT solver.
    #[default]
    Cdcl,
}

impl Display for SolverType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Dpll => write!(f, "dpll"),
            Self::Cdcl => write!(f, "cdcl"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::variable_selection::VariableSelection as VSelTrait;

    #[test]
    fn test_generic_config_instantiation() {
        let _ = DefaultConfig;
    }

    #[test]
    fn test_default_config_type_bounds() {
        let _ = DefaultConfig;
        let _vs: <DefaultConfig as SolverConfig>::VariableSelector =
            Vsids::new::<Vec<PackedLiteral>>(10, &[], &[]);
    }

    #[test]
    fn test_solutions_display() {
        let s1 = Solutions::new(&[1, -2, 30]);
        assert_eq!(s1.to_string(), "1 -2 30");

        let mut assignments_vec: Vec<String> = s1
            .assignments
            .iter()
            .map(|val| val.get().to_string())
            .collect();
        assignments_vec.sort_by_key(|s| s.parse::<i32>().unwrap_or(0));
        let sorted_str = assignments_vec.join(" ");

        assert_eq!(sorted_str, "-2 1 30");

        let s2 = Solutions::new(&[]);
        assert_eq!(s2.to_string(), "");

        let s3 = Solutions::new(&[-5]);
        assert_eq!(s3.to_string(), "-5");
    }

    #[test]
    fn test_solutions_check_add() {
        let mut s = Solutions::default();
        let lit1_pos = NonZeroI32::new(1).unwrap();
        let lit2_neg = NonZeroI32::new(-2).unwrap();
        let lit3_pos = NonZeroI32::new(3).unwrap();

        assert!(!s.check(lit1_pos));
        s.add(lit1_pos);
        assert!(s.check(lit1_pos));
        assert!(!s.check(lit1_pos.checked_neg().unwrap()));

        s.add(lit2_neg);
        assert!(s.check(lit2_neg));
        assert!(!s.check(lit3_pos));

        assert_eq!(s.len(), 2);
        assert!(!s.is_empty());
    }
}
