use crate::sat::assignment::Assignment;
use crate::sat::assignment::VecAssignment;
use crate::sat::clause_storage::LiteralStorage;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use crate::sat::literal::PackedLiteral;
use crate::sat::propagation::Propagator;
use crate::sat::propagation::WatchedLiterals;
use crate::sat::restarter::{Luby, Restarter};
use crate::sat::variable_selection::{VariableSelection};
use crate::sat::variable_selection::Vsids;
use smallvec::SmallVec;
use rustc_hash::{FxHashSet};
use std::fmt::Debug;
use std::num::NonZeroI32;

/// Contains information about a solution.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SolutionStats {
    /// How many conflicts occurred.
    pub conflicts: usize,
    /// How many decisions were made.
    pub decisions: usize,
    /// How many propagations occurred.
    pub propagations: usize,
    /// How many times did the solver restart.
    pub restarts: usize,
}

/// Represents the solutions to a given formula.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Solutions {
    /// Set of assignments. Negative / positive determines polarity.
    pub assignments: FxHashSet<NonZeroI32>,
}

impl Solutions {
    #[must_use]
    pub fn new(s: &[i32]) -> Self {
        Self {
            assignments: s.iter().copied().filter_map(NonZeroI32::new).collect(),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &NonZeroI32> {
        self.assignments.iter()
    }

    #[must_use]
    pub fn check(&self, i: NonZeroI32) -> bool {
        self.assignments.contains(&i)
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.assignments.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.assignments.is_empty()
    }
}

/// A trait that defines the configuration for a SAT solver.
/// It includes types for literals, assignment, variable selection,
pub trait SolverConfig: Debug {
    /// The type of storage of the current assignment.
    type Assignment: Assignment + Clone;
    /// The variable selection strategy.
    type VariableSelector: VariableSelection<Self::Literal> + Clone;
    /// The type of the literal.
    type Literal: Literal + Clone;
    /// The type of the literal storage.
    type LiteralStorage: LiteralStorage<Self::Literal>;
    /// The restarter strategy.
    type Restarter: Restarter + Clone;
    /// The unit propagation strategy.
    type Propagator: Propagator<Self::Literal, Self::LiteralStorage, Self::Assignment> + Clone;
}

/// A macro to define a solver configuration.
///
/// # Examples
///
/// ```
/// solver_config! {
///    MySolverConfig {
///        Literal = MyLiteral,
///        LiteralStorage = MyLiteralStorage,
///        Assignment = MyAssignment,
///        VariableSelector = MyVariableSelector,
///        Propagator = MyPropagator,
///        Restarter = MyRestarter,
///   }
/// }
///
/// solver_config! {
///   <T: Debug + Literal>
///   MyGenericSolverConfig {
///       Literal = T,
///       LiteralStorage = MyLiteralStorage<T>,
///       Assignment = MyAssignment,
///       VariableSelector = MyVariableSelector,
///       Propagator = MyPropagator,
///       Restarter = MyRestarter,
///   }
/// }
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
    }) => {
        /// Generated solver configuration.
        #[derive(Debug, Clone, Default)]
        pub struct $name;

        /// Implements the `SolverConfig` trait for the generated configuration.
        impl SolverConfig for $name {
            type Literal = $literal;
            type LiteralStorage = $storage;
            type Assignment = $assignment;
            type VariableSelector = $selector;
            type Propagator = $propagator;
            type Restarter = $restarter;
        }
    };

    (
        <$($param:ident $(: $bound:path)?),+>
        $name:ident {
            Literal = $literal:ty,
            LiteralStorage = $storage:ty,
            Assignment = $assignment:ty,
            VariableSelector = $selector:ty,
            Propagator = $propagator:ty,
            Restarter = $restarter:ty,
        }
    ) => {
        /// Generated solver configuration with generic parameters.
        #[derive(Debug, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name<$($param $(: $bound)?),+> {
            #[allow(unused_parens)]
            _marker: std::marker::PhantomData<($($param),+)>
        }

        /// Implements the `SolverConfig` trait for the generated configuration with generic parameters.
        impl<$($param $(: $bound)?),+> SolverConfig for $name<$($param),+> {
            type Literal = $literal;
            type LiteralStorage = $storage;
            type Assignment = $assignment;
            type VariableSelector = $selector;
            type Propagator = $propagator;
            type Restarter = $restarter;
        }
    };
}

pub use solver_config;

solver_config!(
    DefaultConfig {
        Literal = PackedLiteral,
        LiteralStorage = SmallVec<[PackedLiteral; 8]>,
        Assignment = VecAssignment,
        VariableSelector = Vsids,
        Propagator = WatchedLiterals<PackedLiteral, SmallVec<[PackedLiteral; 8]>, VecAssignment>,
        Restarter = Luby,
    }
);

/// A trait that defines the interface for a SAT solver.
/// It includes methods for creating a new solver instance,
/// solving a SAT problem, and retrieving solutions.
///
/// Takes a configuration type `C` that implements the `SolverConfig` trait.
pub trait Solver<C: SolverConfig = DefaultConfig> {
    /// Creates a new instance of the solver with the given CNF formula.
    fn new(cnf: Cnf<C::Literal, C::LiteralStorage>) -> Self;

    /// Attempts to solve the given CNF formula.
    fn solve(&mut self) -> Option<Solutions>;

    /// Returns the current assignment of variables.
    fn solutions(&self) -> Solutions;

    /// Returns information about the solution.
    fn stats(&self) -> SolutionStats;
}
