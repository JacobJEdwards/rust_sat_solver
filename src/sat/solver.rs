use crate::sat::assignment::Assignment;
use crate::sat::assignment::Solutions;
use crate::sat::assignment::VecAssignment;
use crate::sat::clause_storage::LiteralStorage;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use crate::sat::literal::PackedLiteral;
use crate::sat::phase_saving::{AdaptiveSavedPhases, PhaseSelector, SavedPhases};
use crate::sat::propagation::{Propagator, UnitSearch};
use crate::sat::propagation::WatchedLiterals;
use crate::sat::restarter::{Luby, Restarter};
use crate::sat::variable_selection::{VariableSelection, Vsids, VsidsHeap};
use smallvec::SmallVec;
use std::fmt::Debug;

pub trait SolverConfig: Debug {
    type Assignment: Assignment + Clone;
    type VariableSelector: VariableSelection<Self::PhaseSelector, Self::Literal> + Clone;
    type Literal: Literal + Clone;
    type LiteralStorage: LiteralStorage<Self::Literal>;
    type Restarter: Restarter + Clone;
    type PhaseSelector: PhaseSelector + Clone;
    type Propagator: Propagator<Self::Literal, Self::LiteralStorage, Self::Assignment> + Clone;
}

#[macro_export]
macro_rules! solver_config {
    ($name:ident {
        Literal = $literal:ty,
        LiteralStorage = $storage:ty,
        Assignment = $assignment:ty,
        VariableSelector = $selector:ty,
        Propagator = $propagator:ty,
        Restarter = $restarter:ty,
        PhaseSelector = $phase_selector:ty
    }) => {
        #[derive(Debug, Clone, Default)]
        pub struct $name;

        impl SolverConfig for $name {
            type Literal = $literal;
            type LiteralStorage = $storage;
            type Assignment = $assignment;
            type VariableSelector = $selector;
            type Propagator = $propagator;
            type Restarter = $restarter;
            type PhaseSelector = $phase_selector;
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
            PhaseSelector = $phase_selector:ty
        }
    ) => {
        #[derive(Debug, Clone, Default)]
        pub struct $name<$($param $(: $bound)?),+> {
            #[allow(unused_parens)]
            _marker: PhantomData<($($param),+)>
        }

        impl<$($param $(: $bound)?),+> SolverConfig for $name<$($param),+> {
            type Literal = $literal;
            type LiteralStorage = $storage;
            type Assignment = $assignment;
            type VariableSelector = $selector;
            type Propagator = $propagator;
            type Restarter = $restarter;
            type PhaseSelector = $phase_selector;
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
        PhaseSelector = AdaptiveSavedPhases
    }
);

pub trait Solver<C: SolverConfig = DefaultConfig> {
    fn new(cnf: Cnf<C::Literal, C::LiteralStorage>) -> Self;
    fn solve(&mut self) -> Option<Solutions>;
    fn solutions(&self) -> Solutions;
}
