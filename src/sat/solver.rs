use crate::sat::assignment::Assignment;
use crate::sat::assignment::Solutions;
use crate::sat::assignment::VecAssignment;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use crate::sat::literal::PackedLiteral;
use crate::sat::phase_saving::{PhaseSelector, SavedPhases};
use crate::sat::preprocessing::Preprocessor;
use crate::sat::propagation::WatchedLiterals;
use crate::sat::propagation::{Propagator};
use crate::sat::restarter::{Luby, Restarter};
use crate::sat::variable_selection::{VariableSelection, Vsids};
use std::fmt::Debug;

pub trait SolverConfig: Debug {
    type Assignment: Assignment + Clone;
    type VariableSelector: VariableSelection + Clone;
    type Literal: Literal + Clone;
    type Restarter: Restarter + Clone;
    type PhaseSelector: PhaseSelector + Clone;
    type Propagator: Propagator<Self::Literal, Self::Assignment> + Clone;
}

#[derive(Debug, Clone)]
pub struct DefaultConfig;

impl SolverConfig for DefaultConfig {
    type Assignment = VecAssignment;
    type VariableSelector = Vsids;
    type Literal = PackedLiteral;
    type Restarter = Luby;
    type PhaseSelector = SavedPhases;
    type Propagator = WatchedLiterals<Self::Literal, Self::Assignment>;
}

pub trait Solver<C: SolverConfig = DefaultConfig> {
    fn new(cnf: Cnf<C::Literal>) -> Self;
    fn solve(&mut self) -> Option<Solutions>;
    fn solutions(&self) -> Solutions;
}

pub trait Preprocessable <L: Literal>{
    fn preprocess(&mut self);
    fn add_preprocessor<T: Preprocessor<L> + 'static>(&mut self, preprocessor: T);
}
