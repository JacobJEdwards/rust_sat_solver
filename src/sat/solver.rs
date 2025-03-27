use crate::sat::assignment::Assignment;
use crate::sat::assignment::Solutions;
use crate::sat::assignment::VecAssignment;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use crate::sat::literal::PackedLiteral;
use crate::sat::phase_saving::{AdaptiveSavedPhases, PhaseSelector};
use crate::sat::preprocessing::Preprocessor;
use crate::sat::propagation::Propagator;
use crate::sat::propagation::WatchedLiterals;
use crate::sat::restarter::{Luby, Restarter};
use crate::sat::variable_selection::{FixedOrder, RandomOrder, VariableSelection, Vsids};
use smallvec::SmallVec;
use std::fmt::Debug;
use std::ops::{Index, IndexMut};
use std::slice::{Iter, IterMut};

pub trait LiteralStorage<L: Literal>:
    Index<usize, Output = L>
    + FromIterator<L>
    + Clone
    + From<Vec<L>>
    + Default
    + IndexMut<usize, Output = L>
    + Extend<L>
    + Debug
{
    fn push(&mut self, literal: L);
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn iter(&self) -> Iter<L>;
    fn iter_mut(&mut self) -> IterMut<L>;
    fn remove(&mut self, index: usize) -> L;
    fn clear(&mut self);
    fn swap(&mut self, a: usize, b: usize);
    unsafe fn get_unchecked(&self, index: usize) -> &L;
    unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut L;
    fn swap_remove(&mut self, index: usize) -> L {
        let last = self.len() - 1;
        self.swap(index, last);
        self.remove(last)
    }
}

impl<L: Literal> LiteralStorage<L> for Vec<L> {
    fn push(&mut self, literal: L) {
        self.push(literal);
    }

    fn len(&self) -> usize {
        self.len()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    fn iter(&self) -> Iter<L> {
        self.as_slice().iter()
    }

    fn iter_mut(&mut self) -> IterMut<L> {
        self.as_mut_slice().iter_mut()
    }

    fn remove(&mut self, index: usize) -> L {
        self.remove(index)
    }

    fn clear(&mut self) {
        self.clear();
    }

    fn swap(&mut self, a: usize, b: usize) {
        self.as_mut_slice().swap(a, b);
    }

    unsafe fn get_unchecked(&self, index: usize) -> &L {
        self.as_slice().get_unchecked(index)
    }

    unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut L {
        self.as_mut_slice().get_unchecked_mut(index)
    }
}

impl<L: Literal, const N: usize> LiteralStorage<L> for SmallVec<[L; N]> {
    fn push(&mut self, literal: L) {
        self.push(literal);
    }

    fn len(&self) -> usize {
        self.len()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    fn iter(&self) -> Iter<L> {
        self.as_slice().iter()
    }

    fn iter_mut(&mut self) -> IterMut<L> {
        self.as_mut_slice().iter_mut()
    }

    fn remove(&mut self, index: usize) -> L {
        self.remove(index)
    }

    fn clear(&mut self) {
        self.clear();
    }

    fn swap(&mut self, a: usize, b: usize) {
        self.as_mut_slice().swap(a, b);
    }

    unsafe fn get_unchecked(&self, index: usize) -> &L {
        self.as_slice().get_unchecked(index)
    }

    unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut L {
        self.as_mut_slice().get_unchecked_mut(index)
    }
}

pub trait SolverConfig: Debug {
    type Assignment: Assignment + Clone;
    type VariableSelector: VariableSelection<Self::PhaseSelector, Self::Literal> + Clone;
    type Literal: Literal + Clone;
    type LiteralStorage: LiteralStorage<Self::Literal>;
    type Restarter: Restarter + Clone;
    type PhaseSelector: PhaseSelector + Clone;
    type Propagator: Propagator<Self::Literal, Self::LiteralStorage, Self::Assignment> + Clone;
}

#[derive(Debug, Clone)]
pub struct DefaultConfig;

impl SolverConfig for DefaultConfig {
    type Assignment = VecAssignment;
    type VariableSelector = Vsids;
    type Literal = PackedLiteral;
    type LiteralStorage = SmallVec<[Self::Literal; 8]>;
    type Restarter = Luby;
    type PhaseSelector = AdaptiveSavedPhases;
    type Propagator = WatchedLiterals<Self::Literal, Self::LiteralStorage, Self::Assignment>;
}

pub trait Solver<C: SolverConfig = DefaultConfig> {
    fn new(cnf: Cnf<C::Literal, C::LiteralStorage>) -> Self;
    fn solve(&mut self) -> Option<Solutions>;
    fn solutions(&self) -> Solutions;
}

pub trait Preprocessable<L: Literal, S: LiteralStorage<L>> {
    fn preprocess(&mut self);
    fn add_preprocessor<T: Preprocessor<L, S> + 'static>(&mut self, preprocessor: T);
}
