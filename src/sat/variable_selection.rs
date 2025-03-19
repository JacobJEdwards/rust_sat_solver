#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

use crate::sat::assignment::Assignment;
use crate::sat::literal::Variable;
use rand::seq::SliceRandom;
use std::ops::{Index, IndexMut};

pub trait VariableSelection {
    fn new(num_vars: usize, vars: &[Variable]) -> Self;
    fn pick<A: Assignment>(&self, assignment: &A) -> Option<Variable>;

    fn bumps<T: IntoIterator<Item = Variable>>(&mut self, vars: T);
    fn decay(&mut self, decay: f64);
}

#[derive(Debug, Clone, PartialEq, Default, PartialOrd)]
pub struct Vsids(Vec<f64>);

impl Index<usize> for Vsids {
    type Output = f64;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl IndexMut<usize> for Vsids {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

const DEFAULT_DECAY: f64 = 0.95;

impl Vsids {
    pub fn bump(&mut self, i: Variable) {
        self.0[i as usize] += 1.0;
    }
    pub fn set(&mut self, i: usize, v: f64) {
        self.0.insert(i, v);
    }

    pub fn iter(&self) -> impl Iterator<Item = (usize, f64)> + '_ {
        self.0.iter().enumerate().map(|(k, &v)| (k, v))
    }
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (usize, &mut f64)> {
        self.0.iter_mut().enumerate()
    }
}

impl VariableSelection for Vsids {
    #[must_use]
    fn new(num_vars: usize, vars: &[Variable]) -> Self {
        let mut vsids = Self(vec![0.0; num_vars]);
        vsids.bumps(vars.iter().copied());
        vsids
    }

    fn pick<A: Assignment>(&self, assignment: &A) -> Option<Variable> {
        let mut max = f64::MIN;
        let mut max_i = None;

        for (i, v) in self.0.iter().enumerate() {
            if *v > max && assignment[i].is_unassigned() {
                max = *v;
                max_i = Some(i as Variable);
            }
        }
        max_i
    }

    fn bumps<T: IntoIterator<Item = Variable>>(&mut self, vars: T) {
        for i in vars {
            self.bump(i);
        }
    }

    fn decay(&mut self, decay: f64) {
        for (_, v) in self.iter_mut() {
            *v *= decay;
        }
    }
}

pub struct FixedOrder(usize);

impl VariableSelection for FixedOrder {
    fn new(num_vars: usize, _: &[Variable]) -> Self {
        Self(num_vars)
    }

    fn pick<A: Assignment>(&self, assignment: &A) -> Option<Variable> {
        (1..self.0)
            .find(|&i| assignment[i].is_unassigned())
            .map(|i| i as Variable)
    }

    fn bumps<T: IntoIterator<Item = Variable>>(&mut self, _: T) {}

    fn decay(&mut self, _: f64) {}
}

pub struct RandomOrder(usize);

impl VariableSelection for RandomOrder {
    fn new(num_vars: usize, _: &[Variable]) -> Self {
        Self(num_vars)
    }

    fn pick<A: Assignment>(&self, assignment: &A) -> Option<Variable> {
        let mut vec = (1..self.0 as u32).collect::<Vec<_>>();

        let mut rng = rand::rng();
        vec.shuffle(&mut rng);

        vec.iter().find(|v| !assignment.is_assigned(**v)).copied()
    }

    fn bumps<T: IntoIterator<Item = Variable>>(&mut self, _: T) {}

    fn decay(&mut self, _: f64) {}
}
