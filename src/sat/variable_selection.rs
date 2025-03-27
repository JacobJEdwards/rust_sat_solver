#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

use crate::sat::assignment::Assignment;
use crate::sat::literal::{Literal};
use rand::seq::SliceRandom;
use std::ops::{Index, IndexMut};
use itertools::Itertools;
use rand::Rng;
use crate::sat::phase_saving::PhaseSelector;

pub trait VariableSelection<Phase: PhaseSelector, L: Literal> {
    fn new(num_vars: usize, vars: &[L]) -> Self;
    fn pick<A: Assignment>(&self, assignment: &A) -> Option<L>;

    fn bumps<T: IntoIterator<Item = L>>(&mut self, vars: T);
    fn decay(&mut self, decay: f64);
}

#[derive(Debug, Clone, PartialEq, Default, PartialOrd)]
pub struct Vsids {
    scores: Vec<f64>,
    activity_inc: f64,
    num_vars: usize,
}

impl Index<usize> for Vsids {
    type Output = f64;

    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.scores.get_unchecked(index) }
    }
}

impl IndexMut<usize> for Vsids {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { self.scores.get_unchecked_mut(index) }
    }
}

impl Vsids {
    pub fn bump(&mut self, i: impl Literal) {
        self[i.index()] += self.activity_inc;
    }
}

impl <S: PhaseSelector, L: Literal> VariableSelection<S, L> for Vsids {
    #[must_use]
    fn new(num_vars: usize, _: &[L]) -> Self {
        Self {
            scores: vec![0.0; num_vars * 2],
            activity_inc: 1.0,
            num_vars
        }
    }

    fn pick<A: Assignment>(&self, assignment: &A) -> Option<L> {
        let mut max = f64::MIN;
        let mut max_i = None;

        for (i, v) in self.scores.iter().enumerate() {
            let lit = L::from_index(i);
            if *v > max && assignment[i / 2].is_unassigned() {
                max = *v;
                max_i = Some(lit);
            }
        }
        max_i
    }

    fn bumps<T: IntoIterator<Item = L>>(&mut self, vars: T) {
        for i in vars {
            self.bump(i);
        }
    }

    fn decay(&mut self, decay: f64) {
        self.activity_inc *= 1.0 / decay;
        
        if self.activity_inc < 1e-100 {
            self.scores.iter_mut().for_each(|s| *s *= 1e-100);
            self.activity_inc = 1e-100;
        }
    }
}

#[derive(Debug, Clone, PartialEq, Default, Eq)]
pub struct FixedOrder(usize);

impl<S: PhaseSelector, L: Literal> VariableSelection<S, L> for FixedOrder {
    fn new(num_vars: usize, _: &[L]) -> Self {
        Self(num_vars)
    }

    fn pick<A: Assignment>(&self, assignment: &A) -> Option<L> {
        #![allow(clippy::cast_possible_truncation)]
        (1..self.0 as u32).find_map(|v| {
            let i = v as usize;
            if assignment[v as usize].is_unassigned() {
                let mut rng = rand::rng();
                Some(L::new(v, rng.random::<bool>()))
            } else {
                None
            }
        })
    }

    fn bumps<T: IntoIterator<Item = L>>(&mut self, _: T) {}

    fn decay(&mut self, _: f64) {}
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct RandomOrder(usize);

impl <S: PhaseSelector, L: Literal> VariableSelection<S, L> for RandomOrder {
    fn new(num_vars: usize, _: &[L]) -> Self {
        Self(num_vars * 2)
    }

    fn pick<A: Assignment>(&self, assignment: &A) -> Option<L> {
        #![allow(clippy::cast_possible_truncation)]
        let mut vec = (1..self.0 as u32).collect_vec();

        let mut rng = rand::rng();
        vec.shuffle(&mut rng);

        vec.iter().find_map(|v| {
            let i = *v as usize;
            let lit = L::from_index(i);

            if assignment[lit.variable() as usize].is_unassigned() {
                Some(lit)
            } else {
                None
            }
        })
    }

    fn bumps<T: IntoIterator<Item = L>>(&mut self, _: T) {}

    fn decay(&mut self, _: f64) {}
}
