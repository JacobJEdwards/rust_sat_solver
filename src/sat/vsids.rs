#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

use crate::sat::assignment::Assignment;
use std::ops::{Index, IndexMut};
// use std::collections::BinaryHeap;

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
    #[must_use] pub fn new(num_vars: usize, vars: &[usize]) -> Self {
        let mut vsids = Self(vec![0.0; num_vars + 1]);
        vsids.bumps(vars.iter().copied());
        vsids
    }

    pub fn decay(&mut self, decay: f64) {
        for (_, v) in self.iter_mut() {
            *v *= decay;
        }
    }

    pub fn bump(&mut self, i: usize) {
        self.0[i] += 1.0;
    }

    pub fn bumps<T: IntoIterator<Item = usize>>(&mut self, vars: T) {
        for i in vars {
            self.bump(i);
        }
    }

    #[must_use] pub fn get(&self, i: usize) -> f64 {
        self[i]
    }

    pub fn set(&mut self, i: usize, v: f64) {
        self.0.insert(i, v);
    }

    pub fn reset(&mut self) {
        self.0.clear();
    }

    pub fn decay_default(&mut self) {
        self.decay(DEFAULT_DECAY);
    }

    pub fn pick<A: Assignment>(&self, assignment: &A) -> Option<usize> {
        let mut max = 0.0;
        let mut max_i = None;

        for (i, v) in self.0.iter().enumerate() {
            if *v > max && assignment[i].is_unassigned() {
                max = *v;
                max_i = Some(i);
            }
        }
        max_i
    }

    pub fn iter(&self) -> impl Iterator<Item = (usize, f64)> + '_ {
        self.0.iter().enumerate().map(|(k, &v)| (k, v))
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (usize, &mut f64)> {
        self.0.iter_mut().enumerate()
    }
}
