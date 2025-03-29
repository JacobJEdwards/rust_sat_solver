#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

use crate::sat::assignment::Assignment;
use crate::sat::literal::Literal;
use crate::sat::phase_saving::PhaseSelector;
use itertools::Itertools;
use ordered_float::OrderedFloat;
use rand::rngs::ThreadRng;
use rand::seq::SliceRandom;
use rand::Rng;
use std::cell::RefCell;
use std::collections::BinaryHeap;
use dary_heap::DaryHeap;
use std::fmt::Debug;
use std::ops::{Index, IndexMut};

pub trait VariableSelection<Phase: PhaseSelector, L: Literal>: Debug + Clone {
    fn new(num_vars: usize, vars: &[L]) -> Self;
    fn pick<A: Assignment>(&mut self, assignment: &A) -> Option<L>;

    fn bumps<T: IntoIterator<Item = L>>(&mut self, vars: T);
    fn decay(&mut self, decay: f64);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ScoreEntry {
    score: OrderedFloat<f64>,
    lit_idx: usize,
}

const VSIDS_RESCALE_THRESHOLD: f64 = 1e100;
const VSIDS_RESCALE_FACTOR: f64 = 1e-100;

#[derive(Debug, Clone)]
pub struct VsidsHeap {
    scores: Vec<f64>,
    activity_inc: f64,
    heap: BinaryHeap<ScoreEntry>,
}

impl Index<usize> for VsidsHeap {
    type Output = f64;

    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.scores.get_unchecked(index) }
    }
}

impl IndexMut<usize> for VsidsHeap {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { self.scores.get_unchecked_mut(index) }
    }
}

impl VsidsHeap {
    fn bump_internal(&mut self, lit_idx: usize) {
        let score_ref = unsafe { self.scores.get_unchecked_mut(lit_idx) };
        *score_ref += self.activity_inc;
        let new_score = *score_ref;

        self.heap.push(ScoreEntry {
            score: OrderedFloat(new_score),
            lit_idx,
        });
    }

    fn rescale_scores(&mut self) {
        self.scores
            .iter_mut()
            .for_each(|s| *s *= VSIDS_RESCALE_FACTOR);
        self.activity_inc *= VSIDS_RESCALE_FACTOR;

        let mut score_entries: Vec<ScoreEntry> = Vec::with_capacity(self.scores.len());
        for (lit_idx, &score) in self.scores.iter().enumerate() {
            score_entries.push(ScoreEntry {
                score: OrderedFloat(score),
                lit_idx,
            });
        }
        self.heap = BinaryHeap::from(score_entries);
    }
}

impl<P: PhaseSelector, L: Literal> VariableSelection<P, L> for VsidsHeap {
    fn new(num_vars: usize, _: &[L]) -> Self {
        let scores = vec![0.0; num_vars * 2];
        let mut score_entries: Vec<ScoreEntry> = Vec::with_capacity(scores.len());
        for (lit_idx, &score) in scores.iter().enumerate() {
            score_entries.push(ScoreEntry {
                score: OrderedFloat(score),
                lit_idx,
            });
        }
        let heap = BinaryHeap::from(score_entries);

        Self {
            scores,
            activity_inc: 1.0,
            heap,
        }
    }

    fn pick<A: Assignment>(&mut self, assignment: &A) -> Option<L> {
        while let Some(entry) = self.heap.pop() {
            let current_score = unsafe { *self.scores.get_unchecked(entry.lit_idx) };

            if entry.score != OrderedFloat(current_score) {
                continue;
            }

            if assignment[entry.lit_idx / 2].is_unassigned() {
                return Some(L::from_index(entry.lit_idx));
            }
        }

        None
    }

    fn bumps<T: IntoIterator<Item = L>>(&mut self, vars: T) {
        for i in vars {
            self.bump_internal(i.index());
        }
    }

    fn decay(&mut self, decay: f64) {
        self.activity_inc /= decay;

        if self.activity_inc > VSIDS_RESCALE_THRESHOLD {
            self.rescale_scores();
        }
    }
}

#[derive(Debug, Clone, PartialEq, Default, PartialOrd)]
pub struct Vsids<const EARLY_EXIT: bool = false> {
    scores: Vec<f64>,
    activity_inc: f64,
    num_vars: usize,
}

impl<const E: bool> Index<usize> for Vsids<E> {
    type Output = f64;

    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.scores.get_unchecked(index) }
    }
}

impl<const E: bool> IndexMut<usize> for Vsids<E> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { self.scores.get_unchecked_mut(index) }
    }
}

impl<const E: bool> Vsids<E> {
    pub fn bump(&mut self, i: impl Literal) {
        self[i.index()] += self.activity_inc;
    }
}

impl<S: PhaseSelector, L: Literal, const E: bool> VariableSelection<S, L> for Vsids<E> {
    #[must_use]
    fn new(num_vars: usize, _: &[L]) -> Self {
        Self {
            scores: vec![0.0; num_vars * 2],
            activity_inc: 1.0,
            num_vars,
        }
    }

    fn pick<A: Assignment>(&mut self, assignment: &A) -> Option<L> {
        let mut max_score = f64::MIN;
        let mut max = None;
        
        for (i, &v) in self.scores.iter().enumerate() {
            
            let lit = L::from_index(i);
            if v > max_score && assignment[lit.variable() as usize].is_unassigned() {
                max = Some(lit);
                max_score = v;
                
                if E && v > self.activity_inc * 5.0 {
                    break;
                }
                
            }
        }
        max
    }

    fn bumps<T: IntoIterator<Item = L>>(&mut self, vars: T) {
        for i in vars {
            self.bump(i);
        }
    }

    fn decay(&mut self, decay: f64) {
        self.activity_inc /= decay;

        if self.activity_inc > VSIDS_RESCALE_THRESHOLD {
            self.scores.iter_mut().for_each(|s| *s *= VSIDS_RESCALE_FACTOR);
            self.activity_inc = VSIDS_RESCALE_FACTOR;
        }

    }
}

#[derive(Debug, Clone, Default)]
pub struct FixedOrder {
    var_count: usize,
    rand: RefCell<ThreadRng>,
}

impl<S: PhaseSelector, L: Literal> VariableSelection<S, L> for FixedOrder {
    fn new(num_vars: usize, _: &[L]) -> Self {
        Self {
            var_count: num_vars,
            rand: RefCell::new(rand::rng()),
        }
    }

    fn pick<A: Assignment>(&mut self, assignment: &A) -> Option<L> {
        #![allow(clippy::cast_possible_truncation)]
        (1..self.var_count as u32).find_map(|v| {
            if assignment[v as usize].is_unassigned() {
                let mut rng = self.rand.borrow_mut();
                let polarity = rng.random::<bool>();
                let lit = L::new(v, polarity);
                Some(lit)
            } else {
                None
            }
        })
    }

    fn bumps<T: IntoIterator<Item = L>>(&mut self, _: T) {}

    fn decay(&mut self, _: f64) {}
}

#[derive(Debug, Clone, Default)]
pub struct RandomOrder {
    var_count: usize,
    rand: RefCell<ThreadRng>,
}

impl<S: PhaseSelector, L: Literal> VariableSelection<S, L> for RandomOrder {
    fn new(num_vars: usize, _: &[L]) -> Self {
        Self {
            var_count: num_vars,
            rand: RefCell::new(rand::rng()),
        }
    }

    fn pick<A: Assignment>(&mut self, assignment: &A) -> Option<L> {
        #![allow(clippy::cast_possible_truncation)]
        let mut rng = self.rand.borrow_mut();
        let mut indices: Vec<usize> = (0..self.var_count).collect();
        indices.shuffle(&mut *rng);

        for i in indices {
            if assignment[i].is_unassigned() {
                let polarity = rng.random::<bool>();
                return Some(L::new(i as u32, polarity));
            }
        }
        None
    }

    fn bumps<T: IntoIterator<Item = L>>(&mut self, _: T) {}

    fn decay(&mut self, _: f64) {}
}
