#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

use crate::sat::assignment::Assignment;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use std::ops::{Index, IndexMut};
use itertools::Itertools;

#[derive(Debug, Clone, PartialEq, Eq, Default, Copy, Hash, PartialOrd, Ord)]
pub enum Reason {
    #[default]
    Decision,
    Unit(usize),
    Clause(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Step<L: Literal> {
    pub lit: L,
    pub decision_level: usize,
    pub reason: Reason,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Trail<L: Literal> {
    t: Vec<Step<L>>,
    pub curr_idx: usize,
    pub lit_to_level: Vec<usize>,
    pub lit_to_pos: Vec<usize>,
}

impl<L: Literal> Index<usize> for Trail<L> {
    type Output = Step<L>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.t[index]
    }
}

impl<L: Literal> IndexMut<usize> for Trail<L> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.t[index]
    }
}

impl<L: Literal> Trail<L> {
    #[must_use]
    pub fn decision_level(&self) -> usize {
        if self.curr_idx == 0 {
            return 0;
        }
        let index = self.curr_idx - 1;
        self.t[index].decision_level
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.t.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.t.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &Step<L>> {
        self.t.iter()
    }

    #[must_use]
    pub fn new(cnf: &Cnf<L>) -> Self {
        let initial = cnf
            .iter()
            .filter(|c| c.is_unit())
            .enumerate()
            .map(|(i, c)| Step {
                lit: c[0],
                decision_level: 0,
                reason: Reason::Unit(i),
            })
            .collect_vec();

        let mut vec = Vec::with_capacity(cnf.num_vars);

        let num_vars = cnf.num_vars;
        let mut lit_to_pos = vec![0; num_vars];
        for (i, step) in initial.iter().enumerate() {
            lit_to_pos[step.lit.variable() as usize] = i;
        }

        vec.extend(initial);

        Self {
            t: vec,
            curr_idx: 0,
            lit_to_level: vec![0; cnf.num_vars],
            lit_to_pos,
        }
    }

    pub fn push(&mut self, lit: L, decision_level: usize, reason: Reason) {
        if self.lit_to_pos[lit.variable() as usize] != 0 {
            return;
        }

        self.t.push(Step {
            lit,
            decision_level,
            reason,
        });
        self.lit_to_level[lit.variable() as usize] = decision_level;
        self.lit_to_pos[lit.variable() as usize] = self.t.len() - 1;
    }

    pub fn backstep_to<A: Assignment>(&mut self, a: &mut A, level: usize) {
        let mut truncate_at = 0;

        for i in (0..self.t.len()).rev() {
            let var = self.t[i].lit.variable();
            if self.lit_to_level[var as usize] >= level {
                a.unassign(var);
                self.lit_to_level[var as usize] = 0;
                self.lit_to_pos[var as usize] = 0;
            } else {
                truncate_at = i + 1;
                break;
            }
        }
        self.curr_idx = truncate_at;
        self.t.truncate(truncate_at);
    }
}
