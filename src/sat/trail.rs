#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

use std::cmp::min;
use std::ops::{Index, IndexMut};
use crate::sat::assignment::{Assignment};
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;

#[derive(Debug, Clone, PartialEq, Eq, Default, Copy, Hash, PartialOrd, Ord)]
pub enum Reason {
    #[default]
    Decision,
    Unit(usize),
    Long(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Step {
    pub lit: Literal,
    pub decision_level: usize,
    pub reason: Reason,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Trail {
    t: Vec<Step>,
    pub curr_idx: usize,
    pub lit_to_level: Vec<usize>,
}

impl Index<usize> for Trail {
    type Output = Step;

    fn index(&self, index: usize) -> &Self::Output {
        &self.t[index]
    }
}

impl IndexMut<usize> for Trail {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.t[index]
    }
}

impl Trail {
    #[must_use] pub fn decision_level(&self) -> usize {
        let index = min(self.curr_idx, self.t.len() - 1);
        self.t[index].decision_level
    }

    #[must_use] pub fn last(&self) -> Literal {
        self.t[self.curr_idx].lit
    }

    #[must_use] pub fn len(&self) -> usize {
        self.t.len()
    }
    
    #[must_use] pub fn is_empty(&self) -> bool {
        self.t.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &Step> {
        self.t.iter()
    }

    #[must_use] pub fn new(cnf: &Cnf) -> Self {
        let initial = cnf.iter()
            .filter(|c| c.is_unit())
            .map(|c| Step {
                lit: c[0],
                decision_level: 0,
                reason: Reason::Unit(c[0].variable()),
            }).collect();
        
        Self {
            t: initial,
            curr_idx: 0,
            lit_to_level: vec![0; cnf.num_vars + 1],
        }
    }

    pub fn push(&mut self, lit: Literal, decision_level: usize, reason: Reason) {
        self.t.push(Step {
            lit,
            decision_level,
            reason,
        });
        self.lit_to_level[lit.variable()] = decision_level;
    }

    pub fn backstep<A: Assignment>(&mut self, a: &mut A) {
        let mut i = self.t.len() - 1;
        while self.t[i].reason != Reason::Decision {
            let lit = self.t[i].lit;
            a.unassign(lit.variable());
            i -= 1;
        }
        self.curr_idx = i;
        self.t.truncate(i);
    }

    pub fn backstep_to<A: Assignment>(&mut self, a: &mut A, level: usize) {
        let mut truncate_at = 0;
        for i in (0..self.t.len()).rev() {
            if self.t[i].decision_level >= level {
                a.unassign(self.t[i].lit.variable());
            } else {
                truncate_at = i + 1;
                break;
            }
        }
        self.curr_idx = truncate_at;
        self.t.truncate(truncate_at);
    }}
