#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
use crate::sat::assignment::{Assignment, VecAssignment};
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
    pub trail: Vec<Step>,
    pub curr_idx: usize,
    pub lit_to_level: Vec<usize>,
}

impl Trail {
    #[must_use] pub fn decision_level(&self) -> usize {
        self.trail[self.curr_idx].decision_level
    }

    #[must_use] pub fn last(&self) -> Literal {
        self.trail[self.curr_idx].lit
    }

    #[must_use] pub fn len(&self) -> usize {
        self.trail.len()
    }
    
    #[must_use] pub fn is_empty(&self) -> bool {
        self.trail.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &Step> {
        self.trail.iter()
    }

    #[must_use] pub fn new(cnf: &Cnf) -> Self {
        Self {
            trail: Vec::with_capacity(cnf.num_vars + 1),
            curr_idx: 0,
            lit_to_level: vec![0; cnf.num_vars + 1],
        }
    }

    pub fn push(&mut self, lit: Literal, decision_level: usize, reason: Reason) {
        self.trail.push(Step {
            lit,
            decision_level,
            reason,
        });
        self.lit_to_level[lit.variable()] = decision_level;
    }

    pub fn backstep(&mut self, a: &mut VecAssignment) {
        let mut i = self.trail.len() - 1;
        while self.trail[i].reason != Reason::Decision {
            let lit = self.trail[i].lit;
            a.unassign(lit.variable());
            i -= 1;
        }
        self.curr_idx = i;
        self.trail.truncate(i);
    }

    pub fn backstep_to<A: Assignment>(&mut self, a: &mut A, level: usize) {
        let mut i = self.trail.len() - 1;
        while self.trail[i].decision_level > level {
            let lit = self.trail[i].lit;
            a.unassign(lit.variable());
            i -= 1;
        }
        self.curr_idx = i;
        self.trail.truncate(i);
    }
}
