#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

use crate::sat::assignment::Assignment;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use crate::sat::solver::LiteralStorage;
use itertools::Itertools;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

#[derive(Debug, Clone, PartialEq, Eq, Default, Copy, Hash, PartialOrd, Ord)]
pub enum Reason {
    #[default]
    Decision,
    Unit(usize),
    Clause(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Part<L: Literal> {
    pub(crate) lit: L,
    decision_level: usize,
    pub(crate) reason: Reason,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Trail<L: Literal, S: LiteralStorage<L>> {
    t: Vec<Part<L>>,
    pub curr_idx: usize,
    pub lit_to_level: Vec<usize>,
    pub lit_to_pos: Vec<usize>,
    marker: PhantomData<*const S>,
}

impl<L: Literal, S: LiteralStorage<L>> Index<usize> for Trail<L, S> {
    type Output = Part<L>;

    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.t.get_unchecked(index) }
    }
}

impl<L: Literal, S: LiteralStorage<L>> IndexMut<usize> for Trail<L, S> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { self.t.get_unchecked_mut(index) }
    }
}

impl<L: Literal, S: LiteralStorage<L>> Trail<L, S> {
    #[must_use]
    pub fn decision_level(&self) -> usize {
        if self.curr_idx == 0 {
            return 0;
        }

        let index = self.curr_idx - 1;
        self[index].decision_level
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.t.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.t.is_empty()
    }

    #[must_use]
    pub fn new(cnf: &Cnf<L, S>) -> Self {
        let num_vars = cnf.num_vars;
        let mut lit_to_pos = vec![0; num_vars];

        let mut vec = Vec::with_capacity(cnf.num_vars);

        vec.extend(
            cnf.iter()
                .filter(|c| c.is_unit())
                .enumerate()
                .map(|(i, c)| {
                    let lit = c[0];
                    unsafe {
                        *lit_to_pos.get_unchecked_mut(lit.variable() as usize) = i;
                    }

                    Part {
                        lit,
                        decision_level: 0,
                        reason: Reason::Unit(i),
                    }
                }),
        );

        Self {
            t: vec,
            curr_idx: 0,
            lit_to_level: vec![0; cnf.num_vars],
            lit_to_pos,
            marker: PhantomData,
        }
    }

    pub fn push(&mut self, lit: L, decision_level: usize, reason: Reason) {
        unsafe {
            if *self.lit_to_pos.get_unchecked(lit.variable() as usize) != 0 {
                return;
            }
        }

        self.t.push(Part {
            lit,
            decision_level,
            reason,
        });
        let var = lit.variable() as usize;
        unsafe {
            *self.lit_to_level.get_unchecked_mut(var) = decision_level;
            *self.lit_to_pos.get_unchecked_mut(var) = self.t.len().wrapping_sub(1);
        }
    }

    pub fn backstep_to<A: Assignment>(&mut self, a: &mut A, level: usize) {
        let mut truncate_at = 0;

        for i in (0..self.len()).rev() {
            let var = self[i].lit.variable();
            unsafe {
                if *self.lit_to_level.get_unchecked(var as usize) >= level {
                    a.unassign(var);
                    *self.lit_to_level.get_unchecked_mut(var as usize) = 0;
                    *self.lit_to_pos.get_unchecked_mut(var as usize) = 0;
                } else {
                    truncate_at = i.wrapping_add(1);
                    break;
                }
            }
        }

        self.curr_idx = truncate_at;
        self.t.truncate(truncate_at);
    }
}
