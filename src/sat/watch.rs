#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
use crate::sat::clause::Clause;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Variable;
use crate::sat::literal::{Literal, PackedLiteral};
use smallvec::SmallVec;
use std::ops::{Index, IndexMut};

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct WatchedLiterals(Vec<SmallVec<[usize; 6]>>);

impl WatchedLiterals {
    #[must_use]
    pub fn new<L: Literal>(cnf: &Cnf<L>) -> Self {
        let mut watched_literals = vec![SmallVec::with_capacity(6); cnf.num_vars];

        for (i, clause) in cnf.iter().enumerate().filter(|(_, c)| !c.is_unit()) {
            let a = clause[0];
            let b = clause[1];

            #[cfg(debug_assertions)]
            debug_assert_ne!(a, b);

            watched_literals[a.variable() as usize].push(i);
            watched_literals[b.variable() as usize].push(i);
        }

        Self(watched_literals)
    }

    pub fn add_clause<L: Literal>(&mut self, clause: &Clause<L>, idx: usize) {
        let a = clause[0];
        let b = clause[1];

        assert_ne!(a, b);

        self[a.variable()].push(idx);
        self[b.variable()].push(idx);
    }
}

impl Index<Variable> for WatchedLiterals {
    type Output = SmallVec<[usize; 6]>;

    fn index(&self, index: Variable) -> &Self::Output {
        &self.0[index as usize]
    }
}

impl IndexMut<Variable> for WatchedLiterals {
    fn index_mut(&mut self, index: Variable) -> &mut Self::Output {
        &mut self.0[index as usize]
    }
}

impl <L: Literal> Index<L> for WatchedLiterals {
    type Output = SmallVec<[usize; 6]>;

    fn index(&self, index: L) -> &Self::Output {
        &self[index.variable()]
    }
}

impl <L: Literal> IndexMut<L> for WatchedLiterals {
    fn index_mut(&mut self, index: L) -> &mut Self::Output {
        &mut self[index.variable()]
    }
}
