#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
use crate::sat::literal::{Literal, PackedLiteral};
use core::ops::{Index, IndexMut};
use smallvec::SmallVec;
use std::collections::HashSet;
use std::hash::Hash;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Clause<L: Literal = PackedLiteral> {
    pub literals: SmallVec<[L; 10]>,
    pub lbd: u32,
    pub deleted: bool,
    pub is_learnt: bool,
}

impl<T: Literal> FromIterator<T> for Clause<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self {
            literals: iter.into_iter().collect(),
            lbd: 0,
            deleted: false,
            is_learnt: false,
        }
    }
}

impl<T: Literal + Hash + Eq> Clause<T> {
    #[must_use]
    pub fn new(literals: Vec<T>) -> Self {
        let literals = literals
            .into_iter()
            .collect::<HashSet<_>>()
            .into_iter()
            .collect();

        Self {
            literals,
            lbd: 0,
            deleted: false,
            is_learnt: false,
        }
    }

    pub fn push(&mut self, literal: T) {
        if !self.literals.contains(&literal) {
            self.literals.push(literal);
        }
    }

    #[must_use]
    pub fn is_tautology(&self) -> bool {
        let mut set = HashSet::new();

        for lit in &self.literals {
            if set.contains(&lit.negated()) {
                return true;
            }
            set.insert(lit);
        }

        false
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.literals.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.literals.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.literals.iter_mut()
    }

    pub fn swap(&mut self, i: usize, j: usize) {
        self.literals.swap(i, j);
    }

    #[must_use]
    pub fn is_unit(&self) -> bool {
        self.len() == 1
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[must_use]
    pub const fn is_deleted(&self) -> bool {
        self.deleted
    }

    pub fn delete(&mut self) {
        self.deleted = true;
    }

    pub fn remove_literal(&mut self, idx: usize) {
        self.literals.remove(idx);
    }
}

impl<T: Literal> Index<usize> for Clause<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        &self.literals[index]
    }
}

impl<T: Literal> IndexMut<usize> for Clause<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.literals[index]
    }
}

impl<T: Literal> From<&Clause<T>> for Vec<T> {
    fn from(clause: &Clause<T>) -> Self {
        clause.literals.to_vec()
    }
}

impl<T: Literal + Eq + Hash> From<Vec<i32>> for Clause<T> {
    fn from(literals: Vec<i32>) -> Self {
        let literals = literals
            .into_iter()
            .map(|l| {
                let pol = l.is_positive();
                let var = l.unsigned_abs();
                T::new(var, pol)
            })
            .collect();
        Self::new(literals)
    }
}

impl<T: Literal> From<Vec<T>> for Clause<T> {
    fn from(literals: Vec<T>) -> Self {
        Self {
            literals: SmallVec::from(literals),
            lbd: 0,
            deleted: false,
            is_learnt: false,
        }
    }
}

impl<T: Literal> From<&Vec<T>> for Clause<T> {
    fn from(literals: &Vec<T>) -> Self {
        Self {
            literals: SmallVec::from(literals.clone()),
            lbd: 0,
            deleted: false,
            is_learnt: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let clause: Clause = Clause::from(vec![1, 2, 3]);
        assert_eq!(clause.len(), 3);
    }

    #[test]
    fn test_iter() {
        let clause: Clause = Clause::from(vec![1, 2, 3]);
        let mut iter = clause.iter();
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter_mut() {
        let mut clause: Clause = Clause::from(vec![1, 2, 3]);
        let mut iter = clause.iter_mut();
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_swap() {
        let mut clause: Clause = Clause::from(vec![1, 2, 3]);
        clause.swap(0, 2);
    }
}
