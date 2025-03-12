#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
use crate::sat::literal::Literal;
use core::ops::{Index, IndexMut};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Clause {
    pub literals: Vec<Literal>,
    pub lbd: u32,
    pub deleted: bool,
}

impl FromIterator<Literal> for Clause {
    fn from_iter<I: IntoIterator<Item = Literal>>(iter: I) -> Self {
        Self {
            literals: iter.into_iter().collect(),
            lbd: 0,
            deleted: false,
        }
    }
}

impl Clause {
    #[must_use]
    pub const fn new(literals: Vec<Literal>) -> Self {
        Self {
            literals,
            lbd: 0,
            deleted: false,
        }
    }

    pub fn push(&mut self, literal: Literal) {
        if !self.literals.contains(&literal) {
            self.literals.push(literal);
        }
    }

    #[must_use]
    pub fn is_tautology(&self) -> bool {
        self.literals
            .iter()
            .any(|l| self.literals.contains(&l.negated()))
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.literals.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = &Literal> {
        self.literals.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Literal> {
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

impl Index<usize> for Clause {
    type Output = Literal;

    fn index(&self, index: usize) -> &Self::Output {
        &self.literals[index]
    }
}

impl IndexMut<usize> for Clause {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.literals[index]
    }
}

impl From<&Clause> for Vec<Literal> {
    fn from(clause: &Clause) -> Self {
        clause.literals.clone()
    }
}

impl From<Vec<i32>> for Clause {
    fn from(literals: Vec<i32>) -> Self {
        let literals = literals.into_iter().map(Literal::from).collect();
        Self::new(literals)
    }
}

impl From<&Vec<i32>> for Clause {
    fn from(literals: &Vec<i32>) -> Self {
        let literals: Vec<_> = literals.iter().map(|l| Literal::from(*l)).collect();
        Self::new(literals)
    }
}

impl From<Vec<Literal>> for Clause {
    fn from(literals: Vec<Literal>) -> Self {
        Self {
            literals,
            lbd: 0,
            deleted: false,
        }
    }
}

impl From<&Vec<Literal>> for Clause {
    fn from(literals: &Vec<Literal>) -> Self {
        Self {
            literals: literals.clone(),
            lbd: 0,
            deleted: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let clause = Clause::from(vec![1, 2, 3]);
        assert_eq!(clause.len(), 3);
    }

    #[test]
    fn test_iter() {
        let clause = Clause::from(vec![1, 2, 3]);
        let mut iter = clause.iter();
        assert_eq!(iter.next(), Some(&Literal::from(1)));
        assert_eq!(iter.next(), Some(&Literal::from(2)));
        assert_eq!(iter.next(), Some(&Literal::from(3)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter_mut() {
        let mut clause = Clause::from(vec![1, 2, 3]);
        let mut iter = clause.iter_mut();
        assert_eq!(iter.next(), Some(&mut Literal::from(1)));
        assert_eq!(iter.next(), Some(&mut Literal::from(2)));
        assert_eq!(iter.next(), Some(&mut Literal::from(3)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_swap() {
        let mut clause = Clause::from(vec![1, 2, 3]);
        clause.swap(0, 2);
        assert_eq!(clause[0], Literal::from(3));
        assert_eq!(clause[1], Literal::from(2));
        assert_eq!(clause[2], Literal::from(1));
    }
}
