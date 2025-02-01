// #![warn(
//     clippy::all,
//     clippy::restriction,
//     clippy::pedantic,
//     clippy::nursery,
//     clippy::cargo,
// )]
use crate::sat::literal::Literal;
use core::ops::{Index, IndexMut};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Clause {
    pub literals: Vec<Literal>,
    pub watched: (usize, usize), // move to be in literals
    pub lbd: u32,
    pub deleted: bool,
}

impl Clause {
    pub fn new(literals: Vec<i32>) -> Self {
        let len = literals.len();
        let literals = literals.into_iter().map(Literal::from).collect();

        Self {
            literals,
            watched: if len > 1 { (0, 1) } else { (0, 0) },
            lbd: 0,
            deleted: false,
        }
    }

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

    pub fn is_unit(&self) -> bool {
        self.len() == 1
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn is_deleted(&self) -> bool {
        self.deleted
    }

    pub fn delete(&mut self) {
        self.deleted = true;
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
        Self::new(literals)
    }
}

impl From<&Vec<i32>> for Clause {
    fn from(literals: &Vec<i32>) -> Self {
        Self::new(literals.clone())
    }
}

impl From<Vec<Literal>> for Clause {
    fn from(literals: Vec<Literal>) -> Self {
        let watched = if literals.len() > 1 { (0, 1) } else { (0, 0) };

        Self {
            literals,
            watched,
            lbd: 0,
            deleted: false,
        }
    }
}

impl From<&Vec<Literal>> for Clause {
    fn from(literals: &Vec<Literal>) -> Self {
        let watched = if literals.len() > 1 { (0, 1) } else { (0, 0) };
        Self {
            literals: literals.clone(),
            watched,
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
        let clause = Clause::new(vec![1, 2, 3]);
        assert_eq!(clause.len(), 3);
    }

    #[test]
    fn test_iter() {
        let clause = Clause::new(vec![1, 2, 3]);
        let mut iter = clause.iter();
        assert_eq!(iter.next(), Some(&Literal::from(1)));
        assert_eq!(iter.next(), Some(&Literal::from(2)));
        assert_eq!(iter.next(), Some(&Literal::from(3)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter_mut() {
        let mut clause = Clause::new(vec![1, 2, 3]);
        let mut iter = clause.iter_mut();
        assert_eq!(iter.next(), Some(&mut Literal::from(1)));
        assert_eq!(iter.next(), Some(&mut Literal::from(2)));
        assert_eq!(iter.next(), Some(&mut Literal::from(3)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_swap() {
        let mut clause = Clause::new(vec![1, 2, 3]);
        clause.swap(0, 2);
        assert_eq!(clause[0], Literal::from(3));
        assert_eq!(clause[1], Literal::from(2));
        assert_eq!(clause[2], Literal::from(1));
    }
}
