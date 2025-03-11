#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
use crate::sat::literal::Literal;
use core::ops::{Index, IndexMut};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq, Copy, Default, Hash, PartialOrd, Ord)]
pub enum VarState {
    #[default]
    Unassigned,
    Assigned(bool),
}

impl VarState {
    #[must_use] pub const fn is_assigned(self) -> bool {
        matches!(self, Self::Assigned(_))
    }

    #[must_use] pub const fn is_unassigned(self) -> bool {
        !self.is_assigned()
    }

    #[must_use] pub const fn is_true(self) -> bool {
        match self {
            Self::Assigned(b) => b,
            Self::Unassigned => false,
        }
    }

    #[must_use] pub const fn is_false(self) -> bool {
        match self {
            Self::Assigned(b) => !b,
            Self::Unassigned => false,
        }
    }
}

impl From<VarState> for Option<bool> {
    fn from(s: VarState) -> Self {
        match s {
            VarState::Assigned(b) => Some(b),
            VarState::Unassigned => None,
        }
    }
}

impl From<Option<bool>> for VarState {
    fn from(b: Option<bool>) -> Self {
        b.map_or(Self::Unassigned, VarState::Assigned)
    }
}

pub trait Assignment: Index<usize, Output = VarState> + IndexMut<usize, Output = VarState> {
    fn new(n: usize) -> Self;

    fn set(&mut self, lit: usize, b: bool);

    fn assign(&mut self, l: Literal) {
        self.set(l.variable(), l.polarity());
    }

    fn unassign(&mut self, i: usize);

    fn get_solutions(&self) -> Solutions;

    fn is_assigned(&self, i: usize) -> bool {
        self[i].is_assigned()
    }

    fn var_value(&self, i: usize) -> Option<bool> {
        self[i].into()
    }

    fn literal_value(&self, l: Literal) -> Option<bool> {
        self.var_value(l.variable()).map(|b| b ^ l.is_negated())
    }
    
    fn len(&self) -> usize;
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct VecAssignment(Vec<VarState>);


impl Index<usize> for VecAssignment {
    type Output = VarState;

    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.0.get_unchecked(index) }
    }
}

impl IndexMut<usize> for VecAssignment {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { self.0.get_unchecked_mut(index) }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Solutions(Vec<usize>);

impl Index<usize> for Solutions {
    type Output = usize;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl IndexMut<usize> for Solutions {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}


impl Solutions {
    pub fn new(s: Vec<usize>) -> Self {
        Self(s)
    }
    
    pub fn iter(&self) -> impl Iterator<Item = &usize> {
        self.0.iter()
    }
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut usize> {
        self.0.iter_mut()
    }
    
    pub fn check(&self, i: usize) -> bool {
        self.0.contains(&i)
    }

    pub fn empty() -> Self {
        Solutions(Vec::new())
    }
    
    pub fn len(&self) -> usize {
        self.0.len()
    }
    
    pub fn contains(&self, i: usize) -> bool {
        self.0.contains(&i)
    }
}

impl Assignment for VecAssignment {
    fn new(n: usize) -> Self {
        Self(vec![VarState::Unassigned; n + 1])
    }

    fn set(&mut self, lit: usize, b: bool) {
        self[lit] = VarState::Assigned(b);
    }

    fn unassign(&mut self, i: usize) {
        self[i] = VarState::Unassigned;
    }

    fn get_solutions(&self) -> Solutions {
        Solutions::new(
        self.0
            .iter()
            .enumerate()
            .filter_map(|(i, s)| match s {
                VarState::Assigned(true) => Some(i),
                _ => None,
            })
            .collect()
        )
    }
    
    fn len(&self) -> usize {
        self.0.len()
    }
}

pub struct HashMapAssignment(HashMap<usize, VarState>);

impl Index<usize> for HashMapAssignment {
    type Output = VarState;

    fn index(&self, index: usize) -> &Self::Output {
        self.0.get(&index).unwrap_or(&VarState::Unassigned)
    }
}

impl IndexMut<usize> for HashMapAssignment {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.0.entry(index).or_insert(VarState::Unassigned)
    }
}

impl Assignment for HashMapAssignment {
    fn new(_: usize) -> Self {
        Self(HashMap::default())
    }

    fn set(&mut self, lit: usize, b: bool) {
        self.0.insert(lit, VarState::Assigned(b));
    }

    fn unassign(&mut self, i: usize) {
        self.0.remove(&i);
    }

    fn get_solutions(&self) -> Solutions {
        Solutions::new(
        self.0
            .iter()
            .filter_map(|(i, s)| match s {
                VarState::Assigned(true) => Some(i),
                _ => None,
            })
            .copied()
            .collect()
        )
    }

    fn is_assigned(&self, i: usize) -> bool {
        self.0.contains_key(&i)
    }
    
    fn len(&self) -> usize {
        self.0.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_var_state() {
        assert!(VarState::Unassigned.is_unassigned());
        assert!(!VarState::Unassigned.is_assigned());
        assert!(!VarState::Unassigned.is_true());
        assert!(!VarState::Unassigned.is_false());

        assert!(!VarState::Assigned(true).is_unassigned());
        assert!(VarState::Assigned(true).is_assigned());
        assert!(VarState::Assigned(true).is_true());
        assert!(!VarState::Assigned(true).is_false());

        assert!(!VarState::Assigned(false).is_unassigned());
        assert!(VarState::Assigned(false).is_assigned());
        assert!(!VarState::Assigned(false).is_true());
        assert!(VarState::Assigned(false).is_false());
    }

    #[test]
    fn test_assignment() {
        let mut a = VecAssignment::new(3);
        a.set(1, true);
        a.set(2, false);
        a.set(3, true);

        assert!(a.is_assigned(1));
        assert!(a.is_assigned(2));
        assert!(a.is_assigned(3));

        assert_eq!(a.var_value(1), Some(true));
        assert_eq!(a.var_value(2), Some(false));
        assert_eq!(a.var_value(3), Some(true));

        assert_eq!(a.literal_value(Literal::new(1, false)), Some(false));
        assert_eq!(a.literal_value(Literal::new(2, true)), Some(false));
        assert_eq!(a.literal_value(Literal::new(3, false)), Some(false));

        a.unassign(1);
        assert!(!a.is_assigned(1));
        assert_eq!(a.var_value(1), None);

        let s = a.get_solutions();
        
        assert_eq!(s, Solutions::new(vec![3]));
    }
    
    #[test]
    fn test_hashmap_assignment() {
        let mut a = HashMapAssignment::new(3);
        a.set(1, true);
        a.set(2, false);
        a.set(3, true);

        assert!(a.is_assigned(1));
        assert!(a.is_assigned(2));
        assert!(a.is_assigned(3));

        assert_eq!(a.var_value(1), Some(true));
        assert_eq!(a.var_value(2), Some(false));
        assert_eq!(a.var_value(3), Some(true));

        assert_eq!(a.literal_value(Literal::new(1, false)), Some(false));
        assert_eq!(a.literal_value(Literal::new(2, true)), Some(false));
        assert_eq!(a.literal_value(Literal::new(3, false)), Some(false));

        a.unassign(1);
        assert!(!a.is_assigned(1));
        assert_eq!(a.var_value(1), None);

        let s = a.get_solutions();
        
        assert_eq!(s, Solutions::new(vec![3]));
    }
    
    #[test]
    fn test_assignment_unassigned() {
        let a = VecAssignment::new(3);
        assert!(!a.is_assigned(1));
        assert!(!a.is_assigned(2));
        assert!(!a.is_assigned(3));
    }
}
    