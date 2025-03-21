#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
use crate::sat::literal::Literal;
use crate::sat::literal::PackedLiteral;
use crate::sat::literal::Variable;
use core::ops::{Index, IndexMut};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq, Copy, Default, Hash, PartialOrd, Ord)]
pub enum VarState {
    #[default]
    Unassigned,
    Assigned(bool),
}

impl VarState {
    #[must_use]
    pub const fn is_assigned(self) -> bool {
        matches!(self, Self::Assigned(_))
    }

    #[must_use]
    pub const fn is_unassigned(self) -> bool {
        !self.is_assigned()
    }

    #[must_use]
    pub const fn is_true(self) -> bool {
        match self {
            Self::Assigned(b) => b,
            Self::Unassigned => false,
        }
    }

    #[must_use]
    pub const fn is_false(self) -> bool {
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

    fn set(&mut self, var: Variable, b: bool);

    fn assign(&mut self, l: impl Literal) {
        self.set(l.variable(), l.polarity());
    }

    fn unassign(&mut self, i: Variable);

    fn get_solutions(&self) -> Solutions;

    fn is_assigned(&self, i: Variable) -> bool {
        self[i as usize].is_assigned()
    }

    fn var_value(&self, i: Variable) -> Option<bool> {
        self[i as usize].into()
    }

    fn all_assigned(&self) -> bool;

    fn literal_value(&self, l: impl Literal) -> Option<bool> {
        self.var_value(l.variable()).map(|b| b ^ l.is_negated())
    }
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
pub struct Solutions(Vec<i32>);

impl Index<usize> for Solutions {
    type Output = i32;

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
    #[must_use]
    pub fn new(s: &[i32]) -> Self {
        Self(s.iter().filter(|i| **i != 0).copied().collect())
    }

    pub fn iter(&self) -> impl Iterator<Item = &i32> {
        self.0.iter()
    }
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut i32> {
        self.0.iter_mut()
    }

    #[must_use]
    pub fn check(&self, i: i32) -> bool {
        self.0.contains(&i)
    }

    #[must_use]
    pub const fn empty() -> Self {
        Self(Vec::new())
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[must_use]
    pub fn contains(&self, i: i32) -> bool {
        self.0.contains(&i)
    }
}

impl Assignment for VecAssignment {
    fn new(n: usize) -> Self {
        Self(vec![VarState::Unassigned; n])
    }

    fn set(&mut self, var: Variable, b: bool) {
        self[var as usize] = VarState::Assigned(b);
    }

    fn unassign(&mut self, i: Variable) {
        self[i as usize] = VarState::Unassigned;
    }

    fn get_solutions(&self) -> Solutions {
        Solutions::new(
            &self
                .0
                .iter()
                .enumerate()
                .filter_map(|(i, s)| {
                    let i = i32::try_from(i).ok()?;
                    match s {
                        VarState::Assigned(true) => Some(i),
                        VarState::Assigned(false) => Some(-i),
                        _ => None,
                    }
                })
                .collect::<Vec<_>>(),
        )
    }

    fn all_assigned(&self) -> bool {
        self.0.iter().all(|s| s.is_assigned())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct HashMapAssignment {
    map: HashMap<Variable, VarState>,
    num_vars: usize,
}

impl Index<usize> for HashMapAssignment {
    type Output = VarState;

    fn index(&self, index: usize) -> &Self::Output {
        let index = Variable::try_from(index).expect("Index overflow");
        self.map.get(&index).unwrap_or(&VarState::Unassigned)
    }
}

impl IndexMut<usize> for HashMapAssignment {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let index = Variable::try_from(index).expect("Index overflow");
        self.map.entry(index).or_insert(VarState::Unassigned)
    }
}

impl Assignment for HashMapAssignment {
    fn new(num_vars: usize) -> Self {
        Self {
            map: HashMap::default(),
            num_vars,
        }
    }

    fn set(&mut self, var: Variable, b: bool) {
        self.map.insert(var, VarState::Assigned(b));
    }

    fn unassign(&mut self, i: Variable) {
        self.map.remove(&i);
    }

    fn get_solutions(&self) -> Solutions {
        Solutions::new(
            &self
                .map
                .iter()
                .filter_map(|(i, s)| {
                    let i = i32::try_from(*i).ok()?;

                    match s {
                        VarState::Assigned(true) => Some(i),
                        VarState::Assigned(false) => Some(-i),
                        _ => None,
                    }
                })
                .collect::<Vec<_>>(),
        )
    }

    fn is_assigned(&self, i: Variable) -> bool {
        self.map.contains_key(&i)
    }

    fn all_assigned(&self) -> bool {
        self.map.len() == self.num_vars && self.map.values().all(|s| s.is_assigned())
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

        assert_eq!(a.literal_value(PackedLiteral::new(1, false)), Some(false));
        assert_eq!(a.literal_value(PackedLiteral::new(2, true)), Some(false));
        assert_eq!(a.literal_value(PackedLiteral::new(3, false)), Some(false));

        a.unassign(1);
        assert!(!a.is_assigned(1));
        assert_eq!(a.var_value(1), None);

        let s = a.get_solutions();

        assert_eq!(s, Solutions::new(&[3]));
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

        assert_eq!(a.literal_value(PackedLiteral::new(1, false)), Some(false));
        assert_eq!(a.literal_value(PackedLiteral::new(2, true)), Some(false));
        assert_eq!(a.literal_value(PackedLiteral::new(3, false)), Some(false));

        a.unassign(1);
        assert!(!a.is_assigned(1));
        assert_eq!(a.var_value(1), None);

        let s = a.get_solutions();

        assert_eq!(s, Solutions::new(&[3]));
    }

    #[test]
    fn test_assignment_unassigned() {
        let a = VecAssignment::new(3);
        assert!(!a.is_assigned(1));
        assert!(!a.is_assigned(2));
        assert!(!a.is_assigned(3));
    }
}
