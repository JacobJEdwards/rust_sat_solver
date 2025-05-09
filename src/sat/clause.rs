#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
use crate::sat::clause_storage::LiteralStorage;
use crate::sat::literal::{Literal, PackedLiteral};
use crate::sat::trail::Trail;
use bit_vec::BitVec;
use core::ops::{Index, IndexMut};
use itertools::Itertools;
use ordered_float::OrderedFloat;
use smallvec::SmallVec;
use std::collections::HashSet;
use std::hash::Hash;
use std::marker::PhantomData;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Clause<L: Literal = PackedLiteral, S: LiteralStorage<L> = SmallVec<[L; 8]>> {
    pub literals: S,
    pub lbd: u32,
    pub deleted: bool,
    pub is_learnt: bool,
    pub activity: OrderedFloat<f64>,
    data: PhantomData<*const L>,
}

impl<L: Literal, S: LiteralStorage<L>> AsRef<[L]> for Clause<L, S> {
    fn as_ref(&self) -> &[L] {
        self.literals.as_ref()
    }
}

impl<L: Literal, S: LiteralStorage<L>> FromIterator<L> for Clause<L, S> {
    fn from_iter<I: IntoIterator<Item = L>>(iter: I) -> Self {
        Self {
            literals: iter.into_iter().collect(),
            lbd: 0,
            deleted: false,
            is_learnt: false,
            activity: OrderedFloat::from(0.0),
            data: PhantomData,
        }
    }
}

impl<L: Literal + Hash + Eq, S: LiteralStorage<L>> Clause<L, S> {
    #[must_use]
    pub fn new(literals: &[L]) -> Self {
        let literals = literals.iter().unique().copied().collect();

        Self {
            literals,
            lbd: 0,
            deleted: false,
            is_learnt: false,
            activity: OrderedFloat::from(0.0),
            data: PhantomData,
        }
    }

    #[must_use]
    pub fn resolve(&self, other: &Self, pivot: L) -> Self {
        if !self.literals.iter().contains(&pivot)
            || !other.literals.iter().contains(&pivot.negated())
        {
            return self.clone();
        }

        let mut resolved_literals: HashSet<L> = HashSet::new();

        for &lit in self.literals.iter() {
            if lit != pivot {
                resolved_literals.insert(lit);
            }
        }
        for &lit in other.literals.iter() {
            if lit != pivot.negated() {
                resolved_literals.insert(lit);
            }
        }

        let resolved_clause = Self::new(resolved_literals.into_iter().collect_vec().as_ref());

        if resolved_clause.is_tautology() {
            Self::default()
        } else {
            resolved_clause
        }
    }

    #[must_use]
    pub fn resolve_binary(&self, binary: &Self) -> Option<Self> {
        if binary.len() != 2 {
            return None;
        }

        let bin_lit1 = binary.literals[0];
        let bin_lit2 = binary.literals[1];

        for &lit in self.literals.iter() {
            if lit == bin_lit1.negated() {
                let mut new_clause = self.clone();
                new_clause.remove_literal(
                    new_clause
                        .literals
                        .iter()
                        .position(|&x| x == lit)
                        .unwrap_or_else(|| new_clause.literals.len() - 1),
                );
                new_clause.push(bin_lit2);

                if new_clause.is_tautology() {
                    return None;
                }

                return Some(new_clause);
            } else if lit == bin_lit2.negated() {
                let mut new_clause = self.clone();
                new_clause.remove_literal(
                    new_clause
                        .literals
                        .iter()
                        .position(|&x| x == lit)
                        .unwrap_or_else(|| new_clause.literals.len() - 1),
                );
                new_clause.push(bin_lit1);

                if new_clause.is_tautology() {
                    return None;
                }

                return Some(new_clause);
            }
        }

        None
    }

    pub fn push(&mut self, literal: L) {
        if !self.literals.iter().contains(&literal) {
            self.literals.push(literal);
        }
    }

    #[must_use]
    pub fn is_tautology(&self) -> bool {
        let mut set = HashSet::new();

        for lit in self.literals.iter() {
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

    pub fn iter(&self) -> impl Iterator<Item = &L> {
        self.literals.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut L> {
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
        self.literals.is_empty()
    }

    #[must_use]
    pub const fn is_deleted(&self) -> bool {
        self.deleted
    }

    pub fn delete(&mut self) {
        self.deleted = true;
    }

    pub fn remove_literal(&mut self, idx: usize) {
        self.literals.swap_remove(idx);
    }

    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    pub fn calculate_lbd(&mut self, trail: &Trail<L, S>) {
        let max_level_in_clause = self
            .literals
            .iter()
            .map(|lit| trail.level(lit.variable()))
            .max()
            .unwrap_or(0);

        let mut levels_seen = BitVec::from_elem(max_level_in_clause.wrapping_add(1), false);
        let mut count = 0u32;

        for &lit in self.literals.iter() {
            let level = trail.level(lit.variable());
            if level > 0 && !levels_seen[level] {
                levels_seen.set(level, true);
                count = count.wrapping_add(1);
            }
        }

        if count == 0
            && !self.is_empty()
            && self.literals.iter().any(|l| trail.level(l.variable()) == 0)
        {
            self.lbd = 1;
        } else {
            self.lbd = count;
        }

        if self.is_learnt && !self.is_empty() && self.lbd == 0 {
            self.lbd = 1;
        }
    }

    pub fn convert<T: Literal, U: LiteralStorage<T>>(&self) -> Clause<T, U> {
        let literals = self
            .literals
            .iter()
            .map(|lit| T::new(lit.variable(), lit.polarity()))
            .collect_vec();

        Clause::new(&literals)
    }

    pub fn bump_activity(&mut self, increment: f64) {
        self.activity += increment;
    }

    pub fn decay_activity(&mut self, factor: f64) {
        self.activity *= factor;
    }

    pub const fn activity(&self) -> f64 {
        self.activity.0
    }
}

impl<T: Literal, S: LiteralStorage<T>> Index<usize> for Clause<T, S> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.literals.get_unchecked(index) }
    }
}

impl<T: Literal, S: LiteralStorage<T>> IndexMut<usize> for Clause<T, S> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { self.literals.get_unchecked_mut(index) }
    }
}

impl<T: Literal, S: LiteralStorage<T>> From<&Clause<T, S>> for Vec<T> {
    fn from(clause: &Clause<T, S>) -> Self {
        clause.literals.iter().copied().collect_vec()
    }
}

impl<T: Literal + Eq + Hash, S: LiteralStorage<T>> From<Vec<i32>> for Clause<T, S> {
    fn from(literals: Vec<i32>) -> Self {
        let literals = literals
            .iter()
            .map(|l| {
                let pol = l.is_positive();
                let var = l.unsigned_abs();

                T::new(var, pol)
            })
            .collect_vec();
        Self::new(&literals)
    }
}

impl<L: Literal, S: LiteralStorage<L>> From<Vec<L>> for Clause<L, S> {
    fn from(literals: Vec<L>) -> Self {
        Self {
            literals: S::from(literals),
            lbd: 0,
            deleted: false,
            is_learnt: false,
            activity: OrderedFloat::from(0.0),
            data: PhantomData,
        }
    }
}

impl<L: Literal, S: LiteralStorage<L>> From<&Vec<L>> for Clause<L, S> {
    fn from(literals: &Vec<L>) -> Self {
        Self {
            literals: S::from(literals.clone()),
            lbd: 0,
            deleted: false,
            is_learnt: false,
            activity: OrderedFloat::from(0.0),
            data: PhantomData,
        }
    }
}

impl<L: Literal, S: LiteralStorage<L>> FromIterator<i32> for Clause<L, S> {
    fn from_iter<I: IntoIterator<Item = i32>>(iter: I) -> Self {
        let literals = iter
            .into_iter()
            .map(|l| {
                let pol = l.is_positive();
                let var = l.unsigned_abs();

                L::new(var, pol)
            })
            .collect_vec();

        Self::new(&literals)
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
    fn test_swap() {
        let mut clause: Clause = Clause::from(vec![1, 2, 3]);
        clause.swap(0, 2);
    }
}
