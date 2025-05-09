use crate::sat::literal;
use crate::sat::literal::Literal;
use smallvec::SmallVec;
use std::fmt::Debug;
use std::ops::{Index, IndexMut};
use std::slice::{Iter, IterMut};

pub trait LiteralStorage<L: Literal>:
    Index<usize, Output = L>
    + FromIterator<L>
    + Clone
    + From<Vec<L>>
    + Default
    + IndexMut<usize, Output = L>
    + Extend<L>
    + Debug
    + AsRef<[L]>
{
    fn push(&mut self, literal: L);
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn iter(&self) -> Iter<L>;
    fn iter_mut(&mut self) -> IterMut<L>;
    fn remove(&mut self, index: usize) -> L;
    fn clear(&mut self);
    fn swap(&mut self, a: usize, b: usize);
    unsafe fn get_unchecked(&self, index: usize) -> &L;
    unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut L;
    fn swap_remove(&mut self, index: usize) -> L {
        let last = self.len() - 1;
        self.swap(index, last);
        self.remove(last)
    }
}

impl<L: Literal> LiteralStorage<L> for Vec<L> {
    fn push(&mut self, literal: L) {
        self.push(literal);
    }

    fn len(&self) -> usize {
        self.len()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    fn iter(&self) -> Iter<L> {
        self.as_slice().iter()
    }

    fn iter_mut(&mut self) -> IterMut<L> {
        self.as_mut_slice().iter_mut()
    }

    fn remove(&mut self, index: usize) -> L {
        self.remove(index)
    }

    fn clear(&mut self) {
        self.clear();
    }

    fn swap(&mut self, a: usize, b: usize) {
        self.as_mut_slice().swap(a, b);
    }

    unsafe fn get_unchecked(&self, index: usize) -> &L {
        self.as_slice().get_unchecked(index)
    }

    unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut L {
        self.as_mut_slice().get_unchecked_mut(index)
    }

    fn swap_remove(&mut self, index: usize) -> L {
        self.swap_remove(index)
    }
}

impl<L: Literal, const N: usize> LiteralStorage<L> for SmallVec<[L; N]> {
    fn push(&mut self, literal: L) {
        self.push(literal);
    }

    fn len(&self) -> usize {
        self.len()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    fn iter(&self) -> Iter<L> {
        self.as_slice().iter()
    }

    fn iter_mut(&mut self) -> IterMut<L> {
        self.as_mut_slice().iter_mut()
    }

    fn remove(&mut self, index: usize) -> L {
        self.remove(index)
    }

    fn clear(&mut self) {
        self.clear();
    }

    fn swap(&mut self, a: usize, b: usize) {
        self.as_mut_slice().swap(a, b);
    }

    unsafe fn get_unchecked(&self, index: usize) -> &L {
        self.as_slice().get_unchecked(index)
    }

    unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut L {
        self.as_mut_slice().get_unchecked_mut(index)
    }

    fn swap_remove(&mut self, index: usize) -> L {
        self.swap_remove(index)
    }
}

pub fn convert<L: Literal, U: Literal, S: LiteralStorage<U>, T: LiteralStorage<L>>(
    literals: &T,
) -> Vec<U> {
    literals.iter().map(literal::convert::<L, U>).collect()
}
