#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
//! Defines how literals are stored within a clause.
//!
//! This module introduces the `LiteralStorage` trait, which abstracts the underlying
//! data structure used to store a collection of literals (e.g. `Vec<L>` or
//! `SmallVec<[L; N]>`). This allows clauses to be generic over their literal
//! storage mechanism, enabling optimisations like `SmallVec` for small clauses
//! while still supporting heap-allocated `Vec` for larger ones.
//!
//! The trait provides a common interface for operations like adding, removing,
//! accessing, and iterating over literals.

use crate::sat::literal; // For the `convert` function in the module's `convert` function
use crate::sat::literal::Literal;
use clap::ValueEnum;
use smallvec::SmallVec;
use std::fmt::{Debug, Display};
use std::ops::{Index, IndexMut};
use std::slice::{Iter, IterMut};

/// A trait abstracting the storage of literals within a clause.
///
/// This trait defines a common interface for collections that can store literals,
/// such as `Vec<L>` or `SmallVec<[L; N]>`. It ensures that clauses can interact
/// with their literal storage in a generic way.
///
/// # Type Parameters
///
/// * `L`: The type of `Literal` being stored.
///
/// # Required Super traits
///
/// Implementors must also implement several standard traits to ensure broad compatibility:
/// - `Index<usize, Output = L>`: For direct read access by index.
/// - `IndexMut<usize, Output = L>`: For direct mutable access by index.
/// - `FromIterator<L>`: To construct the storage from an iterator of literals.
/// - `Clone`: To clone the storage.
/// - `From<Vec<L>>`: To construct the storage from a `Vec<L>`.
/// - `Default`: To create a default (usually empty) instance of the storage.
/// - `Extend<L>`: To add multiple literals from an iterator.
/// - `Debug`: For debugging purposes.
/// - `AsRef<[L]>`: To get a slice view of the stored literals.
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
    /// Appends a literal to the end of the storage.
    ///
    /// # Arguments
    ///
    /// * `literal`: The literal to add.
    fn push(&mut self, literal: L);

    /// Returns the number of literals in the storage.
    fn len(&self) -> usize;

    /// Returns `true` if the storage contains no literals.
    fn is_empty(&self) -> bool;

    /// Returns an iterator over the literals in the storage.
    fn iter(&self) -> Iter<L>;

    /// Returns a mutable iterator over the literals in the storage.
    fn iter_mut(&mut self) -> IterMut<L>;

    /// Removes and returns the literal at `index`, shifting all elements after it to the left.
    ///
    /// # Arguments
    ///
    /// * `index`: The index of the literal to remove.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    fn remove(&mut self, index: usize) -> L;

    /// Removes all literals from the storage.
    fn clear(&mut self);

    /// Swaps the literals at indices `a` and `b`.
    ///
    /// # Arguments
    ///
    /// * `a`: The index of the first literal.
    /// * `b`: The index of the second literal.
    ///
    /// # Panics
    ///
    /// Panics if `a` or `b` are out of bounds.
    fn swap(&mut self, a: usize, b: usize);

    /// Returns a reference to the literal at `index` without bounds checking.
    ///
    /// # Arguments
    ///
    /// * `index`: The index of the literal to access.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds `index` is undefined behavior.
    unsafe fn get_unchecked(&self, index: usize) -> &L;

    /// Returns a mutable reference to the literal at `index` without bounds checking.
    ///
    /// # Arguments
    ///
    /// * `index`: The index of the literal to access.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds `index` is undefined behavior.
    unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut L;

    /// Removes the literal at `index` by swapping it with the last literal and then popping.
    ///
    /// This is generally faster than `remove` because it does not require shifting elements,
    /// but it changes the order of literals in the storage.
    ///
    /// # Arguments
    ///
    /// * `index`: The index of the literal to remove.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    fn swap_remove(&mut self, index: usize) -> L {
        let last_idx = self.len().saturating_sub(1);
        self.swap(index, last_idx);
        self.remove(last_idx)
    }
}

/// Implementation of `LiteralStorage` for `Vec<L>`.
///
/// This allows `Vec<L>` to be used as a concrete storage type for literals in clauses.
/// Most methods delegate directly to the corresponding `Vec` methods.
impl<L: Literal> LiteralStorage<L> for Vec<L> {
    fn push(&mut self, literal: L) {
        Self::push(self, literal);
    }

    fn len(&self) -> usize {
        Self::len(self)
    }

    fn is_empty(&self) -> bool {
        Self::is_empty(self)
    }

    fn iter(&self) -> Iter<L> {
        self.as_slice().iter()
    }

    fn iter_mut(&mut self) -> IterMut<L> {
        self.as_mut_slice().iter_mut()
    }

    fn remove(&mut self, index: usize) -> L {
        Self::remove(self, index)
    }

    fn clear(&mut self) {
        Self::clear(self);
    }

    fn swap(&mut self, a: usize, b: usize) {
        self.as_mut_slice().swap(a, b);
    }

    unsafe fn get_unchecked(&self, index: usize) -> &L {
        unsafe { self.as_slice().get_unchecked(index) }
    }

    unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut L {
        unsafe { self.as_mut_slice().get_unchecked_mut(index) }
    }

    fn swap_remove(&mut self, index: usize) -> L {
        Self::swap_remove(self, index)
    }
}

/// Implementation of `LiteralStorage` for `SmallVec<[L; N]>`.
///
/// `SmallVec` is a vector-like collection that stores a small number (`N`) of elements
/// on the stack and spills to the heap if more elements are added. This can be an
/// optimisation for clauses, as many clauses are small.
///
/// # Type Parameters
///
/// * `L`: The type of `Literal` being stored.
/// * `N`: A compile-time constant specifying the stack capacity of the `SmallVec`.
impl<L: Literal, const N: usize> LiteralStorage<L> for SmallVec<[L; N]> {
    fn push(&mut self, literal: L) {
        Self::push(self, literal);
    }

    fn len(&self) -> usize {
        Self::len(self)
    }

    fn is_empty(&self) -> bool {
        Self::is_empty(self)
    }

    fn iter(&self) -> Iter<L> {
        self.as_slice().iter()
    }

    fn iter_mut(&mut self) -> IterMut<L> {
        self.as_mut_slice().iter_mut()
    }

    fn remove(&mut self, index: usize) -> L {
        Self::remove(self, index)
    }

    fn clear(&mut self) {
        Self::clear(self);
    }

    fn swap(&mut self, a: usize, b: usize) {
        self.as_mut_slice().swap(a, b);
    }

    unsafe fn get_unchecked(&self, index: usize) -> &L {
        unsafe { self.as_slice().get_unchecked(index) }
    }

    unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut L {
        unsafe { self.as_mut_slice().get_unchecked_mut(index) }
    }

    fn swap_remove(&mut self, index: usize) -> L {
        Self::swap_remove(self, index)
    }
}

/// Converts a collection of literals of one type (`L`) to a `Vec` of literals of another type (`U`).
///
/// This function iterates over the input `literals` (which must implement `LiteralStorage<L>`),
/// converts each literal from type `L` to type `U` using `crate::sat::literal::convert`,
/// and collects the results into a new `Vec<U>`.
///
/// # Type Parameters
///
/// * `L`: The source `Literal` type.
/// * `U`: The target `Literal` type.
/// * `S`: The `LiteralStorage` type for the target literals `U` (unused in this specific signature, but implies context).
/// * `T`: The `LiteralStorage` type for the source literals `L`.
///
/// # Arguments
///
/// * `literals`: A reference to a `LiteralStorage<L>` containing the literals to convert.
///
/// # Returns
///
/// A `Vec<U>` containing the converted literals.
#[allow(dead_code)]
pub fn convert<L: Literal, U: Literal, S: LiteralStorage<U>, T: LiteralStorage<L>>(
    literals: &T,
) -> Vec<U> {
    literals.iter().map(literal::convert::<L, U>).collect()
}

/// Enum representing the storage implementation for literals in a clause.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LiteralStorageImpls<L: Literal, const N: usize> {
    /// Uses a standard `Vec` to store literals.
    VecStorage(Vec<L>),
    /// Uses a `SmallVec` to store literals, optimised for small collections.
    SmallVecStorage(SmallVec<[L; N]>),
}

impl<L: Literal, const N: usize> Index<usize> for LiteralStorageImpls<L, N> {
    type Output = L;

    fn index(&self, index: usize) -> &Self::Output {
        match self {
            Self::VecStorage(vec) => &vec[index],
            Self::SmallVecStorage(small_vec) => &small_vec[index],
        }
    }
}

impl<L: Literal, const N: usize> IndexMut<usize> for LiteralStorageImpls<L, N> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        match self {
            Self::VecStorage(vec) => &mut vec[index],
            Self::SmallVecStorage(small_vec) => &mut small_vec[index],
        }
    }
}

impl<L: Literal, const N: usize> FromIterator<L> for LiteralStorageImpls<L, N> {
    fn from_iter<T: IntoIterator<Item = L>>(iter: T) -> Self {
        let mut vec = Vec::new();
        for item in iter {
            vec.push(item);
        }
        if vec.len() <= N {
            Self::SmallVecStorage(SmallVec::from(vec))
        } else {
            Self::VecStorage(vec)
        }
    }
}

impl<L: Literal, const N: usize> From<Vec<L>> for LiteralStorageImpls<L, N> {
    fn from(value: Vec<L>) -> Self {
        if value.len() <= N {
            Self::SmallVecStorage(SmallVec::from(value))
        } else {
            Self::VecStorage(value)
        }
    }
}

impl<L: Literal, const N: usize> Extend<L> for LiteralStorageImpls<L, N> {
    fn extend<T: IntoIterator<Item = L>>(&mut self, iter: T) {
        match self {
            Self::VecStorage(vec) => vec.extend(iter),
            Self::SmallVecStorage(small_vec) => small_vec.extend(iter),
        }
    }
}

impl<L: Literal, const N: usize> AsRef<[L]> for LiteralStorageImpls<L, N> {
    fn as_ref(&self) -> &[L] {
        match self {
            Self::VecStorage(vec) => vec.as_ref(),
            Self::SmallVecStorage(small_vec) => small_vec.as_ref(),
        }
    }
}

impl<L: Literal, const N: usize> Default for LiteralStorageImpls<L, N> {
    fn default() -> Self {
        Self::VecStorage(Vec::default())
    }
}

impl<L: Literal, const N: usize> LiteralStorage<L> for LiteralStorageImpls<L, N> {
    fn push(&mut self, literal: L) {
        match self {
            Self::VecStorage(vec) => vec.push(literal),
            Self::SmallVecStorage(small_vec) => small_vec.push(literal),
        }
    }

    fn len(&self) -> usize {
        match self {
            Self::VecStorage(vec) => vec.len(),
            Self::SmallVecStorage(small_vec) => small_vec.len(),
        }
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn iter(&self) -> Iter<L> {
        match self {
            Self::VecStorage(vec) => vec.iter(),
            Self::SmallVecStorage(small_vec) => small_vec.iter(),
        }
    }

    fn iter_mut(&mut self) -> IterMut<L> {
        match self {
            Self::VecStorage(vec) => vec.iter_mut(),
            Self::SmallVecStorage(small_vec) => small_vec.iter_mut(),
        }
    }

    fn remove(&mut self, index: usize) -> L {
        match self {
            Self::VecStorage(vec) => vec.remove(index),
            Self::SmallVecStorage(small_vec) => small_vec.remove(index),
        }
    }

    fn clear(&mut self) {
        match self {
            Self::VecStorage(vec) => vec.clear(),
            Self::SmallVecStorage(small_vec) => small_vec.clear(),
        }
    }

    fn swap(&mut self, a: usize, b: usize) {
        match self {
            Self::VecStorage(vec) => vec.swap(a, b),
            Self::SmallVecStorage(small_vec) => small_vec.swap(a, b),
        }
    }

    unsafe fn get_unchecked(&self, index: usize) -> &L {
        match self {
            Self::VecStorage(vec) => unsafe { vec.get_unchecked(index) },
            Self::SmallVecStorage(small_vec) => unsafe { small_vec.get_unchecked(index) },
        }
    }

    unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut L {
        match self {
            Self::VecStorage(vec) => unsafe { vec.get_unchecked_mut(index) },
            Self::SmallVecStorage(small_vec) => unsafe { small_vec.get_unchecked_mut(index) },
        }
    }

    fn swap_remove(&mut self, index: usize) -> L {
        match self {
            Self::VecStorage(vec) => vec.swap_remove(index),
            Self::SmallVecStorage(small_vec) => small_vec.swap_remove(index),
        }
    }
}

/// Enum representing the storage type for literals in a clause.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Copy, Default, ValueEnum)]
pub enum LiteralStorageType {
    /// Uses a standard `Vec` to store literals.
    Vec,
    /// Uses a `SmallVec` to store literals, optimised for small collections.
    #[default]
    SmallVec,
}

impl Display for LiteralStorageType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Vec => write!(f, "vec"),
            Self::SmallVec => write!(f, "small-vec"),
        }
    }
}

impl LiteralStorageType {
    /// Returns the name of the storage type as a string.
    #[allow(dead_code)]
    #[must_use]
    pub fn to_impl<L: Literal, const N: usize>(self) -> LiteralStorageImpls<L, N> {
        match self {
            Self::Vec => LiteralStorageImpls::VecStorage(Vec::new()),
            Self::SmallVec => LiteralStorageImpls::SmallVecStorage(SmallVec::new()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::literal::{PackedLiteral, StructLiteral};

    #[allow(clippy::cognitive_complexity)]
    fn test_literal_storage_behavior<S: LiteralStorage<PackedLiteral>>(mut storage: S) {
        assert!(storage.is_empty());
        assert_eq!(storage.len(), 0);

        let lit1 = PackedLiteral::new(1u32, true);
        let lit2 = PackedLiteral::new(2u32, false);
        let lit3 = PackedLiteral::new(3u32, true);

        storage.push(lit1);
        assert!(!storage.is_empty());
        assert_eq!(storage.len(), 1);
        assert_eq!(storage[0], lit1);

        storage.push(lit2);
        assert_eq!(storage.len(), 2);
        assert_eq!(storage[1], lit2);

        let mut iter = storage.iter();
        assert_eq!(iter.next(), Some(&lit1));
        assert_eq!(iter.next(), Some(&lit2));
        assert_eq!(iter.next(), None);

        let removed_lit = storage.remove(0);
        assert_eq!(removed_lit, lit1);
        assert_eq!(storage.len(), 1);
        assert_eq!(storage[0], lit2);

        let new_literals = vec![lit1, lit3];
        storage.extend(new_literals);
        assert_eq!(storage.len(), 3);
        assert_eq!(storage[0], lit2);
        assert_eq!(storage[1], lit1);
        assert_eq!(storage[2], lit3);

        storage.swap(0, 2);
        assert_eq!(storage[0], lit3);
        assert_eq!(storage[2], lit2);

        let removed_by_swap = storage.swap_remove(0);
        assert_eq!(removed_by_swap, lit3);
        assert_eq!(storage.len(), 2);
        assert!(storage.iter().any(|&l| l == lit1));
        assert!(storage.iter().any(|&l| l == lit2));

        if !storage.is_empty() {
            unsafe {
                assert_eq!(*storage.get_unchecked(0), storage[0]);
            }
        }

        storage.clear();
        assert!(storage.is_empty());
        assert_eq!(storage.len(), 0);
    }

    #[test]
    fn test_vec_literal_storage() {
        let vec_storage: Vec<PackedLiteral> = Vec::new();
        test_literal_storage_behavior(vec_storage);
    }

    #[test]
    fn test_smallvec_literal_storage_stack() {
        let small_vec_storage: SmallVec<[PackedLiteral; 3]> = SmallVec::new();
        test_literal_storage_behavior(small_vec_storage);
    }

    #[test]
    fn test_smallvec_literal_storage_heap() {
        let small_vec_storage: SmallVec<[PackedLiteral; 1]> = SmallVec::new();
        test_literal_storage_behavior(small_vec_storage);
    }

    #[test]
    fn test_from_vec_and_from_iterator() {
        let literals = vec![
            PackedLiteral::new(1u32, true),
            PackedLiteral::new(2u32, false),
        ];

        let storage_vec_from_vec = literals.clone();
        assert_eq!(storage_vec_from_vec.len(), 2);

        let storage_vec_from_iter = literals.clone().into_iter();
        assert_eq!(storage_vec_from_iter.len(), 2);

        let storage_smallvec_from_vec: SmallVec<[PackedLiteral; 3]> =
            SmallVec::from(literals.clone());
        assert_eq!(storage_smallvec_from_vec.len(), 2);

        let storage_smallvec_from_iter: SmallVec<[PackedLiteral; 3]> =
            literals.into_iter().collect();
        assert_eq!(storage_smallvec_from_iter.len(), 2);
    }

    #[test]
    fn test_module_convert_function() {
        type TargetStorage = Vec<StructLiteral>;

        let source_literals_vec: Vec<PackedLiteral> = vec![
            PackedLiteral::new(1u32, true),
            PackedLiteral::new(2u32, false),
        ];

        let converted_literals: Vec<StructLiteral> =
            convert::<PackedLiteral, StructLiteral, TargetStorage, _>(&source_literals_vec);

        assert_eq!(converted_literals.len(), 2);
        assert_eq!(converted_literals[0].variable(), 1u32);
        assert!(converted_literals[0].polarity());
        assert_eq!(converted_literals[1].variable(), 2u32);
        assert!(!converted_literals[1].polarity());
    }
}
