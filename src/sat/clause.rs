#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
// Hiding unsafety warnings for `get_unchecked` as it's an intentional optimization
// with preconditions managed by the logic.
// Allowing specific casts that are understood within the context of SAT solver logic.
#![allow(unsafe_code, clippy::cast_possible_truncation, clippy::cast_sign_loss)]

//! Contains details of a clause, a fundamental component in SAT solvers.
//!
//! A clause is a disjunction of literals (e.g., `x1 OR !x2 OR x3`).
//! This module defines the `Clause` struct, which stores literals and associated metadata
//! relevant for Conflict-Driven Clause Learning (CDCL) SAT solvers, such as
//! Literal Blocks Distance (LBD) and activity scores for clause deletion strategies.

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

/// Represents a clause in a SAT formula.
///
/// A clause is a set of literals, typically interpreted as a disjunction.
/// For example, the clause `{L1, L2, L3}` represents `L1 OR L2 OR L3`.
///
/// # Type Parameters
///
/// * `L`: The type of literal stored in the clause. Defaults to `PackedLiteral`.
///   Must implement the `Literal` trait.
/// * `S`: The storage type for the literals. Defaults to `SmallVec<[L; 8]>`.
///   Must implement the `LiteralStorage<L>` trait, providing efficient storage for literals.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Clause<L: Literal = PackedLiteral, S: LiteralStorage<L> = SmallVec<[L; 8]>> {
    /// The collection of literals forming the clause.
    /// The specific storage (e.g., `Vec`, `SmallVec`) is determined by the `S` type parameter.
    pub literals: S,
    /// Literal Blocks Distance (LBD) of the clause.
    /// LBD is a measure of the "locality" of a learnt clause in terms of decision levels.
    /// Lower LBD often indicates higher quality learnt clauses. Calculated for learnt clauses.
    pub lbd: u32,
    /// Flag indicating if the clause has been marked for deletion.
    /// Deleted clauses are typically removed by the solver during database cleaning.
    pub deleted: bool,
    /// Flag indicating if the clause was learnt during conflict analysis.
    /// Original clauses (from the input problem) are not marked as learnt.
    pub is_learnt: bool,
    /// Activity score of the clause, used in clause deletion heuristics (e.g., VSIDS-like).
    /// Higher activity suggests the clause has been more recently involved in conflicts or propagations.
    pub activity: OrderedFloat<f64>,
    /// `PhantomData` to ensure proper variance and handling of the generic type `L`.
    /// `*const L` suggests covariance over `L`, meaning `Clause<LSub, S>` could be
    /// treated as `Clause<LSuper, S>` if `LSub` is a subtype of `LSuper`, though this
    /// concept is less direct in Rust without trait object subtyping.
    /// It mainly helps the compiler with type checking for `L`.
    data: PhantomData<*const L>,
}

impl<L: Literal, S: LiteralStorage<L>> AsRef<[L]> for Clause<L, S> {
    /// Returns a slice containing the literals in the clause.
    /// This allows the clause to be treated as a slice for read-only operations.
    fn as_ref(&self) -> &[L] {
        self.literals.as_ref()
    }
}

impl<L: Literal, S: LiteralStorage<L>> FromIterator<L> for Clause<L, S> {
    /// Creates a new clause from an iterator of literals.
    ///
    /// The literals from the iterator are collected into the `literals` field.
    /// Other fields (`lbd`, `deleted`, `is_learnt`, `activity`) are initialized to default values.
    fn from_iter<I: IntoIterator<Item = L>>(iter: I) -> Self {
        Self {
            literals: iter.into_iter().unique().collect(),
            lbd: 0,
            deleted: false,
            is_learnt: false,
            activity: OrderedFloat::from(0.0),
            data: PhantomData,
        }
    }
}

impl<L: Literal + Hash + Eq, S: LiteralStorage<L>> Clause<L, S> {
    /// Creates a new clause from a slice of literals.
    ///
    /// Literals are deduplicated during creation using `itertools::Itertools::unique`.
    /// For example, `[L1, L1, L2]` becomes `{L1, L2}`.
    /// The clause is initialized as not learnt, not deleted, with LBD 0 and activity 0.0.
    /// This method does not check for tautologies automatically upon creation.
    ///
    /// # Arguments
    ///
    /// * `literals_slice`: A slice of literals to form the clause.
    #[must_use]
    pub fn new(literals_slice: &[L]) -> Self {
        literals_slice.iter().copied().collect()
    }

    /// Performs resolution between this clause and another clause on a pivot literal.
    ///
    /// The resolution rule is: `(A V x) AND (B V !x) => (A V B)`.
    /// In this context, `self` represents `(A V x)` and `other` represents `(B V !x)`.
    /// The `pivot` argument is the literal `x`.
    ///
    /// - If `pivot` (i.e. `x`) is not found in `self.literals`, or `pivot.negated()` (i.e. `!x`)
    ///   is not found in `other.literals`, resolution is not applicable with the given pivot.
    ///   In this case, a clone of `self` is returned.
    /// - The resolvent clause is formed by taking the union of literals from `self` (excluding `pivot`)
    ///   and `other` (excluding `pivot.negated()`), with duplicates removed.
    /// - If the resulting resolvent is a tautology (e.g., contains both `y` and `!y`),
    ///   a default (typically empty and non-learnt) clause is returned. A tautological resolvent
    ///   is logically true and provides no new constraints.
    ///
    /// # Arguments
    ///
    /// * `other`: The other clause to resolve with.
    /// * `pivot`: The literal `x` to resolve upon. `self` should contain `pivot`, and
    ///   `other` should contain `pivot.negated()`.
    ///
    /// # Returns
    ///
    /// The resolved clause. This is a new `Clause` instance.
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

        let resolved_clause = resolved_literals.into_iter().collect::<Self>();

        if resolved_clause.is_tautology() {
            Self::default()
        } else {
            resolved_clause
        }
    }

    /// Performs binary resolution: resolves `self` with a binary clause `binary`.
    ///
    /// A binary clause contains exactly two literals. Let `binary` be `(L1 V L2)`.
    /// - If `self` contains `!L1`, the result is `(self - {!L1}) V {L2}`.
    /// - If `self` contains `!L2`, the result is `(self - {!L2}) V {L1}`.
    ///   The literals in the resulting clause are unique.
    ///   If the resulting clause is a tautology, `None` is returned.
    ///
    /// # Arguments
    ///
    /// * `binary`: A binary clause (must have exactly two literals).
    ///
    /// # Returns
    ///
    /// `Some(resolved_clause)` if resolution is possible and the result is not a tautology.
    /// `None` if `binary` is not a binary clause, resolution is not applicable (no matching negated literal found),
    /// or the result of resolution is a tautology.
    ///
    /// # Panics
    /// The `unwrap_or_else` for `position` might lead to unexpected behavior if the literal to be removed
    /// is not found (which shouldn't happen if `lit` was found in `self.literals` and `new_clause` is a clone).
    /// If `position` returns `None`, `remove_literal` would attempt to remove the last element of `new_clause.literals`.
    #[must_use]
    pub fn resolve_binary(&self, binary: &Self) -> Option<Self> {
        if binary.len() != 2 {
            return None;
        }

        let bin_lit1 = binary.literals[0];
        let bin_lit2 = binary.literals[1];

        for &lit_in_self in self.literals.iter() {
            if lit_in_self == bin_lit1.negated() {
                let mut new_clause = self.clone();
                let pos = new_clause
                    .literals
                    .iter()
                    .position(|&x| x == lit_in_self)
                    .unwrap_or_else(|| new_clause.literals.len().saturating_sub(1));
                if !new_clause.literals.is_empty() {
                    new_clause.remove_literal(pos);
                }
                new_clause.push(bin_lit2);

                return if new_clause.is_tautology() {
                    None
                } else {
                    Some(new_clause)
                };
            } else if lit_in_self == bin_lit2.negated() {
                let mut new_clause = self.clone();
                let pos = new_clause
                    .literals
                    .iter()
                    .position(|&x| x == lit_in_self)
                    .unwrap_or_else(|| new_clause.literals.len().saturating_sub(1));
                if !new_clause.literals.is_empty() {
                    new_clause.remove_literal(pos);
                }
                new_clause.push(bin_lit1);

                return if new_clause.is_tautology() {
                    None
                } else {
                    Some(new_clause)
                };
            }
        }

        None
    }

    /// Adds a literal to the clause, if it is not already present.
    ///
    /// # Arguments
    ///
    /// * `literal`: The literal to add.
    pub fn push(&mut self, literal: L) {
        if !self.literals.iter().contains(&literal) {
            self.literals.push(literal);
        }
    }

    /// Checks if the clause is a tautology.
    ///
    /// A clause is a tautology if it contains both a literal and its negation
    /// (e.g., `x OR !x`). Such clauses are always true and typically not useful
    /// in logical reasoning or SAT solving.
    ///
    /// # Returns
    ///
    /// `true` if the clause is a tautology, `false` otherwise.
    #[must_use]
    pub fn is_tautology(&self) -> bool {
        let mut set = HashSet::with_capacity(self.len());

        for lit_ref in self.literals.iter() {
            let lit = *lit_ref;
            if set.contains(&lit.negated()) {
                return true;
            }
            set.insert(lit);
        }
        false
    }

    /// Returns the number of literals in the clause.
    #[must_use]
    pub fn len(&self) -> usize {
        self.literals.len()
    }

    /// Returns an iterator over the literals in the clause.
    pub fn iter(&self) -> impl Iterator<Item = &L> {
        self.literals.iter()
    }

    /// Returns a mutable iterator over the literals in the clause.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut L> {
        self.literals.iter_mut()
    }

    /// Swaps two literals in the clause by their indices.
    ///
    /// This operation is often used in SAT solvers that employ watch lists,
    /// where watched literals are moved to specific positions (e.g., the first two)
    /// in the clause for efficient propagation.
    ///
    /// # Arguments
    ///
    /// * `i`: The index of the first literal.
    /// * `j`: The index of the second literal.
    ///
    /// # Panics
    ///
    /// Panics if `i` or `j` are out of bounds for `self.literals`.
    pub fn swap(&mut self, i: usize, j: usize) {
        self.literals.swap(i, j);
    }

    /// Checks if the clause is a unit clause.
    ///
    /// A unit clause is a clause with exactly one literal.
    /// Under a partial assignment, a clause can become unit if all but one of its literals
    /// are assigned false. Unit clauses are crucial for unit propagation in SAT solvers.
    ///
    /// # Returns
    ///
    /// `true` if the clause has exactly one literal, `false` otherwise.
    #[must_use]
    pub fn is_unit(&self) -> bool {
        self.len() == 1
    }

    /// Checks if the clause is empty.
    ///
    /// An empty clause (containing no literals) represents a contradiction (logical false).
    /// If an empty clause is derived during SAT solving, the formula is unsatisfiable.
    ///
    /// # Returns
    ///
    /// `true` if the clause has no literals, `false` otherwise.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }

    /// Checks if the clause is marked as deleted.
    #[must_use]
    pub const fn is_deleted(&self) -> bool {
        self.deleted
    }

    /// Marks the clause as deleted.
    ///
    /// This only sets the `deleted` flag to `true`. It does not remove the clause
    /// from any external storage (like a clause database). The actual removal is typically
    /// handled by a separate garbage collection or clause database cleaning process.
    pub const fn delete(&mut self) {
        self.deleted = true;
    }

    /// Removes a literal from the clause at the given index.
    ///
    /// This method uses `swap_remove` for efficiency, which means the order of
    /// the remaining literals in the clause may change (the last literal is swapped
    /// into the `idx` position, and then the length is reduced).
    ///
    /// # Arguments
    ///
    /// * `idx`: The index of the literal to remove.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is out of bounds for `self.literals`.
    pub fn remove_literal(&mut self, idx: usize) {
        self.literals.swap_remove(idx);
    }

    /// Calculates and updates the Literal Block Distance (LBD) of the clause.
    ///
    /// LBD is defined as the number of distinct decision levels (excluding level 0)
    /// of the variables in the clause's literals. This metric is used in CDCL solvers
    /// to estimate the "quality" or "usefulness" of learnt clauses, often guiding
    /// clause deletion strategies (clauses with lower LBD are generally preferred).
    ///
    /// Special LBD rules applied:
    /// - If the clause is empty, LBD is 0.
    /// - If all literals are at decision level 0 (or unassigned and treated as level 0),
    ///   and the clause is not empty, LBD is 1.
    /// - For learnt, non-empty clauses, LBD is ensured to be at least 1.
    ///
    /// # Arguments
    ///
    /// * `trail`: The solver's assignment trail, used to find the decision level
    ///   of each literal's variable.
    ///
    /// # Panics
    /// Behavior of `BitVec` indexing with `level` (a `u32`) depends on `usize` size.
    /// `clippy::cast_possible_truncation` lint is allowed for this module.
    pub fn calculate_lbd(&mut self, trail: &Trail<L, S>) {
        if self.is_empty() {
            self.lbd = 0;
            return;
        }

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
            if level > 0 {
                let level_idx = level;
                if !levels_seen.get(level_idx).unwrap_or(true) {
                    levels_seen.set(level_idx, true);
                    count = count.wrapping_add(1);
                }
            }
        }

        if count == 0 {
            self.lbd = if !self.is_empty()
                && self.literals.iter().any(|l| trail.level(l.variable()) == 0)
            {
                1
            } else {
                u32::from(!self.is_empty())
            };
        } else {
            self.lbd = count;
        }

        if self.is_learnt && !self.is_empty() && self.lbd == 0 {
            self.lbd = 1;
        }
    }

    /// Converts this clause into a clause with different literal or storage types.
    ///
    /// This is useful for interoperability if different parts of a solver
    /// use different representations (e.g., for specialized literal types or storage).
    /// The literals are converted one by one using `T::new(original_lit.variable(), original_lit.polarity())`.
    /// Metadata like LBD, deleted status, learnt status, and activity are copied.
    ///
    /// # Type Parameters
    ///
    /// * `T`: The target `Literal` type for the new clause.
    /// * `U`: The target `LiteralStorage<T>` type for the new clause.
    ///
    /// # Returns
    ///
    /// A new `Clause<T, U>` with equivalent literals and copied metadata.
    pub fn convert<T: Literal, U: LiteralStorage<T>>(&self) -> Clause<T, U> {
        let literals_as_t: Vec<T> = self
            .literals
            .iter()
            .map(|lit| T::new(lit.variable(), lit.polarity()))
            .collect_vec();

        let mut new_clause = Clause::<T, U>::new(&literals_as_t);
        new_clause.lbd = self.lbd;
        new_clause.deleted = self.deleted;
        new_clause.is_learnt = self.is_learnt;
        new_clause.activity = self.activity;
        new_clause
    }

    /// Increases the activity score of the clause by a specified increment.
    ///
    /// This is part of VSIDS-like (Variable State Independent Decaying Sum) heuristics,
    /// where clauses involved in recent conflict analysis get their activity "bumped",
    /// making them less likely to be deleted.
    ///
    /// # Arguments
    ///
    /// * `increment`: The positive amount to add to the clause's activity score.
    pub fn bump_activity(&mut self, increment: f64) {
        self.activity += increment;
    }

    /// Decays the activity score of the clause by a multiplicative factor.
    ///
    /// In VSIDS-like heuristics, all clause activities are periodically decayed.
    /// This gradually reduces the importance of clauses that have not been active recently.
    ///
    /// # Arguments
    ///
    /// * `factor`: The factor to multiply the activity score by (typically between 0 and 1).
    pub fn decay_activity(&mut self, factor: f64) {
        self.activity *= factor;
    }

    /// Returns the raw floating-point activity score of the clause.
    #[must_use]
    pub const fn activity(&self) -> f64 {
        self.activity.0
    }
}

impl<T: Literal, S: LiteralStorage<T>> Index<usize> for Clause<T, S> {
    type Output = T;

    /// Accesses the literal at the given `index` within the clause.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds for `self.literals`.
    ///
    /// # Safety
    ///
    /// This implementation uses `get_unchecked` for performance, based on the assumption
    /// that accesses are correctly bounded by the caller or internal logic (e.g., after a length check).
    /// Direct, unchecked indexing can lead to undefined behavior if `index` is invalid.
    fn index(&self, index: usize) -> &Self::Output {
        // Safety: Caller must ensure `index` is within bounds `[0, self.literals.len())`.
        unsafe { self.literals.get_unchecked(index) }
    }
}

impl<T: Literal, S: LiteralStorage<T>> IndexMut<usize> for Clause<T, S> {
    /// Mutably accesses the literal at the given `index` within the clause.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds for `self.literals`.
    ///
    /// # Safety
    ///
    /// This implementation uses `get_unchecked_mut` for performance.
    /// See `Index` implementation for safety notes regarding `get_unchecked`.
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        // Safety: Caller must ensure `index` is within bounds `[0, self.literals.len())`.
        unsafe { self.literals.get_unchecked_mut(index) }
    }
}

impl<T: Literal, S: LiteralStorage<T>> From<&Clause<T, S>> for Vec<T> {
    /// Converts a reference to a clause into a `Vec` of its literals.
    ///
    /// The literals are copied from the clause's internal storage into a new `Vec<T>`.
    /// `T` must be `Copy`.
    fn from(clause: &Clause<T, S>) -> Self {
        clause.literals.iter().copied().collect_vec()
    }
}

impl<T: Literal + Eq + Hash, S: LiteralStorage<T>> From<Vec<i32>> for Clause<T, S> {
    /// Creates a clause from a `Vec<i32>`, where integers represent literals
    /// in DIMACS format (e.g., `1` for variable 1 true, `-2` for variable 2 false).
    ///
    /// Variables are assumed to be 1-indexed in the input `Vec<i32>`. The absolute value
    /// of `i32` is taken as the variable identifier (typically `u32`), and its sign determines
    /// the polarity. `T::new(variable_id, polarity)` is used to create each literal.
    /// The `T::Variable` type associated with the `Literal` trait `T` should be compatible
    /// with `u32` or constructible from it.
    ///
    /// This constructor uses `Clause::new`, so literals will be deduplicated.
    /// Other fields (`lbd`, `deleted`, etc.) are initialized to defaults.
    fn from(literals_dimacs: Vec<i32>) -> Self {
        let literals_t = literals_dimacs
            .iter()
            .map(|&l_dimacs| {
                let polarity = l_dimacs.is_positive();
                let var_id = l_dimacs.unsigned_abs();
                T::new(var_id, polarity)
            })
            .collect_vec();

        Self::new(&literals_t)
    }
}

impl<L: Literal, S: LiteralStorage<L>> From<Vec<L>> for Clause<L, S> {
    /// Creates a clause directly from a `Vec<L>`.
    ///
    /// The provided `Vec<L>` is used to initialize the `literals` field, typically via
    /// `S::from(Vec<L>)` if `S` implements such a conversion (e.g., `SmallVec`).
    /// Note: This does not automatically deduplicate literals from `literals_vec`.
    /// If deduplication is required, consider using `Clause::new(&literals_vec)`.
    /// Other fields (`lbd`, `deleted`, etc.) are initialized to defaults.
    fn from(literals_vec: Vec<L>) -> Self {
        Self {
            literals: S::from(literals_vec), // Relies on S: From<Vec<L>>
            lbd: 0,
            deleted: false,
            is_learnt: false,
            activity: OrderedFloat::from(0.0),
            data: PhantomData,
        }
    }
}

impl<L: Literal, S: LiteralStorage<L>> From<&Vec<L>> for Clause<L, S> {
    /// Creates a clause from a reference to a `Vec<L>`, cloning the literals.
    ///
    /// The literals from `literals_vec` are cloned to create the `literals` field.
    /// Note: This does not automatically deduplicate literals.
    /// If deduplication is required, consider using `Clause::new(literals_vec.as_slice())`.
    /// Other fields (`lbd`, `deleted`, etc.) are initialized to defaults.
    fn from(literals_vec: &Vec<L>) -> Self {
        Self {
            literals: S::from(literals_vec.clone()),
            lbd: 0,
            deleted: false,
            is_learnt: false,
            activity: OrderedFloat::from(0.0),
            data: PhantomData,
        }
    }
}

impl<L: Literal + Eq + Hash, S: LiteralStorage<L>> FromIterator<i32> for Clause<L, S> {
    /// Creates a clause from an iterator of `i32` (DIMACS literals).
    ///
    /// This is similar to `From<Vec<i32>>`. Literals are converted from DIMACS format,
    /// collected into a temporary `Vec<L>`, and then `Clause::new` is used, which
    /// ensures deduplication.
    /// See `From<Vec<i32>>` for more details on DIMACS conversion and variable indexing.
    fn from_iter<I: IntoIterator<Item = i32>>(iter: I) -> Self {
        let literals_t: Vec<L> = iter
            .into_iter()
            .map(|l_dimacs| {
                let polarity = l_dimacs.is_positive();
                let var_id = l_dimacs.unsigned_abs();
                L::new(var_id, polarity)
            })
            .collect_vec();

        Self::new(&literals_t)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_from_i32_vec_and_len() {
        let clause: Clause = Clause::from(vec![1, 2, 3]);
        assert_eq!(clause.len(), 3, "Clause length should be 3");

        let expected_lit = PackedLiteral::new(1_u32, true);
        assert!(
            clause.literals.iter().any(|&l| l == expected_lit),
            "Clause should contain literal for var 1 positive"
        );
    }

    #[test]
    fn test_swap_no_assert() {
        let mut clause: Clause = Clause::from(vec![1, 2, 3]);

        if clause.len() == 3 {
            let lit0_before = clause.literals[0];
            let lit2_before = clause.literals[2];
            clause.swap(0, 2);
            assert_eq!(
                clause.literals[0], lit2_before,
                "Literal at index 0 should be the original literal from index 2"
            );
            assert_eq!(
                clause.literals[2], lit0_before,
                "Literal at index 2 should be the original literal from index 0"
            );
        } else {
            panic!("Clause length was not 3 after creation from vec![1,2,3]");
        }
    }

    #[test]
    fn test_is_tautology() {
        let tautology_clause: Clause = Clause::from(vec![1, -1]);
        assert!(
            tautology_clause.is_tautology(),
            "Clause should be tautology"
        );

        let non_tautology_clause: Clause = Clause::from(vec![1, 2]);
        assert!(
            !non_tautology_clause.is_tautology(),
            "Clause should not be tautology"
        );
    }

    #[test]
    fn test_resolve() {
        let clause1: Clause = Clause::from(vec![1, 2]);
        let clause2: Clause = Clause::from(vec![-1, 3]);
        let pivot = PackedLiteral::new(1_u32, true);

        let resolved_clause = clause1.resolve(&clause2, pivot);
        assert_eq!(
            resolved_clause.literals.len(),
            2,
            "Resolved clause should have 2 literals"
        );
        assert!(resolved_clause
            .literals
            .iter()
            .any(|&l| l == PackedLiteral::new(2_u32, true)));
        assert!(resolved_clause
            .literals
            .iter()
            .any(|&l| l == PackedLiteral::new(3_u32, true)));
    }

    #[test]
    fn test_is_unit() {
        let unit_clause: Clause = Clause::from(vec![1]);
        assert!(unit_clause.is_unit(), "Clause should be unit");

        let non_unit_clause: Clause = Clause::from(vec![1, 2]);
        assert!(!non_unit_clause.is_unit(), "Clause should not be unit");
    }

    #[test]
    fn test_is_empty() {
        let empty_clause: Clause = Clause::default();
        assert!(empty_clause.is_empty(), "Clause should be empty");

        let non_empty_clause: Clause = Clause::from(vec![1]);
        assert!(!non_empty_clause.is_empty(), "Clause should not be empty");
    }
}
