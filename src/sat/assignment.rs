#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
#![allow(
    unsafe_code,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap
)]

//! This module defines the `Assignment` trait and its implementations for managing variable states
//! in the SAT solvers.
//!
//! It provides a way to track whether variables are assigned true, false, or remain unassigned.
//!
//! It includes two main implementations:
//! - `VecAssignment`: Uses a `Vec<VarState>` for dense variable sets.
//! - `HashMapAssignment`: Uses an `FxHashMap<Variable, VarState>` for sparse or non-contiguous variable sets.
//!
//! The `Assignment` trait defines methods for setting, resetting, and querying variable states,
//! as well as retrieving solutions in a format compatible with SAT solver outputs.

use crate::sat::literal::{Literal, Variable};
use crate::sat::solver::Solutions;
use core::ops::{Index, IndexMut};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use std::fmt::Debug;
use std::hash::Hash;

/// Represents the assignment state of a propositional variable.
///
/// A variable can be unassigned, or assigned to true or false.
#[derive(Debug, Clone, PartialEq, Eq, Copy, Default, Hash, PartialOrd, Ord)]
pub enum VarState {
    /// The variable has not been assigned a truth value.
    #[default]
    Unassigned,
    /// The variable has been assigned a specific truth value.
    Assigned(bool),
}

impl VarState {
    /// Checks if the variable state is `Assigned`.
    ///
    /// # Returns
    ///
    /// `true` if the variable is assigned (either true or false), `false` otherwise.
    #[must_use]
    pub const fn is_assigned(self) -> bool {
        matches!(self, Self::Assigned(_))
    }

    /// Checks if the variable state is `Unassigned`.
    ///
    /// # Returns
    ///
    /// `true` if the variable is unassigned, `false` otherwise.
    #[must_use]
    pub const fn is_unassigned(self) -> bool {
        !self.is_assigned()
    }

    /// Checks if the variable state is `Assigned(true)`.
    ///
    /// # Returns
    ///
    /// `true` if the variable is assigned true, `false` otherwise.
    #[must_use]
    pub const fn is_true(self) -> bool {
        matches!(self, Self::Assigned(true))
    }

    /// Checks if the variable state is `Assigned(false)`.
    ///
    /// # Returns
    ///
    /// `true` if the variable is assigned false, `false` otherwise.
    #[must_use]
    pub const fn is_false(self) -> bool {
        matches!(self, Self::Assigned(false))
    }
}

impl From<VarState> for Option<bool> {
    /// Converts a `VarState` into an `Option<bool>`.
    ///
    /// `VarState::Assigned(b)` converts to `Some(b)`.
    /// `VarState::Unassigned` converts to `None`.
    fn from(s: VarState) -> Self {
        match s {
            VarState::Assigned(b) => Some(b),
            VarState::Unassigned => None,
        }
    }
}

impl From<Option<bool>> for VarState {
    /// Converts an `Option<bool>` into a `VarState`.
    ///
    /// `Some(b)` converts to `VarState::Assigned(b)`.
    /// `None` converts to `VarState::Unassigned`.
    fn from(b: Option<bool>) -> Self {
        b.map_or(Self::Unassigned, VarState::Assigned)
    }
}

/// Trait defining the interface for managing variable assignments.
///
/// This trait allows for different underlying data structures (e.g. `Vec`, `HashMap`)
/// to store and manage the states of variables in a SAT solver.
/// Variables are typically represented by `usize` indices for direct access,
/// or `Variable` (a `u32` alias) for semantic clarity.
/// Assumes 0-indexed variables if `Variable` is a numeric type used as an index.
pub trait Assignment:
    Index<usize, Output = VarState> + IndexMut<usize, Output = VarState> + Debug + Clone
{
    /// Creates a new assignment manager for `n_vars` variables.
    ///
    /// All variables are initially `Unassigned`.
    ///
    /// # Arguments
    ///
    /// * `n_vars`: The total number of variables to manage.
    fn new(n_vars: usize) -> Self;

    /// Returns the total number of variables this assignment manager is configured for.
    fn num_vars(&self) -> usize;

    /// Sets the truth value of a variable.
    ///
    /// # Arguments
    ///
    /// * `var`: The variable to assign.
    /// * `b`: The boolean value to assign (`true` or `false`).
    fn set(&mut self, var: Variable, b: bool);

    /// Resets all variables to the `Unassigned` state.
    fn reset(&mut self);

    /// Assigns a truth value to a variable based on a literal.
    ///
    /// The variable of the literal is assigned the literal's polarity.
    /// For example, if `l` is `x_i`, `x_i` is set to `true`. If `l` is `!x_i`, `x_i` is set to `false`.
    ///
    /// # Arguments
    ///
    /// * `l`: The literal to assign.
    fn assign(&mut self, l: impl Literal) {
        self.set(l.variable(), l.polarity());
    }

    /// Sets a variable to the `Unassigned` state.
    ///
    /// # Arguments
    ///
    /// * `var`: The variable to unassign.
    fn unassign(&mut self, var: Variable);

    /// Retrieves the current set of assigned variables as a `Solutions` object.
    ///
    /// `Solutions` expects 1-indexed variable IDs for DIMACS compatibility.
    fn get_solutions(&self) -> Solutions;

    /// Checks if a specific variable is assigned a truth value.
    ///
    /// # Arguments
    ///
    /// * `var`: The variable to check.
    ///
    /// # Returns
    ///
    /// `true` if the variable is assigned, `false` otherwise.
    fn is_assigned(&self, var: Variable) -> bool {
        self[var as usize].is_assigned()
    }

    /// Gets the truth value of a variable, if assigned.
    ///
    /// # Arguments
    ///
    /// * `var`: The variable whose value is requested.
    ///
    /// # Returns
    ///
    /// `Some(true)` if the variable is assigned true, `Some(false)` if assigned false,
    /// or `None` if unassigned.
    fn var_value(&self, var: Variable) -> Option<bool> {
        self[var as usize].into()
    }

    /// Checks if all variables managed by this assignment are currently assigned.
    ///
    /// # Returns
    ///
    /// `true` if all variables have a truth value, `false` otherwise.
    fn all_assigned(&self) -> bool;

    /// Gets the truth value of a literal under the current assignment.
    ///
    /// # Arguments
    ///
    /// * `l`: The literal to evaluate.
    ///
    /// # Returns
    ///
    /// `Some(true)` if the literal is true, `Some(false)` if false,
    /// or `None` if the literal's variable is unassigned.
    fn literal_value(&self, l: impl Literal) -> Option<bool> {
        self.var_value(l.variable()).map(|b| b == l.polarity())
    }

    /// Returns an iterator over all currently unassigned variables.
    ///
    /// The iterator yields `Variable` identifiers.
    fn unassigned(&self) -> impl Iterator<Item = Variable> + '_ {
        (0..self.num_vars()).filter_map(move |i| {
            #[allow(clippy::cast_possible_truncation)]
            let var = i as Variable;
            if self[var as usize].is_unassigned() {
                Some(var)
            } else {
                None
            }
        })
    }
}

/// An implementation of `Assignment` using a `Vec<VarState>`.
///
/// This implementation is efficient for dense sets of variables, where variable IDs
/// are contiguous and start from 0 (i.e. `0, 1, ..., n-1`).
/// Indexing with a `usize` value greater than or equal to the number of variables
/// will result in a panic.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct VecAssignment {
    /// Stores the state of each variable. The index in the vector corresponds to the `Variable` ID.
    states: Vec<VarState>,
}

impl Index<usize> for VecAssignment {
    type Output = VarState;

    /// Accesses the state of the variable at the given `index`.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    /// The `unsafe get_unchecked` is used for performance, assuming valid indices
    /// from internal logic.
    fn index(&self, index: usize) -> &Self::Output {
        // Safety: Caller must ensure index is within bounds [0, states.len()).
        // This should never fault when used correctly
        unsafe { self.states.get_unchecked(index) }
    }
}

impl IndexMut<usize> for VecAssignment {
    /// Mutably accesses the state of the variable at the given `index`.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    /// The `unsafe get_unchecked_mut` is used for performance, similar to `index`.
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        // Safety: Caller must ensure index is within bounds [0, states.len()).
        // This should never fault when used correctly
        unsafe { self.states.get_unchecked_mut(index) }
    }
}

impl Assignment for VecAssignment {
    /// Creates a new `VecAssignment` for `n_vars` variables.
    /// Variables are indexed from `0` to `n_vars - 1`.
    fn new(n_vars: usize) -> Self {
        Self {
            states: vec![VarState::Unassigned; n_vars],
        }
    }

    fn num_vars(&self) -> usize {
        self.states.len()
    }

    fn set(&mut self, var: Variable, b: bool) {
        self[var as usize] = VarState::Assigned(b);
    }

    fn reset(&mut self) {
        self.states.fill(VarState::Unassigned);
    }

    fn unassign(&mut self, var: Variable) {
        self[var as usize] = VarState::Unassigned;
    }

    fn get_solutions(&self) -> Solutions {
        Solutions::new(
            &self
                .states
                .iter()
                .enumerate()
                .filter_map(|(i, s)| {
                    #[allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]
                    let var_id = i as i32;
                    match s {
                        VarState::Assigned(true) => Some(var_id),
                        VarState::Assigned(false) => Some(-var_id),
                        _ => None,
                    }
                })
                .collect_vec(),
        )
    }

    fn all_assigned(&self) -> bool {
        self.states.iter().all(|v| v.is_assigned())
    }
}

/// An implementation of `Assignment` using an `FxHashMap<Variable, VarState>`.
///
/// This implementation is suitable for sparse sets of variables or when variable IDs
/// are not necessarily small or contiguous. It stores states only for variables
/// that have been explicitly set or unassigned. Accessing a variable not in the map
/// via `Index` will return `VarState::Unassigned`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct HashMapAssignment {
    /// Stores variable states. Keys are `Variable` IDs.
    map: FxHashMap<Variable, VarState>,
    /// The total number of distinct variables expected or managed by this assignment instance.
    /// Used for `all_assigned` and iterating `unassigned` variables up to this conceptual limit.
    num_vars: usize,
}

impl Index<usize> for HashMapAssignment {
    type Output = VarState;

    /// Accesses the state of the variable corresponding to `index`.
    ///
    /// If the variable (converted from `index`) is not in the map,
    /// it's treated as `Unassigned`.
    fn index(&self, index: usize) -> &Self::Output {
        #[allow(clippy::cast_possible_truncation)]
        self.map
            .get(&(index as Variable))
            .unwrap_or(&VarState::Unassigned)
    }
}

impl IndexMut<usize> for HashMapAssignment {
    /// Mutably accesses the state of the variable corresponding to `index`.
    ///
    /// If the variable (converted from `index`) is not in the map, it's inserted
    /// with `VarState::Unassigned` before returning a mutable reference.
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        #[allow(clippy::cast_possible_truncation)]
        self.map
            .entry(index as Variable)
            .or_insert(VarState::Unassigned)
    }
}

impl Assignment for HashMapAssignment {
    /// Creates a new `HashMapAssignment`.
    ///
    /// # Arguments
    ///
    /// * `n_vars`: The conceptual number of variables. This is used by `all_assigned`
    ///   to determine if all *expected* variables have assignments, and by
    ///   `unassigned` to iterate up to this many variables.
    fn new(n_vars: usize) -> Self {
        Self {
            map: FxHashMap::default(),
            num_vars: n_vars,
        }
    }

    fn num_vars(&self) -> usize {
        self.num_vars
    }

    fn set(&mut self, var: Variable, b: bool) {
        self.map.insert(var, VarState::Assigned(b));
    }

    fn reset(&mut self) {
        self.map.clear();
    }

    /// Unassigns a variable by setting its state to `VarState::Unassigned` in the map.
    /// If the variable was not in the map, it will be inserted as `Unassigned`.
    fn unassign(&mut self, var: Variable) {
        self.map.insert(var, VarState::Unassigned);
    }

    fn get_solutions(&self) -> Solutions {
        Solutions::new(
            &self
                .map
                .iter()
                .filter_map(|(&var, s)| {
                    #[allow(clippy::cast_possible_wrap)]
                    let var_id = var as i32;
                    match s {
                        VarState::Assigned(true) => Some(var_id),
                        VarState::Assigned(false) => Some(-var_id),
                        _ => None,
                    }
                })
                .collect_vec(),
        )
    }

    fn all_assigned(&self) -> bool {
        self.map.len() == self.num_vars && self.map.values().all(|v| v.is_assigned())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::literal::PackedLiteral;

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

    #[allow(clippy::cognitive_complexity)]
    fn test_assignment<A: Assignment>(a: &mut A) {
        a.set(1, true);
        a.set(2, false);
        a.set(3, true);

        assert!(a.is_assigned(1));
        assert!(a.is_assigned(2));
        assert!(a.is_assigned(3));
        assert!(!a.is_assigned(0));

        assert_eq!(a.var_value(1), Some(true));
        assert_eq!(a.var_value(2), Some(false));
        assert_eq!(a.var_value(3), Some(true));
        assert_eq!(a.var_value(0), None);

        assert_eq!(a.literal_value(PackedLiteral::new(1, false)), Some(false));
        assert_eq!(a.literal_value(PackedLiteral::new(1, true)), Some(true));

        assert_eq!(a.literal_value(PackedLiteral::new(2, false)), Some(true));
        assert_eq!(a.literal_value(PackedLiteral::new(2, true)), Some(false));

        assert_eq!(a.literal_value(PackedLiteral::new(3, false)), Some(false));
        assert_eq!(a.literal_value(PackedLiteral::new(3, true)), Some(true));

        a.unassign(1);
        assert!(!a.is_assigned(1));
        assert_eq!(a.var_value(1), None);
        assert_eq!(a.literal_value(PackedLiteral::new(1, false)), None);

        let s = a.get_solutions();
        assert_eq!(s, Solutions::new(&[-2, 3]));

        let unassigned_vars = a.unassigned().collect_vec();
        assert_eq!(unassigned_vars, vec![0, 1]);

        assert!(!a.all_assigned());
        a.set(0, true);
        a.set(1, true);
        assert!(a.all_assigned());

        a.reset();
        assert!(!a.is_assigned(0));
        assert!(!a.is_assigned(1));
        assert!(!a.is_assigned(2));
        assert!(!a.is_assigned(3));
        assert!(!a.all_assigned());
    }

    #[test]
    fn test_assignment_vec() {
        let mut a: VecAssignment = Assignment::new(4);
        test_assignment(&mut a);
    }

    #[test]
    fn test_hashmap_assignment() {
        let mut a = HashMapAssignment::new(4);
        test_assignment(&mut a);
    }

    #[test]
    fn test_assignment_unassigned_default_impl() {
        let a = VecAssignment::new(4);
        assert!(!a.is_assigned(0));
        assert!(!a.is_assigned(1));
        assert!(!a.is_assigned(2));
        assert!(!a.is_assigned(3));
        assert_eq!(a.unassigned().count(), 4);
        assert!(!a.all_assigned());

        let b = HashMapAssignment::new(4);
        assert!(!b.is_assigned(0));
        assert!(!b.is_assigned(1));
        assert_eq!(b.unassigned().count(), 4);
        assert!(!b.all_assigned());

        let c = VecAssignment::new(0);
        assert!(c.all_assigned());

        let d = HashMapAssignment::new(0);
        assert!(d.all_assigned());
    }
}
