#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
//! Defines the Conjunctive Normal Form (CNF) representation for SAT formulas.
//!
//! A CNF formula is a conjunction (AND) of clauses, where each clause is a
//! disjunction (OR) of literals. This is the standard input format for most
//! SAT solvers.
//!
//! This module provides:
//! - The `Cnf` struct to store a list of clauses and related metadata.
//! - Methods for constructing `Cnf` from various sources (e.g. iterators of DIMACS literals, `Expr`).
//! - Utilities for interacting with the `Cnf` formula, such as adding clauses, iterating,
//!   and verifying solutions.
//! - Conversion functions to and from a more general `Expr` (expression tree) representation.
#![allow(unsafe_code, clippy::cast_possible_truncation, clippy::cast_sign_loss)]

use super::clause::Clause;
use super::expr::{apply_laws, Expr};
use crate::sat::clause_storage::LiteralStorage;
use crate::sat::literal;
use crate::sat::literal::{Literal, PackedLiteral, Variable};
use crate::sat::solver::Solutions;
use itertools::Itertools;
use smallvec::SmallVec;
use std::fmt::Display;
use std::num::NonZeroI32;
use std::ops::{Index, IndexMut};

/// Represents a decision level in the SAT solver's search process.
pub type DecisionLevel = usize;

/// Represents a boolean formula in Conjunctive Normal Form (CNF).
///
/// A CNF formula is a collection of clauses. The formula is satisfied if and only if
/// all its clauses are satisfied.
///
/// # Type Parameters
///
/// * `L`: The type of `Literal` used in the clauses. Defaults to `PackedLiteral`.
/// * `S`: The `LiteralStorage` type used within each `Clause`. Defaults to `SmallVec<[L; 8]>`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Cnf<L: Literal = PackedLiteral, S: LiteralStorage<L> = SmallVec<[L; 8]>> {
    /// The list of clauses that make up the CNF formula.
    pub clauses: Vec<Clause<L, S>>,
    /// The highest variable identifier encountered in the formula, plus one.
    /// This represents the number of distinct variables if they are numbered contiguously from 0 or 1.
    /// If variables are 1-indexed `v1, ..., vn`, `num_vars` would be `n+1`.
    /// If variables are 0-indexed `v0, ..., v(n-1)`, `num_vars` would be `n`.
    pub num_vars: usize,
    /// A flat list of all variable identifiers present in the formula. May contain duplicates.
    pub vars: Vec<Variable>,
    /// A flat list of all literals present across all clauses. May contain duplicates.
    pub lits: Vec<L>,
    /// The index in `clauses` vector that separates original problem clauses from learnt clauses.
    /// Clauses from `0` to `non_learnt_idx - 1` are original.
    /// Clauses from `non_learnt_idx` onwards are learnt during solving.
    /// When a `Cnf` is first created from a problem, `non_learnt_idx` is equal to `clauses.len()`.
    pub non_learnt_idx: usize,
}

impl<T: Literal, S: LiteralStorage<T>> Index<usize> for Cnf<T, S> {
    type Output = Clause<T, S>;

    /// Accesses the clause at the given `index`.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Safety
    ///
    /// This implementation uses `get_unchecked` for performance
    fn index(&self, index: usize) -> &Self::Output {
        // Safety: Caller must ensure `index` is within bounds `[0, self.clauses.len())`.
        // This should be fine if used correctly.
        unsafe { self.clauses.get_unchecked(index) }
    }
}

impl<T: Literal, S: LiteralStorage<T>> IndexMut<usize> for Cnf<T, S> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        // Safety: Caller must ensure `index` is within bounds `[0, self.clauses.len())`.
        // This should be fine if used correctly.
        unsafe { self.clauses.get_unchecked_mut(index) }
    }
}

impl<T: Literal, S: LiteralStorage<T>> Cnf<T, S> {
    /// Creates a new `Cnf` instance from an iterator of clauses, where each clause
    /// is itself an iterator of `i32` (DIMACS literals).
    ///
    /// Example: `Cnf::new(vec![vec![1, -2], vec![2, 3]])` creates a CNF for
    /// `(x1 OR !x2) AND (x2 OR x3)`.
    ///
    /// During construction, it determines `num_vars` based on the maximum variable ID
    /// encountered. `vars` and `lits` collect all variables and literals.
    /// `non_learnt_idx` is set to the total number of initial clauses.
    ///
    /// # Type Parameters for Arguments
    ///
    /// * `J`: An iterator yielding `i32` (DIMACS literals for a single clause).
    /// * `I`: An iterator yielding `J` (an iterator of clauses).
    pub fn new<J: IntoIterator<Item = i32>, I: IntoIterator<Item = J>>(clauses_iter: I) -> Self {
        let (clauses_vec, max_var_id, vars_vec, lits_vec, num_initial_clauses) = clauses_iter
            .into_iter()
            .map(|clause_dimacs| clause_dimacs.into_iter().collect::<Clause<_, _>>())
            .fold(
                (Vec::new(), u32::default(), Vec::new(), Vec::new(), 0),
                |(
                    mut acc_clauses,
                    mut current_max_var,
                    mut acc_vars,
                    mut acc_lits,
                    clause_count,
                ),
                 clause| {
                    if clause.is_empty() || clause.is_tautology() {
                        return (
                            acc_clauses,
                            current_max_var,
                            acc_vars,
                            acc_lits,
                            clause_count,
                        );
                    }

                    let clause_max_var = clause
                        .iter()
                        .map(|l: &T| l.variable())
                        .max()
                        .unwrap_or_default();

                    current_max_var = current_max_var.max(clause_max_var);

                    acc_lits.extend(clause.iter().copied());
                    acc_vars.extend(clause.iter().map(|l| l.variable()));

                    acc_clauses.push(clause);

                    (
                        acc_clauses,
                        current_max_var,
                        acc_vars,
                        acc_lits,
                        clause_count + 1,
                    )
                },
            );

        Self {
            clauses: clauses_vec,
            num_vars: (max_var_id as usize).wrapping_add(1),
            vars: vars_vec,
            lits: lits_vec,
            non_learnt_idx: num_initial_clauses,
        }
    }

    /// Removes a clause at the specified index.
    ///
    /// # Arguments
    ///
    /// * `idx`: The index of the clause to remove.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is out of bounds.
    pub fn remove(&mut self, idx: usize) {
        self.clauses.remove(idx);
        if idx < self.non_learnt_idx {
            self.non_learnt_idx = self.non_learnt_idx.saturating_sub(1);
        }
    }

    /// Returns an iterator over the clauses in the CNF.
    pub fn iter(&self) -> impl Iterator<Item = &Clause<T, S>> {
        self.clauses.iter()
    }

    /// Returns a mutable iterator over the clauses in the CNF.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Clause<T, S>> {
        self.clauses.iter_mut()
    }

    /// Adds a new clause to the CNF.
    ///
    /// The clause is added to the end of the `clauses` list. If it's considered a learnt
    /// clause, it should be added after `non_learnt_idx`. This function implicitly adds
    /// it as if it's a new problem clause if `non_learnt_idx` isn't managed externally
    /// before calling this for learnt clauses.
    ///
    /// Updates `num_vars`, `vars`, and `lits` based on the new clause.
    ///
    /// # Arguments
    ///
    /// * `clause`: The `Clause<T, S>` to add.
    pub fn add_clause(&mut self, clause: Clause<T, S>) {
        let clause_max_var_id = clause
            .iter()
            .map(|l| l.variable())
            .max()
            .unwrap_or_default();
        let clause_max_var_usize = clause_max_var_id as usize;

        let clause_vars = clause.iter().map(|l| l.variable()).collect_vec();

        self.vars.extend(clause_vars);
        self.lits.extend(clause.iter());
        self.clauses.push(clause);

        let required_num_vars = clause_max_var_usize.wrapping_add(1);
        self.num_vars = self.num_vars.max(required_num_vars);
    }

    /// Adds a new clause specified as a `Vec<i32>` (DIMACS literals).
    ///
    /// Converts `clause_dimacs` to a `Clause<T, S>` and then calls `add_clause`.
    ///
    /// # Arguments
    ///
    /// * `clause_dimacs`: A vector of `i32` representing the clause.
    pub fn add_clause_vec(&mut self, clause_dimacs: Vec<i32>) {
        self.add_clause(Clause::from(clause_dimacs));
    }

    /// Returns the total number of clauses in the CNF (both original and learnt).
    #[must_use]
    pub const fn len(&self) -> usize {
        self.clauses.len()
    }

    /// Returns `true` if the CNF contains no clauses.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    /// Verifies if a given set of solutions satisfies the CNF formula.
    ///
    /// A CNF is satisfied if every clause in it is satisfied. A clause is satisfied
    /// if at least one of its literals is true under the given assignment.
    ///
    /// # Arguments
    ///
    /// * `solutions`: A `Solutions` object providing the truth assignment for variables.
    ///   `Solutions` handles DIMACS-style variable IDs (1-indexed, signed).
    ///
    /// # Returns
    ///
    /// `true` if `solutions` satisfies all clauses in the CNF, `false` otherwise.
    #[must_use]
    pub fn verify(&self, solutions: &Solutions) -> bool {
        self.iter().all(|clause| {
            clause.iter().any(|&lit| {
                let lit_i32 = lit.to_i32();
                NonZeroI32::new(lit_i32).is_some_and(|nonzero_var| solutions.check(nonzero_var))
            })
        })
    }

    /// Converts this `Cnf<T, S>` into a `Cnf<L, U>` with different literal or storage types.
    ///
    /// Each clause is converted using `Clause::convert`. Metadata like `num_vars`,
    /// `vars`, `lits`, and `non_learnt_idx` are also transformed or cloned.
    ///
    /// # Type Parameters
    ///
    /// * `L`: The target `Literal` type for the new CNF.
    /// * `U`: The target `LiteralStorage<L>` type for clauses in the new CNF.
    ///
    /// # Returns
    ///
    /// A new `Cnf<L, U>` instance.
    pub fn convert<TargetL: Literal, TargetS: LiteralStorage<TargetL>>(
        &self,
    ) -> Cnf<TargetL, TargetS> {
        let clauses_converted = self.clauses.iter().map(Clause::convert).collect_vec();

        let vars_converted = self.vars.clone();

        let lits_converted = self.lits.iter().map(|l| literal::convert(l)).collect_vec();

        Cnf {
            clauses: clauses_converted,
            num_vars: self.num_vars,
            vars: vars_converted,
            lits: lits_converted,
            non_learnt_idx: self.non_learnt_idx,
        }
    }
}

impl<L: Literal, S: LiteralStorage<L>> Display for Cnf<L, S> {
    /// Formats the CNF into DIMACS CNF format.
    ///
    /// Example output:
    /// ```
    /// c Generated by CNF
    /// p cnf <num_vars> <num_clauses>
    /// 1 -2 0
    /// 2 3 0
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let dimacs_num_vars = if self.num_vars > 0 {
            self.num_vars - 1
        } else {
            0
        };
        let dimacs_num_clauses = self.non_learnt_idx;

        writeln!(f, "c Generated by CNF module")?;
        writeln!(f, "p cnf {dimacs_num_vars} {dimacs_num_clauses}")?;

        for clause_idx in 0..self.non_learnt_idx {
            let clause = &self.clauses[clause_idx];
            for &lit in clause.iter() {
                write!(f, "{} ", lit.to_i32())?;
            }
            writeln!(f, "0")?;
        }
        Ok(())
    }
}

impl<L: Literal, S: LiteralStorage<L>> FromIterator<Clause<L, S>> for Cnf<L, S> {
    /// Creates a `Cnf` from an iterator of `Clause<L, S>`.
    ///
    /// Each clause from the iterator is added using `self.add_clause`.
    /// This initialises a default `Cnf` and then populates it.
    /// `non_learnt_idx` will be implicitly managed by `add_clause` if it updates it,
    /// or will remain 0 if `add_clause` only appends to `clauses`.
    /// A more robust way would be to collect clauses, then initialise `Cnf` fields properly.
    fn from_iter<IterClauses: IntoIterator<Item = Clause<L, S>>>(iter: IterClauses) -> Self {
        let mut cnf = Self::default();
        let mut max_var_id = u32::default();
        let mut clause_count = 0;

        for clause in iter {
            if let Some(clause_max_v) = clause.iter().map(|l| l.variable()).max() {
                max_var_id = max_var_id.max(clause_max_v);
            }
            cnf.vars.extend(clause.iter().map(|l| l.variable()));
            cnf.lits.extend(clause.iter().copied());
            cnf.clauses.push(clause);
            clause_count += 1;
        }
        cnf.num_vars = (max_var_id as usize).wrapping_add(1);
        cnf.non_learnt_idx = clause_count;
        cnf
    }
}

/// Converts a general boolean expression (`Expr`) into CNF.
///
/// The conversion involves:
/// 1. Applying logical laws (`apply_laws`) to transform the expression into a
///    structure that is easier to convert to CNF (e.g. NNF, pushing negations inwards).
/// 2. Recursively converting the transformed expression into a list of clauses (`to_clauses`).
/// 3. Constructing a `Cnf` object from this list of clauses.
///
/// Note: This is a standard, potentially exponential, conversion for arbitrary expressions.
/// For more efficient CNF conversion (e.g. Tseytin transformation), specialised algorithms are needed.
#[must_use]
pub fn to_cnf<T: Literal, S: LiteralStorage<T>>(expr: &Expr) -> Cnf<T, S> {
    let cnf_expr = apply_laws(expr);
    let clauses_vec = to_clauses_recursive(&cnf_expr);
    Cnf::from_iter(clauses_vec)
}

/// Helper function to recursively convert an `Expr` (assumed to be in a CNF-friendly form)
/// into a list of `Clause`s.
fn to_clauses_recursive<T: Literal, S: LiteralStorage<T>>(expr: &Expr) -> Vec<Clause<T, S>> {
    match expr {
        Expr::And(e1, e2) => {
            let mut c1_clauses = to_clauses_recursive(e1);
            let c2_clauses = to_clauses_recursive(e2);
            c1_clauses.extend(c2_clauses);
            c1_clauses
        }
        _ => vec![to_clause_recursive(expr)],
    }
}

/// Helper function to convert an `Expr` representing a disjunction or a literal
/// into a single `Clause`.
fn to_clause_recursive<T: Literal, S: LiteralStorage<T>>(expr: &Expr) -> Clause<T, S> {
    match expr {
        Expr::Or(e1, e2) => {
            let clause1: Clause<T, S> = to_clause_recursive(e1);
            let clause2: Clause<T, S> = to_clause_recursive(e2);
            let mut combined_lits: Vec<T> = Vec::from(&clause1);
            combined_lits.extend(Vec::from(&clause2));
            Clause::<T, S>::new(&combined_lits)
        }
        _ => Clause::<T, S>::new(&[expr_to_literal(expr)]),
    }
}

/// Helper function to convert an `Expr` representing a literal into a `Literal` type `T`.
/// Panics if the expression is not a literal form (Var or Not(Var)).
fn expr_to_literal<T: Literal>(expr: &Expr) -> T {
    match expr {
        Expr::Var(i) => T::new(*i, true),
        Expr::Not(e) => {
            if let Expr::Var(i) = **e {
                T::new(i, false)
            } else {
                panic!("Expression Not(Non-Variable) encountered where literal expected.");
            }
        }
        _ => panic!("Expression is not a literal (Var or Not(Var))."),
    }
}

/// Converts a `Clause` back into an `Expr` (a disjunction of literal expressions).
fn clause_to_expr<T: Literal, S: LiteralStorage<T>>(clause: &Clause<T, S>) -> Expr {
    let mut iter = clause.iter();
    let first_lit_expr =
        literal_to_expr_node(*iter.next().expect("Cannot convert empty clause to Expr"));
    iter.fold(first_lit_expr, |acc_expr, &literal| {
        Expr::Or(Box::new(acc_expr), Box::new(literal_to_expr_node(literal)))
    })
}

/// Converts a `Literal` `T` into an `Expr` node (Var or Not(Var)).
fn literal_to_expr_node<T: Literal>(literal: T) -> Expr {
    if literal.polarity() {
        Expr::Var(literal.variable())
    } else {
        Expr::Not(Box::new(Expr::Var(literal.variable())))
    }
}

impl<T: Literal, S: LiteralStorage<T>> From<Expr> for Cnf<T, S> {
    /// Converts an `Expr` into a `Cnf<T, S>`.
    /// This is a convenience wrapper around `to_cnf`.
    fn from(expr: Expr) -> Self {
        to_cnf(&expr)
    }
}

impl<L: Literal, S: LiteralStorage<L>> From<Vec<Clause<L, S>>> for Cnf<L, S> {
    /// Converts a `Vec<Clause<L, S>>` directly into a `Cnf<L, S>`.
    /// Uses `from_iter` for consistent initialisation.
    fn from(clauses: Vec<Clause<L, S>>) -> Self {
        Self::from_iter(clauses)
    }
}

impl<L: Literal, S: LiteralStorage<L>> From<Vec<Vec<i32>>> for Cnf<L, S> {
    /// Converts `Vec<Vec<i32>>` (DIMACS clauses) into a `Cnf<L, S>`.
    /// Uses `Cnf::new` for construction.
    fn from(value: Vec<Vec<i32>>) -> Self {
        Self::new(value)
    }
}

impl<T: Literal, S: LiteralStorage<T>> TryFrom<Cnf<T, S>> for Expr {
    type Error = &'static str;

    /// Attempts to convert a `Cnf<T, S>` back into an `Expr`.
    /// The resulting `Expr` will be a conjunction of disjunctions.
    /// Returns an error if the CNF is empty (contains no clauses).
    fn try_from(cnf: Cnf<T, S>) -> Result<Self, Self::Error> {
        let mut iter = cnf.iter();
        let first_clause_expr =
            clause_to_expr(iter.next().ok_or("Cannot convert empty CNF to Expr")?);

        iter.try_fold(first_clause_expr, |acc_expr, clause| {
            Ok(Self::And(
                Box::new(acc_expr),
                Box::new(clause_to_expr(clause)),
            ))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::literal::PackedLiteral;

    #[test]
    fn test_cnf_new_from_dimacs() {
        let dimacs_clauses = vec![vec![1, -2], vec![-1, 2, 3]];
        let cnf: Cnf<PackedLiteral> = Cnf::new(dimacs_clauses);

        assert_eq!(cnf.clauses.len(), 2);
        assert_eq!(cnf.num_vars, 3 + 1);
        assert_eq!(cnf.non_learnt_idx, 2);

        let first_clause = &cnf.clauses[0];
        assert_eq!(first_clause.len(), 2);
        assert!(first_clause
            .iter()
            .any(|l| l.variable() == 1_u32 && l.polarity()));
        assert!(first_clause
            .iter()
            .any(|l| l.variable() == 2_u32 && !l.polarity()));
    }

    #[test]
    fn test_cnf_add_clause() {
        let mut cnf: Cnf<PackedLiteral> = Cnf::new(Vec::<Vec<i32>>::new());
        assert_eq!(cnf.num_vars, 1);

        let clause1_dimacs = vec![1, -2];
        cnf.add_clause_vec(clause1_dimacs);
        assert_eq!(cnf.clauses.len(), 1);
        assert_eq!(cnf.num_vars, 2 + 1);

        let clause2 = Clause::from(vec![-2, 3, 4]);
        cnf.add_clause(clause2);
        assert_eq!(cnf.clauses.len(), 2);
        assert_eq!(cnf.num_vars, 4 + 1);
    }

    #[test]
    fn test_cnf_display_dimacs() {
        let cnf: Cnf<PackedLiteral> = Cnf::new(vec![vec![1, -2], vec![2, 3]]);
        let dimacs_str = format!("{cnf}");
        let expected_header = "p cnf 3 2";
        assert!(
            dimacs_str.contains(expected_header),
            "DIMACS header mismatch"
        );
        assert!(dimacs_str.contains("1 -2 0"), "Clause 1 mismatch");
        assert!(dimacs_str.contains("2 3 0"), "Clause 2 mismatch");
    }

    #[test]
    fn test_cnf_from_expr() {
        let expr = Expr::And(
            Box::new(Expr::Or(
                Box::new(Expr::Var(1_u32)),
                Box::new(Expr::Not(Box::new(Expr::Var(2_u32)))),
            )),
            Box::new(Expr::Or(
                Box::new(Expr::Var(2_u32)),
                Box::new(Expr::Var(3_u32)),
            )),
        );

        let cnf: Cnf<PackedLiteral> = Cnf::from(expr);
        assert_eq!(cnf.clauses.len(), 2);
        assert_eq!(cnf.num_vars, 3 + 1);

        assert!(cnf.clauses.iter().any(|c| {
            c.len() == 2
                && c.iter().any(|l| l.variable() == 1_u32 && l.polarity())
                && c.iter().any(|l| l.variable() == 2_u32 && !l.polarity())
        }));

        assert!(cnf.clauses.iter().any(|c| {
            c.len() == 2
                && c.iter().any(|l| l.variable() == 2_u32 && l.polarity())
                && c.iter().any(|l| l.variable() == 3_u32 && l.polarity())
        }));
    }

    #[test]
    fn test_cnf_verify_solution() {
        let cnf: Cnf<PackedLiteral> = Cnf::new(vec![vec![1, -2], vec![-1, 2, 3]]);
        let mut solutions = Solutions::default();
        solutions.add(1.try_into().unwrap());
        solutions.add((-2).try_into().unwrap());
        solutions.add(3.try_into().unwrap());
        assert!(cnf.verify(&solutions));

        let mut solutions_fail = Solutions::default();
        solutions_fail.add((-1).try_into().unwrap());
        solutions_fail.add(2.try_into().unwrap());
        solutions_fail.add((-3).try_into().unwrap());
        assert!(!cnf.verify(&solutions_fail));
    }

    #[test]
    fn test_cnf_new_empty_input() {
        let cnf_empty: Cnf<PackedLiteral> = Cnf::new(Vec::<Vec<i32>>::new());
        assert!(cnf_empty.is_empty());
        assert_eq!(cnf_empty.num_vars, 1);
        assert_eq!(cnf_empty.non_learnt_idx, 0);
    }

    #[test]
    fn test_cnf_new_with_empty_clause() {
        let cnf_with_empty_clause: Cnf<PackedLiteral> = Cnf::new(vec![Vec::<i32>::new()]);
        assert_eq!(cnf_with_empty_clause.clauses.len(), 0);
    }
}
