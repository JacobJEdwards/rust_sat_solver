//! Defines an arbitrary boolean expression type and functions for its manipulation.
//!
//! This module provides an `Expr` enum to represent boolean expressions involving
//! variables, logical NOT, AND, OR, and constant boolean values (true/false).
//! It includes helper methods for checking expression types, unwrapping values,
//! and constructing complex expressions from slices.
//!
//! Furthermore, it implements several logical transformation functions:
//! - `demorgans_laws`: Applies De Morgan's laws to push negations inwards.
//! - `distributive_laws`: Applies distributive laws (e.g., AND over OR) to transform
//!   expressions towards a conjunctive or disjunctive normal form.
//! - `apply_laws`: A higher-level function that repeatedly applies De Morgan's and
//!   distributive laws until the expression stabilizes, aiming to convert it into
//!   a form suitable for CNF conversion (though full CNF conversion often requires
//!   more, like Tseytin transformation for non-exponential results).

#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

use crate::sat::literal::Variable;

/// Represents a boolean expression.
///
/// Expressions can be:
/// - A `Var(Variable)`: A propositional variable.
/// - A `Not(Box<Expr>)`: The logical negation of an expression.
/// - An `And(Box<Expr>, Box<Expr>)`: The logical conjunction of two expressions.
/// - An `Or(Box<Expr>, Box<Expr>)`: The logical disjunction of two expressions.
/// - A `Val(bool)`: A constant boolean value (`true` or `false`).
///
/// `Box<Expr>` is used for recursive variants (`Not`, `And`, `Or`) to avoid
/// infinitely sized types.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Expr {
    /// A propositional variable, identified by `Variable`.
    Var(Variable),
    /// Logical negation of an inner expression.
    Not(Box<Expr>),
    /// Logical conjunction (AND) of two inner expressions.
    And(Box<Expr>, Box<Expr>),
    /// Logical disjunction (OR) of two inner expressions.
    Or(Box<Expr>, Box<Expr>),
    /// A constant boolean value (`true` or `false`).
    Val(bool),
}

impl Expr {
    /// Checks if the expression is a `Val` variant.
    #[must_use]
    pub const fn is_val(&self) -> bool {
        matches!(self, Self::Val(_))
    }

    /// Checks if the expression is a `Var` variant.
    #[must_use]
    pub const fn is_var(&self) -> bool {
        matches!(self, Self::Var(_))
    }

    /// Checks if the expression is a `Not` variant.
    #[must_use]
    pub const fn is_not(&self) -> bool {
        matches!(self, Self::Not(_))
    }

    /// Checks if the expression is an `And` variant.
    #[must_use]
    pub const fn is_and(&self) -> bool {
        matches!(self, Self::And(_, _))
    }

    /// Checks if the expression is an `Or` variant.
    #[must_use]
    pub const fn is_or(&self) -> bool {
        matches!(self, Self::Or(_, _))
    }

    /// Checks if the expression is `Val(true)`.
    #[must_use]
    pub const fn is_true(&self) -> bool {
        match self {
            Self::Val(b) => *b,
            _ => false,
        }
    }

    /// Checks if the expression is `Val(false)`.
    #[must_use]
    pub const fn is_false(&self) -> bool {
        match self {
            Self::Val(b) => !*b,
            _ => false,
        }
    }

    /// Unwraps the boolean value if the expression is a `Val` variant.
    ///
    /// # Panics
    ///
    /// Panics if the expression is not `Expr::Val(_)`.
    #[must_use]
    pub fn unwrap_val(&self) -> bool {
        match self {
            Self::Val(b) => *b,
            _ => panic!("Called unwrap_val on a non-Val expression: {self:?}"),
        }
    }

    /// Unwraps the variable identifier if the expression is a `Var` variant.
    ///
    /// # Panics
    ///
    /// Panics if the expression is not `Expr::Var(_)`.
    #[must_use]
    pub fn unwrap_var(&self) -> Variable {
        match self {
            Self::Var(i) => *i,
            _ => panic!("Called unwrap_var on a non-Var expression: {self:?}"),
        }
    }

    /// Creates a new expression representing the disjunction (OR) of all expressions in the slice `e`.
    ///
    /// `e_1 OR e_2 OR ... OR e_n`.
    /// The fold starts with `Expr::Val(false)` as the identity for OR (`x OR false == x`).
    /// If `e` is empty, `Expr::Val(false)` is returned.
    ///
    /// # Arguments
    ///
    /// * `e`: A slice of `Expr` to be OR-ed together.
    ///
    /// # Returns
    ///
    /// A new `Expr` representing the OR of all expressions in `e`.
    ///
    /// # Panics
    ///
    /// Panics if `e` is empty, as the OR of no elements is not defined.
    #[must_use]
    pub fn ors(expressions: &[Self]) -> Self {
        if expressions.is_empty() {
            return Self::Val(false);
        }
        let mut iter = expressions.iter();
        let first = iter.next().unwrap().clone();
        iter.fold(first, |acc, x| Self::Or(Box::new(acc), Box::new(x.clone())))
    }

    /// Creates a new expression representing the conjunction (AND) of all expressions in the slice `e`.
    ///
    /// `e_1 AND e_2 AND ... AND e_n`.
    /// The fold starts with `Expr::Val(true)` as the identity for AND (`x AND true == x`).
    /// If `e` is empty, `Expr::Val(true)` is returned.
    ///
    /// # Arguments
    ///
    /// * `e`: A slice of `Expr` to be AND-ed together.
    ///
    /// # Returns
    ///
    /// A new `Expr` representing the AND of all expressions in `e`.
    ///
    /// # Panics
    ///
    /// Should not panic, but if `e` is empty, it returns `Expr::Val(true)`.
    #[must_use]
    pub fn ands(expressions: &[Self]) -> Self {
        if expressions.is_empty() {
            return Self::Val(true);
        }
        let mut iter = expressions.iter();
        let first = iter.next().unwrap().clone();
        iter.fold(first, |acc, x| {
            Self::And(Box::new(acc), Box::new(x.clone()))
        })
    }
}

impl From<bool> for Expr {
    /// Converts a `bool` into an `Expr::Val`.
    fn from(b: bool) -> Self {
        Self::Val(b)
    }
}

impl From<Variable> for Expr {
    /// Converts a `Variable` into an `Expr::Var`.
    fn from(i: Variable) -> Self {
        Self::Var(i)
    }
}

impl From<i32> for Expr {
    /// Converts an `i32` (DIMACS-style literal) into an `Expr`.
    /// A positive `i` becomes `Expr::Var(i.abs())`.
    /// A negative `i` becomes `Expr::Not(Box::new(Expr::Var(i.abs())))`.
    /// `Variable` is assumed to be constructible from `u32`.
    fn from(i: i32) -> Self {
        let var_id = i.unsigned_abs();
        if i < 0 {
            Self::Not(Box::new(Self::Var(var_id)))
        } else {
            Self::Var(var_id)
        }
    }
}

/// Applies De Morgan's laws to an expression to push negations (`Not`) inwards.
///
/// - `Not(And(e1, e2))` becomes `Or(Not(e1), Not(e2))` (after recursive calls).
/// - `Not(Or(e1, e2))` becomes `And(Not(e1), Not(e2))` (after recursive calls).
/// - `Not(Not(e))` becomes `e`.
/// - `Not(Var(i))` remains `Not(Var(i))`.
/// - `Not(Val(b))` becomes `Val(!b)`.
///
/// The function recursively applies these transformations throughout the expression.
/// Non-`Not` expressions are traversed, and `demorgans_laws` is applied to their sub-expressions.
///
/// # Arguments
///
/// * `expr`: The expression to transform.
///
/// # Returns
///
/// A new `Expr` with negations pushed inwards.
#[must_use]
pub fn demorgans_laws(expr: &Expr) -> Expr {
    match expr {
        Expr::Not(e_boxed) => match e_boxed.as_ref() {
            Expr::Var(i) => Expr::Not(Box::new(Expr::Var(*i))),
            Expr::Not(inner_e_boxed) => demorgans_laws(inner_e_boxed.as_ref()),
            Expr::And(e1, e2) => Expr::Or(
                Box::new(demorgans_laws(&Expr::Not(e1.clone()))),
                Box::new(demorgans_laws(&Expr::Not(e2.clone()))),
            ),
            Expr::Or(e1, e2) => Expr::And(
                Box::new(demorgans_laws(&Expr::Not(e1.clone()))),
                Box::new(demorgans_laws(&Expr::Not(e2.clone()))),
            ),
            Expr::Val(b) => Expr::Val(!*b),
        },
        Expr::And(e1, e2) => Expr::And(Box::new(demorgans_laws(e1)), Box::new(demorgans_laws(e2))),
        Expr::Or(e1, e2) => Expr::Or(Box::new(demorgans_laws(e1)), Box::new(demorgans_laws(e2))),
        Expr::Val(b) => Expr::Val(*b),
        Expr::Var(i) => Expr::Var(*i),
    }
}

/// Applies distributive laws to an expression, primarily `A AND (B OR C) -> (A AND B) OR (A AND C)`
/// and `(B OR C) AND A -> (B AND A) OR (C AND A)`.
///
/// This function aims to transform expressions towards a disjunctive normal form (DNF) if applied
/// to distribute AND over OR.
///
/// The current implementation focuses on distributing AND over OR:
/// - `e1 AND (e21 OR e22)` becomes `(e1 AND e21) OR (e1 AND e22)`.
/// - `(e11 OR e12) AND e2` becomes `(e11 AND e2) OR (e12 AND e2)`.
///
/// It recursively applies these transformations.
///
/// # Arguments
///
/// * `expr`: The expression to transform.
///
/// # Panics
///
/// Panics if it encounters an `Expr::Not(_)` variant directly during distribution, as it
/// expects negations to have been pushed to the literal level (NNF) by `demorgans_laws`
/// before distribution is applied for typical CNF/DNF conversion steps.
#[must_use]
pub fn distributive_laws(expr: &Expr) -> Expr {
    let current_expr = expr.clone();
    match current_expr {
        Expr::And(e1_boxed, e2_boxed) => {
            let e1_dist = distributive_laws(&e1_boxed);
            let e2_dist = distributive_laws(&e2_boxed);

            match (e1_dist.clone(), e2_dist.clone()) {
                (Expr::Or(e11, e12), _) => Expr::Or(
                    Box::new(distributive_laws(&Expr::And(
                        e11,
                        Box::new(e2_dist.clone()),
                    ))),
                    Box::new(distributive_laws(&Expr::And(e12, Box::new(e2_dist)))),
                ),
                (_, Expr::Or(e21, e22)) => Expr::Or(
                    Box::new(distributive_laws(&Expr::And(
                        Box::new(e1_dist.clone()),
                        e21,
                    ))),
                    Box::new(distributive_laws(&Expr::And(Box::new(e1_dist), e22))),
                ),
                _ => Expr::And(Box::new(e1_dist), Box::new(e2_dist)),
            }
        }
        Expr::Or(e1_boxed, e2_boxed) => Expr::Or(
            Box::new(distributive_laws(&e1_boxed)),
            Box::new(distributive_laws(&e2_boxed)),
        ),
        Expr::Val(b) => Expr::Val(b),
        Expr::Var(i) => Expr::Var(i),
        Expr::Not(inner_expr_boxed) => {
            Expr::Not(Box::new(distributive_laws(inner_expr_boxed.as_ref())))
        }
    }
}

/// Applies De Morgan's laws and then distributive laws repeatedly to an expression
/// until it no longer changes (reaches a fixed point).
///
/// This is a common step in converting an arbitrary boolean expression into a
/// standard form, often as a preliminary step before full CNF or DNF conversion.
/// The goal is typically to achieve Negation Normal Form (NNF) via `demorgans_laws`,
/// and then apply `distributive_laws` to move towards a sum-of-products (DNF) or
/// product-of-sums (CNF like) structure. The current `distributive_laws` primarily
/// creates DNF-like structures (ORs of ANDs).
///
/// # Arguments
///
/// * `expr`: The initial expression.
///
/// # Returns
///
/// The transformed `Expr` after applying laws to a fixed point.
#[must_use]
pub fn apply_laws(expr: &Expr) -> Expr {
    let mut current_expr = expr.clone();
    loop {
        let nnf_expr = demorgans_laws(&current_expr);
        let distributed_expr = distributive_laws(&nnf_expr);

        if distributed_expr == current_expr {
            break;
        }
        current_expr = distributed_expr;
    }
    current_expr
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(id: u32) -> Expr {
        Expr::Var(id)
    }
    fn not(expr: Expr) -> Expr {
        Expr::Not(Box::new(expr))
    }
    fn and(e1: Expr, e2: Expr) -> Expr {
        Expr::And(Box::new(e1), Box::new(e2))
    }
    fn or(e1: Expr, e2: Expr) -> Expr {
        Expr::Or(Box::new(e1), Box::new(e2))
    }

    #[test]
    fn test_demorgans_laws_not_and() {
        let expr = not(and(var(1), var(2)));
        let expected = or(not(var(1)), not(var(2)));
        assert_eq!(demorgans_laws(&expr), expected);
    }

    #[test]
    fn test_demorgans_laws_not_or() {
        let expr = not(or(var(1), var(2)));
        let expected = and(not(var(1)), not(var(2)));
        assert_eq!(demorgans_laws(&expr), expected);
    }

    #[test]
    fn test_demorgans_laws_double_negation() {
        let expr = not(not(var(1)));
        let expected = var(1);
        assert_eq!(demorgans_laws(&expr), expected);
    }

    #[test]
    fn test_demorgans_laws_not_val() {
        let expr = not(Expr::Val(true));
        let expected = Expr::Val(false);
        assert_eq!(demorgans_laws(&expr), expected);
    }

    #[test]
    fn test_demorgans_laws_nested() {
        let expr = not(and(var(1), not(or(var(2), var(3)))));
        let expected = or(not(var(1)), or(var(2), var(3)));
        assert_eq!(demorgans_laws(&expr), expected);
    }

    #[test]
    fn test_distributive_laws_a_and_or_b_c() {
        let expr = and(or(var(1), var(2)), var(3));
        let expected = or(and(var(1), var(3)), and(var(2), var(3)));
        assert_eq!(distributive_laws(&expr), expected);
    }

    #[test]
    fn test_distributive_laws_or_a_b_and_c() {
        let expr = and(or(var(1), var(2)), var(3));
        let expected = or(and(var(1), var(3)), and(var(2), var(3)));
        assert_eq!(distributive_laws(&expr), expected);
    }

    #[test]
    fn test_distributive_laws_no_change() {
        let expr = and(var(1), var(2));
        assert_eq!(distributive_laws(&expr), expr.clone());

        let expr_or = or(var(1), var(2));
        assert_eq!(distributive_laws(&expr_or), expr_or.clone());
    }

    #[test]
    fn test_distributive_laws_handles_not_nnf() {
        let expr = and(not(var(1)), or(var(2), var(3)));
        let expected = or(and(not(var(1)), var(2)), and(not(var(1)), var(3)));
        assert_eq!(distributive_laws(&expr), expected);
    }

    #[test]
    fn test_apply_laws_simple_distribution() {
        let expr = and(or(var(1), var(2)), var(3));
        let expected = or(and(var(1), var(3)), and(var(2), var(3)));
        assert_eq!(apply_laws(&expr), expected);
    }

    #[test]
    fn test_apply_laws_with_demorgans() {
        let expr = and(not(and(var(1), var(2))), var(3));
        let expected = or(and(not(var(1)), var(3)), and(not(var(2)), var(3)));
        assert_eq!(apply_laws(&expr), expected);
    }

    #[test]
    fn test_apply_laws_stabilization() {
        let expr = or(and(var(1), var(3)), and(var(2), var(3)));
        assert_eq!(apply_laws(&expr), expr.clone());
    }

    #[test]
    fn test_ors_and_ands_helpers() {
        assert_eq!(Expr::ors(&[]), Expr::Val(false));
        assert_eq!(Expr::ands(&[]), Expr::Val(true));

        let exprs = [var(1), var(2), var(3)];
        let or_expr = Expr::ors(&exprs);
        let expected_or = or(or(var(1), var(2)), var(3));
        assert_eq!(or_expr, expected_or);

        let and_expr = Expr::ands(&exprs);
        let expected_and = and(and(var(1), var(2)), var(3));
        assert_eq!(and_expr, expected_and);

        assert_eq!(Expr::ors(&[var(1)]), var(1));
        assert_eq!(Expr::ands(&[var(1)]), var(1));
    }
}
