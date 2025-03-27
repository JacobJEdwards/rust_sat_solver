#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
use super::clause::Clause;
use super::expr::{apply_laws, Expr};
use crate::sat::assignment::Solutions;
use crate::sat::literal::{Literal, PackedLiteral, Variable};
use crate::sat::solver::LiteralStorage;
use itertools::Itertools;
use num::traits::WrappingAdd;
use smallvec::SmallVec;
use std::ops::{Index, IndexMut};

pub type DecisionLevel = usize;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Cnf<L: Literal = PackedLiteral, S: LiteralStorage<L> = SmallVec<[L; 8]>> {
    pub clauses: Vec<Clause<L, S>>,
    pub num_vars: usize,
    pub vars: Vec<Variable>,
    pub lits: Vec<L>,
}

impl<T: Literal, S: LiteralStorage<T>> Index<usize> for Cnf<T, S> {
    type Output = Clause<T, S>;

    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.clauses.get_unchecked(index) }
    }
}

impl<T: Literal, S: LiteralStorage<T>> IndexMut<usize> for Cnf<T, S> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { self.clauses.get_unchecked_mut(index) }
    }
}

impl<T: Literal, S: LiteralStorage<T>> Cnf<T, S> {
    pub fn new(clauses: Vec<Vec<i32>>) -> Self {
        let (clauses, num_vars, vars, literals) = clauses
            .into_iter()
            .filter(|clause| !clause.is_empty())
            .map(Clause::from)
            .fold(
                (Vec::new(), 0u32, Vec::new(), Vec::new()),
                |(mut acc_clauses, mut max_var, mut acc_vars, mut acc_literals), clause| unsafe {
                    let clause_max_var = clause
                        .iter()
                        .map(|l: &T| l.variable())
                        .max()
                        .unwrap_unchecked();

                    max_var = max_var.max(clause_max_var);

                    acc_literals.extend(clause.iter().copied());
                    acc_vars.extend(clause.iter().map(|l| l.variable()));

                    acc_clauses.push(clause);

                    (acc_clauses, max_var, acc_vars, acc_literals)
                },
            );

        Self {
            clauses,
            num_vars: num_vars.wrapping_add(1) as usize,
            vars,
            lits: literals,
        }
    }

    pub fn remove(&mut self, idx: usize) {
        self.clauses.remove(idx);
    }

    pub fn iter(&self) -> impl Iterator<Item = &Clause<T, S>> {
        self.clauses.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Clause<T, S>> {
        self.clauses.iter_mut()
    }

    pub fn add_clause(&mut self, clause: Clause<T, S>) {
        unsafe {
            let max_var = clause.iter().map(|l| l.variable()).max().unwrap_unchecked() as usize;
            let vars = clause.iter().map(|l| l.variable()).collect_vec();

            self.vars.extend(vars);
            self.clauses.push(clause);

            let max_var = max_var.wrapping_add(1);
            if max_var > self.num_vars {
                self.num_vars = max_var;
            }
        }
    }

    pub fn add_clause_vec(&mut self, clause: Vec<i32>) {
        self.add_clause(Clause::from(clause));
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    #[must_use]
    pub fn verify(&self, solutions: &Solutions) -> bool {
        self.iter().all(|clause| {
            clause.iter().any(|&lit| {
                let var = i32::try_from(lit.variable()).unwrap_or(0);

                if lit.is_negated() {
                    solutions.contains(-var)
                } else {
                    solutions.contains(var)
                }
            })
        })
    }
}

impl<L: Literal, S: LiteralStorage<L>> FromIterator<Clause<L, S>> for Cnf<L, S> {
    fn from_iter<T: IntoIterator<Item = Clause<L, S>>>(iter: T) -> Self {
        let mut cnf = Self::default();
        for clause in iter {
            cnf.add_clause(clause);
        }
        cnf
    }
}

#[must_use]
pub fn to_cnf<T: Literal, S: LiteralStorage<T>>(expr: &Expr) -> Cnf<T, S> {
    let expr = apply_laws(expr);
    let clauses = to_clauses(&expr);
    Cnf::from_iter(clauses)
}

fn to_clauses<T: Literal, S: LiteralStorage<T>>(expr: &Expr) -> Vec<Clause<T, S>> {
    match expr {
        Expr::And(e1, e2) => {
            let mut c1 = to_clauses(e1);
            let c2 = to_clauses(e2);
            c1.extend(c2);
            c1
        }
        e => vec![to_clause(e)],
    }
}

fn to_clause<T: Literal, S: LiteralStorage<T>>(expr: &Expr) -> Clause<T, S> {
    match expr {
        Expr::Or(e1, e2) => {
            let mut c1: Clause<T, S> = to_clause(e1);
            let c2: Clause<T, S> = to_clause(e2);
            c1.literals.extend(c2.literals.iter().copied());
            c1
        }
        e => Clause::new(&[to_literal(e)]),
    }
}

fn to_literal<T: Literal>(expr: &Expr) -> T {
    match expr {
        Expr::Var(i) => T::new(*i, false),
        Expr::Not(e) => {
            let lit: T = to_literal(e);
            lit.negated()
        }
        _ => panic!("Not a literal"),
    }
}

fn to_expr<T: Literal, S: LiteralStorage<T>>(clause: &Clause<T, S>) -> Expr {
    let mut iter = clause.iter();
    let first = iter.next().unwrap();
    let mut expr = to_expr_literal(*first);
    for literal in iter {
        expr = Expr::Or(Box::new(expr), Box::new(to_expr_literal(*literal)));
    }
    expr
}

fn to_expr_literal<T: Literal>(literal: T) -> Expr {
    if literal.is_negated() {
        Expr::Not(Box::new(Expr::Var(literal.variable())))
    } else {
        Expr::Var(literal.variable())
    }
}

impl<T: Literal, S: LiteralStorage<T>> From<Expr> for Cnf<T, S> {
    fn from(expr: Expr) -> Self {
        to_cnf(&expr)
    }
}

impl<L: Literal, S: LiteralStorage<L>> From<Vec<Clause<L, S>>> for Cnf<L, S> {
    fn from(clauses: Vec<Clause<L, S>>) -> Self {
        Self::from_iter(clauses)
    }
}

impl<T: Literal, S: LiteralStorage<T>> TryFrom<Cnf<T, S>> for Expr {
    type Error = &'static str;

    fn try_from(cnf: Cnf<T, S>) -> Result<Self, Self::Error> {
        let mut iter = cnf.iter();
        let first = iter.next().ok_or("Empty CNF")?;
        let mut expr = to_expr(first);
        for clause in iter {
            expr = Self::And(Box::new(expr), Box::new(to_expr(clause)));
        }
        Ok(expr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_cnf() {
        let expr = Expr::Or(
            Box::new(Expr::Var(1)),
            Box::new(Expr::And(Box::new(Expr::Var(2)), Box::new(Expr::Var(3)))),
        );
        let cnf: Cnf = to_cnf(&expr);
        assert_eq!(cnf.len(), 2);
    }

    #[test]
    fn test_to_expr() {
        let clause: Clause = Clause::from(vec![1, 2, 3]);
        let expr = to_expr(&clause);
        assert_eq!(
            expr,
            Expr::Or(
                Box::new(Expr::Var(1)),
                Box::new(Expr::Or(Box::new(Expr::Var(2)), Box::new(Expr::Var(3))))
            )
        );
    }
}
