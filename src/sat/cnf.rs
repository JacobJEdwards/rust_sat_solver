#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
use super::clause::Clause;
use super::expr::{apply_laws, Expr};
use crate::sat::assignment::{Assignment, Solutions};
use crate::sat::literal::Literal;
use std::ops::{Index, IndexMut};

pub type DecisionLevel = usize;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Cnf {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
}

impl Index<usize> for Cnf {
    type Output = Clause;

    fn index(&self, index: usize) -> &Self::Output {
        &self.clauses[index]
    }
}

impl IndexMut<usize> for Cnf {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.clauses[index]
    }
}

impl Cnf {
    pub fn new(clauses: Vec<Vec<i32>>) -> Self {
        let clauses: Vec<_> = clauses
            .into_iter()
            .filter(|clause| !clause.is_empty())
            .map(Clause::from)
            .collect();

        let num_vars = clauses
            .iter()
            .flat_map(Clause::iter)
            .map(Literal::variable)
            .max()
            .unwrap_or(0)
            + 1;

        Self { clauses, num_vars }
    }

    pub fn remove(&mut self, idx: usize) {
        self.clauses.remove(idx);
    }

    pub fn iter(&self) -> impl Iterator<Item = &Clause> {
        self.clauses.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Clause> {
        self.clauses.iter_mut()
    }

    pub fn add_clause(&mut self, clause: Clause) {
        let max_var = clause.iter().map(Literal::variable).max().unwrap_or(0);

        self.clauses.push(clause);

        if max_var > self.num_vars {
            self.num_vars = max_var;
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
                if lit.is_negated() {
                    solutions.contains(-(lit.variable() as i32))
                } else {
                    solutions.contains(lit.variable() as i32)
                }
            })
        })
    }
}

impl FromIterator<Clause> for Cnf {
    fn from_iter<T: IntoIterator<Item = Clause>>(iter: T) -> Self {
        let mut cnf = Self::default();
        for clause in iter {
            cnf.add_clause(clause);
        }
        cnf
    }
}

#[must_use]
pub fn to_cnf(expr: &Expr) -> Cnf {
    let expr = apply_laws(expr);
    let clauses = to_clauses(&expr);
    Cnf::new(
        clauses
            .iter()
            .map(|c| c.iter().map(std::convert::Into::into).collect())
            .collect(),
    )
}

fn to_clauses(expr: &Expr) -> Vec<Clause> {
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

fn to_clause(expr: &Expr) -> Clause {
    match expr {
        Expr::Or(e1, e2) => {
            let mut c1 = to_clause(e1);
            let c2 = to_clause(e2);
            c1.literals.extend(c2.literals);
            c1
        }
        e => Clause::new(vec![to_literal(e)]),
    }
}

fn to_literal(expr: &Expr) -> Literal {
    match expr {
        Expr::Var(i) => Literal::new(*i, false),
        Expr::Not(e) => -to_literal(e),
        _ => panic!("Not a literal"),
    }
}

fn to_expr(clause: &Clause) -> Expr {
    let mut iter = clause.iter();
    let first = iter.next().unwrap();
    let mut expr = to_expr_literal(*first);
    for literal in iter {
        expr = Expr::Or(Box::new(expr), Box::new(to_expr_literal(*literal)));
    }
    expr
}

fn to_expr_literal(literal: Literal) -> Expr {
    if literal.is_negated() {
        Expr::Not(Box::new(Expr::Var(literal.variable())))
    } else {
        Expr::Var(literal.variable())
    }
}

impl From<Expr> for Cnf {
    fn from(expr: Expr) -> Self {
        to_cnf(&expr)
    }
}

impl TryFrom<Cnf> for Expr {
    type Error = &'static str;

    fn try_from(cnf: Cnf) -> Result<Self, Self::Error> {
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
        let cnf = to_cnf(&expr);
        assert_eq!(cnf.len(), 2);
    }

    #[test]
    fn test_to_expr() {
        let clause = Clause::from(vec![1, 2, 3]);
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
