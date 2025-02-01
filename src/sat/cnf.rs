use super::clause::Clause;
use super::expr::{apply_laws, Expr};
use crate::sat::literal::Literal;
use std::ops::{Index, IndexMut};

pub type DecisionLevel = u32;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct CNF {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
}

impl Index<usize> for CNF {
    type Output = Clause;

    fn index(&self, index: usize) -> &Self::Output {
        &self.clauses[index]
    }
}

impl IndexMut<usize> for CNF {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.clauses[index]
    }
}

impl CNF {
    pub fn new(clauses: Vec<Vec<i32>>) -> Self {
        let clauses: Vec<_> = clauses.into_iter().map(Clause::new).collect();

        let num_vars = clauses
            .iter()
            .flat_map(|c| c.iter())
            .map(|l| l.var)
            .max()
            .unwrap_or(0);

        Self { clauses, num_vars }
    }

    pub fn iter(&self) -> impl Iterator<Item = &Clause> {
        self.clauses.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Clause> {
        self.clauses.iter_mut()
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }
}

pub fn to_cnf(expr: &Expr) -> CNF {
    let expr = apply_laws(expr);
    let clauses = to_clauses(&expr);
    CNF::new(
        clauses
            .iter()
            .map(|c| c.iter().map(|l| l.into()).collect())
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
        e => Clause::new(vec![to_literal(e).var as i32]),
    }
}

fn to_literal(expr: &Expr) -> Literal {
    match expr {
        Expr::Var(i) => Literal::new(*i, false),
        Expr::Not(e) => -to_literal(e),
        _ => panic!("Not a literal"),
    }
}

fn to_expr(clause: Clause) -> Expr {
    let mut iter = clause.iter();
    let first = iter.next().unwrap();
    let mut expr = to_expr_literal(*first);
    for literal in iter {
        expr = Expr::Or(Box::new(expr), Box::new(to_expr_literal(*literal)));
    }
    expr
}

fn to_expr_literal(literal: Literal) -> Expr {
    if literal.negated {
        Expr::Not(Box::new(Expr::Var(literal.var)))
    } else {
        Expr::Var(literal.var)
    }
}

impl From<Expr> for CNF {
    fn from(expr: Expr) -> Self {
        to_cnf(&expr)
    }
}

impl From<CNF> for Expr {
    fn from(cnf: CNF) -> Self {
        let mut iter = cnf.iter();
        let first = iter.next().unwrap();
        let mut expr = to_expr(first.clone());
        for clause in iter {
            expr = Expr::And(Box::new(expr), Box::new(to_expr(clause.clone())));
        }
        expr
    }
}
