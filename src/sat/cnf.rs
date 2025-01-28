use super::expr::Expr;
use std::collections::hash_set::HashSet;

pub type Literal = i32;
pub type Variable = usize;

pub type DecisionLevel = u32;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Clause {
    pub literals: Vec<i32>,
    pub watched: (usize, usize),
}

impl Clause {
    pub fn new(literals: Vec<i32>) -> Self {
        Clause {
            literals: literals.clone(),
            watched: if literals.len() > 1 {
                (0, 1)
            } else {
                (0, 0)
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CNF(Vec<Clause>);

impl CNF {
    pub fn new(clauses: Vec<Vec<i32>>) -> Self {
        CNF(clauses
            .into_iter()
            .map(|c| 
                Clause {
                    literals: c.iter().map(|l| *l).collect(),
                    watched: if c.len() > 1 {
                        (0, 1)
                    } else {
                        (0, 0)
                    },
                }
    )
            .collect())
    }

    pub fn clauses(&self) -> Vec<Clause> {
        self.0.clone()
    }

    pub fn all_variables(&self) -> Vec<usize> {
        let literals = self.0.iter().map(|c| c.literals.iter().map(|l| var_of_lit(*l))).flatten().collect();
        literals
    }
    
    pub fn iter(&self) -> impl Iterator<Item = &Clause> {
        self.0.iter()
    }
}

pub fn var_of_lit(l: Literal) -> Variable {
    l.abs() as Variable
}

pub fn neg_lit(l: Literal) -> Literal {
    -l
}

pub fn demorgans_laws(expr: &Expr) -> Expr {
    match expr {
        Expr::Not(e) => match *e.clone() {
            Expr::Var(i) => Expr::Not(Box::new(Expr::Var(i))),
            Expr::Not(e) => *e.clone(),
            Expr::And(e1, e2) => Expr::Or(
                Box::new(demorgans_laws(&Expr::Not(e1))),
                Box::new(demorgans_laws(&Expr::Not(e2))),
            ),
            Expr::Or(e1, e2) => Expr::And(
                Box::new(demorgans_laws(&Expr::Not(e1))),
                Box::new(demorgans_laws(&Expr::Not(e2))),
            ),
            Expr::Val(b) => Expr::Val(!b),
        },
        Expr::And(e1, e2) => Expr::And(Box::new(demorgans_laws(e1)), Box::new(demorgans_laws(e2))),
        Expr::Or(e1, e2) => Expr::Or(Box::new(demorgans_laws(e1)), Box::new(demorgans_laws(e2))),
        Expr::Val(b) => Expr::Val(*b),
        Expr::Var(i) => Expr::Var(*i),
        _ => panic!("Not implemented"),
    }
}

pub fn distributive_laws(expr: &Expr) -> Expr {
    let expr = expr.clone();
    match expr {
        Expr::And(e1, e2) => {
            let e1 = distributive_laws(&*e1);
            let e2 = distributive_laws(&*e2);
            match e1 {
                Expr::Or(e11, e12) => Expr::Or(
                    Box::new(distributive_laws(&Expr::And(
                        e11.clone(),
                        Box::from(e2.clone()),
                    ))),
                    Box::new(distributive_laws(&Expr::And(e12, Box::from(e2)))),
                ),
                _ => match e2 {
                    Expr::Or(e21, e22) => Expr::Or(
                        Box::new(distributive_laws(&Expr::And(
                            Box::from(e1.clone()),
                            e21.clone(),
                        ))),
                        Box::new(distributive_laws(&Expr::And(
                            Box::from(e1.clone()),
                            e22.clone(),
                        ))),
                    ),
                    _ => Expr::And(Box::new(e1), Box::new(e2)),
                },
            }
        }
        Expr::Or(e1, e2) => Expr::Or(
            Box::new(distributive_laws(&*e1)),
            Box::new(distributive_laws(&*e2)),
        ),
        Expr::Val(b) => Expr::Val(b),
        Expr::Var(i) => Expr::Var(i),
        _ => panic!("Not implemented"),
    }
}

pub fn apply_laws(expr: &Expr) -> Expr {
    let mut expr = expr.clone();
    loop {
        let new_expr = distributive_laws(&demorgans_laws(&expr));
        if new_expr == expr {
            break;
        }
        expr = new_expr;
    }
    expr
}

pub fn to_cnf(expr: &Expr) -> CNF {
    let expr = apply_laws(expr);
    let clauses = to_clauses(&expr);
    CNF::new(clauses.iter().map(|c| c.literals.clone()).collect())
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
        e => Clause::new(
            vec![to_literal(e)],
        ),
    }
}

fn to_literal(expr: &Expr) -> Literal {
    match expr {
        Expr::Var(i) => *i as Literal,
        Expr::Not(e) => -to_literal(e),
        _ => panic!("Not a literal"),
    }
}

pub fn add_clause(cnf: &mut CNF, clause: Clause) {
    cnf.0.push(clause);
}

pub fn is_negative(l: Literal) -> bool {
    l < 0
}
