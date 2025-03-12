#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Expr {
    Var(usize),
    Not(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Val(bool),
}

impl Expr {
    #[must_use]
    pub const fn is_val(&self) -> bool {
        matches!(self, Self::Val(_))
    }

    #[must_use]
    pub const fn is_var(&self) -> bool {
        matches!(self, Self::Var(_))
    }

    #[must_use]
    pub const fn is_not(&self) -> bool {
        matches!(self, Self::Not(_))
    }

    #[must_use]
    pub const fn is_and(&self) -> bool {
        matches!(self, Self::And(_, _))
    }

    #[must_use]
    pub const fn is_or(&self) -> bool {
        matches!(self, Self::Or(_, _))
    }

    #[must_use]
    pub const fn is_true(&self) -> bool {
        match self {
            Self::Val(b) => *b,
            _ => false,
        }
    }

    #[must_use]
    pub const fn is_false(&self) -> bool {
        match self {
            Self::Val(b) => !*b,
            _ => false,
        }
    }

    #[must_use]
    pub fn unwrap_val(&self) -> bool {
        match self {
            Self::Val(b) => *b,
            _ => panic!("Not a value"),
        }
    }

    #[must_use]
    pub fn unwrap_var(&self) -> usize {
        match self {
            Self::Var(i) => *i,
            _ => panic!("Not a variable"),
        }
    }

    #[must_use]
    pub fn ors(e: &[Self]) -> Self {
        e.iter().fold(Self::Val(false), |acc, x| {
            Self::Or(Box::new(acc), Box::new(x.clone()))
        })
    }

    #[must_use]
    pub fn ands(e: &[Self]) -> Self {
        e.iter().fold(Self::Val(true), |acc, x| {
            Self::And(Box::new(acc), Box::new(x.clone()))
        })
    }
}

impl From<bool> for Expr {
    fn from(b: bool) -> Self {
        Self::Val(b)
    }
}

impl From<usize> for Expr {
    fn from(i: usize) -> Self {
        Self::Var(i)
    }
}

impl From<i32> for Expr {
    fn from(i: i32) -> Self {
        if i < 0 {
            Self::Not(Box::new(Self::Var(i.unsigned_abs() as usize)))
        } else {
            Self::Var(i.unsigned_abs() as usize)
        }
    }
}

#[must_use]
pub fn demorgans_laws(expr: &Expr) -> Expr {
    match expr {
        Expr::Not(e) => match *e.clone() {
            Expr::Var(i) => Expr::Not(Box::new(Expr::Var(i))),
            Expr::Not(e) => *e,
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
    }
}

#[must_use]
pub fn distributive_laws(expr: &Expr) -> Expr {
    let expr = expr.clone();
    match expr {
        Expr::And(e1, e2) => {
            let e1 = distributive_laws(&e1);
            let e2 = distributive_laws(&e2);
            match e1 {
                Expr::Or(e11, e12) => Expr::Or(
                    Box::new(distributive_laws(&Expr::And(e11, Box::from(e2.clone())))),
                    Box::new(distributive_laws(&Expr::And(e12, Box::from(e2)))),
                ),
                _ => match e2 {
                    Expr::Or(e21, e22) => Expr::Or(
                        Box::new(distributive_laws(&Expr::And(Box::from(e1.clone()), e21))),
                        Box::new(distributive_laws(&Expr::And(Box::from(e1.clone()), e22))),
                    ),
                    _ => Expr::And(Box::new(e1), Box::new(e2)),
                },
            }
        }
        Expr::Or(e1, e2) => Expr::Or(
            Box::new(distributive_laws(&e1)),
            Box::new(distributive_laws(&e2)),
        ),
        Expr::Val(b) => Expr::Val(b),
        Expr::Var(i) => Expr::Var(i),
        Expr::Not(_) => panic!("Not implemented"),
    }
}

#[must_use]
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_demorgans_laws() {
        let expr = Expr::Not(Box::new(Expr::And(
            Box::new(Expr::Var(1)),
            Box::new(Expr::Var(2)),
        )));
        let expected = Expr::Or(
            Box::new(Expr::Not(Box::new(Expr::Var(1)))),
            Box::new(Expr::Not(Box::new(Expr::Var(2)))),
        );
        assert_eq!(demorgans_laws(&expr), expected);
    }

    #[test]
    fn test_distributive_laws() {
        let expr = Expr::And(
            Box::new(Expr::Or(Box::new(Expr::Var(1)), Box::new(Expr::Var(2)))),
            Box::new(Expr::Var(3)),
        );
        let expected = Expr::Or(
            Box::new(Expr::And(Box::new(Expr::Var(1)), Box::new(Expr::Var(3)))),
            Box::new(Expr::And(Box::new(Expr::Var(2)), Box::new(Expr::Var(3)))),
        );
        assert_eq!(distributive_laws(&expr), expected);
    }

    #[test]
    fn test_apply_laws() {
        let expr = Expr::And(
            Box::new(Expr::Or(Box::new(Expr::Var(1)), Box::new(Expr::Var(2)))),
            Box::new(Expr::Var(3)),
        );
        let expected = Expr::Or(
            Box::new(Expr::And(Box::new(Expr::Var(1)), Box::new(Expr::Var(3)))),
            Box::new(Expr::And(Box::new(Expr::Var(2)), Box::new(Expr::Var(3)))),
        );
        assert_eq!(apply_laws(&expr), expected);
    }
}
