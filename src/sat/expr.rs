#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Expr {
    Var(usize),
    Not(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Val(bool),
}

impl Expr {
    pub fn is_val(&self) -> bool {
        matches!(self, Expr::Val(_))
    }

    pub fn is_var(&self) -> bool {
        matches!(self, Expr::Var(_))
    }

    pub fn is_not(&self) -> bool {
        matches!(self, Expr::Not(_))
    }

    pub fn is_and(&self) -> bool {
        matches!(self, Expr::And(_, _))
    }

    pub fn is_or(&self) -> bool {
        matches!(self, Expr::Or(_, _))
    }

    pub fn is_true(&self) -> bool {
        match self {
            Expr::Val(b) => *b,
            _ => false,
        }
    }

    pub fn is_false(&self) -> bool {
        match self {
            Expr::Val(b) => !*b,
            _ => false,
        }
    }

    pub fn unwrap_val(&self) -> bool {
        match self {
            Expr::Val(b) => *b,
            _ => panic!("Not a value"),
        }
    }

    pub fn unwrap_var(&self) -> usize {
        match self {
            Expr::Var(i) => *i,
            _ => panic!("Not a variable"),
        }
    }

    pub fn ors(e: &[Expr]) -> Expr {
        e.iter().fold(Expr::Val(false), |acc, x| {
            Expr::Or(Box::new(acc), Box::new(x.clone()))
        })
    }

    pub fn ands(e: &[Expr]) -> Expr {
        e.iter().fold(Expr::Val(true), |acc, x| {
            Expr::And(Box::new(acc), Box::new(x.clone()))
        })
    }
}

impl From<bool> for Expr {
    fn from(b: bool) -> Self {
        Expr::Val(b)
    }
}

impl From<usize> for Expr {
    fn from(i: usize) -> Self {
        Expr::Var(i)
    }
}

impl From<i32> for Expr {
    fn from(i: i32) -> Self {
        if i < 0 {
            Expr::Not(Box::new(Expr::Var((-i) as usize)))
        } else {
            Expr::Var(i as usize)
        }
    }
}

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
