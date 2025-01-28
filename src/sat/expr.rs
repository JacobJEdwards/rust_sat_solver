#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Expr {
    Var(usize),
    Not(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Val(bool),
    // Implies(Box<Expr>, Box<Expr>),
    // Xor(Box<Expr>, Box<Expr>),
    // XNor(Box<Expr>, Box<Expr>),
    // NAnd(Box<Expr>, Box<Expr>),
    // NOr(Box<Expr>, Box<Expr>),
}

pub fn un_val(e: &Expr) -> bool {
    match e {
        Expr::Val(b) => *b,
        _ => panic!("Not a value"),
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

pub fn to_var(i: isize) -> Expr {
    if i < 0 {
        Expr::Not(Box::new(Expr::Var((-i) as usize)))
    } else {
        Expr::Var(i as usize)
    }
}
