use core::ops::{Neg, Not};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Literal {
    pub var: usize,
    pub negated: bool,
}

impl Literal {
    pub const fn new(var: usize, negated: bool) -> Self {
        Self { var, negated }
    }

    pub const fn negated(&self) -> Self {
        Self {
            var: self.var,
            negated: !self.negated,
        }
    }
}

impl From<i32> for Literal {
    fn from(l: i32) -> Self {
        let negated = l.is_negative();
        let var = l.unsigned_abs() as usize;

        Self { var, negated }
    }
}

impl From<&Literal> for i32 {
    fn from(l: &Literal) -> Self {
        if l.negated {
            -(l.var as i32)
        } else {
            l.var as i32
        }
    }
}

impl Neg for Literal {
    type Output = Self;

    fn neg(self) -> Self::Output {
        self.negated()
    }
}

impl Not for Literal {
    type Output = Self;

    fn not(self) -> Self::Output {
        self.negated()
    }
}

impl Neg for &Literal {
    type Output = Literal;

    fn neg(self) -> Self::Output {
        self.negated()
    }
}

impl Not for &Literal {
    type Output = Literal;

    fn not(self) -> Self::Output {
        self.negated()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_literal_from_i32() {
        assert_eq!(Literal::from(1), Literal::new(1, false));
        assert_eq!(Literal::from(-1), Literal::new(1, true));
    }

    #[test]
    fn test_literal_into_i32() {
        assert_eq!(i32::from(&Literal::new(1, false)), 1);
        assert_eq!(i32::from(&Literal::new(1, true)), -1);
    }

    #[test]
    fn test_literal_neg() {
        assert_eq!(-Literal::new(1, false), Literal::new(1, true));
        assert_eq!(-Literal::new(1, true), Literal::new(1, false));
    }

    #[test]
    fn test_literal_not() {
        assert_eq!(!Literal::new(1, false), Literal::new(1, true));
        assert_eq!(!Literal::new(1, true), Literal::new(1, false));
    }
}
