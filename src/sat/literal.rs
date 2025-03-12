#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
use core::ops::{Neg, Not};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Literal {
    var: usize,
    polarity: bool,
}

impl Literal {
    #[must_use]
    pub const fn new(var: usize, polarity: bool) -> Self {
        Self { var, polarity }
    }

    #[must_use]
    pub const fn negated(&self) -> Self {
        Self {
            var: self.var,
            polarity: !self.polarity,
        }
    }

    #[must_use]
    pub const fn is_negated(&self) -> bool {
        !self.polarity
    }

    #[must_use]
    pub const fn is_positive(&self) -> bool {
        self.polarity
    }

    #[must_use]
    pub const fn polarity(&self) -> bool {
        self.polarity
    }

    #[must_use]
    pub const fn variable(&self) -> usize {
        self.var
    }
}

impl From<i32> for Literal {
    fn from(l: i32) -> Self {
        let polarity = l.is_positive();
        let var = l.unsigned_abs() as usize;

        Self { var, polarity }
    }
}

impl From<&Literal> for i32 {
    fn from(l: &Literal) -> Self {
        if l.polarity {
            Self::try_from(l.var).expect("Literal variable is too large")
        } else {
            -Self::try_from(l.var).expect("Literal variable is too large")
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
        assert_eq!(Literal::from(1), Literal::new(1, true));
        assert_eq!(Literal::from(-1), Literal::new(1, false));
    }

    #[test]
    fn test_literal_into_i32() {
        assert_eq!(i32::from(&Literal::new(1, true)), 1);
        assert_eq!(i32::from(&Literal::new(1, false)), -1);
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
