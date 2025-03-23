#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
use core::ops::{Neg, Not};
use std::fmt::Debug;
use std::hash::Hash;

pub type Variable = u32;

pub trait Literal: Copy + Debug + Eq + Hash + Default {
    fn new(var: Variable, polarity: bool) -> Self;
    fn variable(self) -> Variable;
    fn polarity(self) -> bool;

    #[must_use]
    fn negated(self) -> Self;

    fn is_negated(self) -> bool {
        !self.polarity()
    }

    fn is_positive(self) -> bool {
        !self.polarity()
    }

    #[must_use]
    fn from_i32(value: i32) -> Self {
        let polarity = value.is_positive();
        let var = value.unsigned_abs();
        Self::new(var, polarity)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct PackedLiteral(u32);

impl Literal for PackedLiteral {
    fn new(var: Variable, polarity: bool) -> Self {
        Self(var & 0x7FFF_FFFF | ((u32::from(polarity)) << 31))
    }

    fn variable(self) -> Variable {
        self.0 & 0x7FFF_FFFF
    }

    fn polarity(self) -> bool {
        (self.0 >> 31) != 0
    }

    fn negated(self) -> Self {
        Self(self.0 & 0x7FFF_FFFF)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct StructLiteral {
    value: u32,
    polarity: bool,
}

impl Literal for StructLiteral {
    fn new(var: Variable, polarity: bool) -> Self {
        Self {
            value: var,
            polarity,
        }
    }
    fn variable(self) -> Variable {
        self.value
    }

    fn polarity(self) -> bool {
        self.polarity
    }

    #[must_use]
    fn negated(self) -> Self {
        Self {
            value: self.value,
            polarity: !self.polarity,
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct DoubleLiteral(u32);

impl Literal for DoubleLiteral {
    fn new(var: Variable, polarity: bool) -> Self {
        if polarity {
            Self(var * 2)
        } else {
            Self(var * 2 + 1)
        }
    }

    fn variable(self) -> Variable {
        self.0 / 2
    }

    fn polarity(self) -> bool {
        self.0 % 2 != 0
    }

    fn negated(self) -> Self {
        if self.polarity() {
            Self(self.0 + 1)
        } else {
            Self(self.0 - 1)
        }
    }
}

impl Neg for DoubleLiteral {
    type Output = Self;

    fn neg(self) -> Self::Output {
        self.negated()
    }
}

impl Not for DoubleLiteral {
    type Output = Self;

    fn not(self) -> Self::Output {
        self.negated()
    }
}

impl Neg for &DoubleLiteral {
    type Output = DoubleLiteral;

    fn neg(self) -> Self::Output {
        self.negated()
    }
}

impl Not for &DoubleLiteral {
    type Output = DoubleLiteral;

    fn not(self) -> Self::Output {
        self.negated()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct NegativeLiteral(i32);

impl Literal for NegativeLiteral {
    fn new(var: Variable, polarity: bool) -> Self {
        let var = i32::try_from(var).expect("negative literal variable overflowed");

        if polarity {
            Self(var)
        } else {
            Self(-var)
        }
    }

    fn variable(self) -> Variable {
        self.0.unsigned_abs()
    }

    fn polarity(self) -> bool {
        self.0.is_positive()
    }

    fn negated(self) -> Self {
        Self(-self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_literal_neg() {
        assert_eq!(
            PackedLiteral::new(1, false).negated(),
            PackedLiteral::new(1, true)
        );
        assert_eq!(
            PackedLiteral::new(1, true).negated(),
            PackedLiteral::new(1, false)
        );
    }
}
