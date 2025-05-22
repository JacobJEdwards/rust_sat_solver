#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
use std::fmt::Debug;
use std::hash::Hash;

pub type Variable = u32;

/// Trait that defines the shape of a literal used in the formula
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

    fn to_i32(&self) -> i32 {
        #[allow(clippy::cast_possible_wrap)]
        let var = self.variable() as i32;
        let polarity = if self.polarity() { 1 } else { -1 };
        var * polarity
    }

    fn index(self) -> usize {
        let polarity = usize::from(self.polarity());
        let var = self.variable() as usize;
        var.wrapping_mul(2).wrapping_add(polarity)
    }

    #[must_use]
    fn from_index(index: usize) -> Self {
        let polarity = index % 2 != 0;
        let var = index / 2;
        #[allow(clippy::cast_possible_truncation)]
        Self::new(var as Variable, polarity)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct PackedLiteral(u32);

/// Extract the variable value
const VAR_MASK: u32 = 0x7FFF_FFFF;
/// How far to left shift to get to the polarity bit
const LSHIFT: u32 = 31;

impl Literal for PackedLiteral {
    /// O(1) creation
    fn new(var: Variable, polarity: bool) -> Self {
        Self(var & VAR_MASK | ((u32::from(polarity)) << LSHIFT))
    }

    /// O(1)
    fn variable(self) -> Variable {
        self.0 & VAR_MASK
    }

    /// O(1)
    fn polarity(self) -> bool {
        (self.0 >> LSHIFT) != 0
    }

    /// O(1)
    fn negated(self) -> Self {
        Self(self.0 ^ (1 << LSHIFT))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct StructLiteral {
    value: u32,
    polarity: bool,
}

/// Very simple implementation
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
        // Wrapping not needed, but wanted to not have overflow checks
        Self(var.wrapping_mul(2).wrapping_add(u32::from(polarity)))
    }

    fn variable(self) -> Variable {
        self.0 / 2
    }

    fn polarity(self) -> bool {
        self.0 % 2 != 0
    }

    fn negated(self) -> Self {
        Self(self.0 ^ 1)
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct NegativeLiteral(i32);

/// Intuitive implementation
impl Literal for NegativeLiteral {
    fn new(var: Variable, polarity: bool) -> Self {
        #[allow(clippy::cast_possible_wrap)]
        let var = var as i32;

        let p = i32::from(!polarity);
        Self(var * (1 - 2 * p))
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

pub fn convert<T: Literal, U: Literal>(lit: &T) -> U {
    let var = lit.variable();
    let polarity = lit.polarity();
    U::new(var, polarity)
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

        assert_eq!(
            StructLiteral::new(1, false).negated(),
            StructLiteral::new(1, true)
        );

        assert_eq!(
            StructLiteral::new(1, true).negated(),
            StructLiteral::new(1, false)
        );

        assert_eq!(
            DoubleLiteral::new(1, false).negated(),
            DoubleLiteral::new(1, true)
        );

        assert_eq!(
            DoubleLiteral::new(1, true).negated(),
            DoubleLiteral::new(1, false)
        );

        assert_eq!(
            NegativeLiteral::new(1, false).negated(),
            NegativeLiteral::new(1, true)
        );

        assert_eq!(
            NegativeLiteral::new(1, true).negated(),
            NegativeLiteral::new(1, false)
        );
    }
}
