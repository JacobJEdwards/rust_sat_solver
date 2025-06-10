#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
//! Defines literals, the fundamental building blocks of clauses in SAT formulas.
//!
//! A literal is either a propositional variable (e.g. `x`) or its negation (e.g. `!x`).
//! This module provides:
//! - A `Variable` type alias (typically `u32`) for identifying propositional variables.
//! - The `Literal` trait, which defines the common interface for literal representations.
//!   This allows different data structures to represent literals while adhering to a
//!   consistent API for accessing their variable, polarity, and performing operations
//!   like negation.
//! - Several concrete implementations of the `Literal` trait:
//!   - `PackedLiteral`: A memory-efficient representation storing the variable and polarity
//!     within a single `u32` using bit manipulation.
//!   - `StructLiteral`: A straightforward representation using a struct with separate fields
//!     for variable and polarity.
//!   - `DoubleLiteral`: Represents a literal `L` as `2*variable_index(L) + polarity_bit(L)`.
//!     This is a common encoding for mapping literals to unique `usize` indices.
//!   - `NegativeLiteral`: Represents literals using signed integers, similar to the DIMACS format
//!     (e.g. `x` as `variable_id`, `!x` as `-variable_id`).
//! - A utility function `convert` to transform a literal of one type into another.

use clap::ValueEnum;
use std::fmt::{Debug, Display};
use std::hash::Hash;

/// Type alias for representing a propositional variable identifier.
///
/// Variables are typically identified by non-negative integers.
/// `u32` provides a large range, suitable for most practical SAT instances.
pub type Variable = u32;

/// Trait defining the common interface for literal representations.
///
/// A literal is a propositional variable or its negation.
/// This trait allows for different underlying data structures while providing
/// consistent methods for:
/// - Creating a new literal from a variable ID and its polarity.
/// - Accessing the variable ID of the literal.
/// - Accessing the polarity of the literal (true for positive, false for negative).
/// - Negating the literal.
/// - Converting to/from `i32` (DIMACS-like representation).
/// - Converting to/from a `usize` index (useful for array lookups).
pub trait Literal:
    Copy + Debug + Eq + Hash + Default + Ord + PartialOrd + PartialEq + Send + Sync
{
    /// Creates a new literal.
    ///
    /// # Arguments
    ///
    /// * `var`: The `Variable` identifier.
    /// * `polarity`: The polarity of the literal. Conventionally:
    ///   - `true` indicates a positive literal (e.g. `x_var`).
    ///   - `false` indicates a negative literal (e.g. `!x_var`).
    fn new(var: Variable, polarity: bool) -> Self;

    /// Returns the `Variable` identifier of this literal.
    fn variable(self) -> Variable;

    /// Returns the polarity of this literal.
    ///
    /// Convention:
    /// - `true` for a positive literal (e.g. `x_i`).
    /// - `false` for a negative literal (e.g. `!x_i`).
    fn polarity(self) -> bool;

    /// Returns the negated version of this literal.
    /// If `self` is `x_i`, returns `!x_i`.
    /// If `self` is `!x_i`, returns `x_i`.
    #[must_use]
    fn negated(self) -> Self;

    /// Checks if the literal is negated (i.e. has negative polarity).
    /// This is equivalent to `!self.polarity()`.
    fn is_negated(self) -> bool {
        !self.polarity()
    }

    /// Checks if the literal is positive (i.e. has positive polarity).
    /// This is equivalent to `self.polarity()`.
    fn is_positive(self) -> bool {
        self.polarity()
    }

    /// Creates a literal from an `i32` value (DIMACS-style).
    ///
    /// A positive `value` `v` becomes a positive literal for variable `v`.
    /// A negative `value` `-v` becomes a negative literal for variable `v`.
    /// Variable `0` is not part of the DIMACS standard for literals and its handling
    /// here depends on `Self::new` if `value.unsigned_abs()` is 0.
    ///
    /// # Arguments
    ///
    /// * `value`: The `i32` representing the literal.
    #[must_use]
    fn from_i32(value: i32) -> Self {
        let polarity = value.is_positive();
        let var = value.unsigned_abs();
        Self::new(var, polarity)
    }

    /// Converts the literal to its `i32` (DIMACS-style) representation.
    /// Positive literal `x_v` becomes `v` (as `i32`).
    /// Negative literal `!x_v` becomes `-v` (as `i32`).
    ///
    /// # Panics
    ///
    /// `self.variable() as i32` may panic if `self.variable()` (a `u32`) is too large
    /// to fit in an `i32` (i.e. > `i32::MAX`). `clippy::cast_possible_wrap` is allowed.
    fn to_i32(&self) -> i32 {
        #[allow(clippy::cast_possible_wrap)]
        let var_signed = self.variable() as i32;
        if self.polarity() {
            var_signed
        } else {
            -var_signed
        }
    }

    /// Converts the literal to a `usize` index.
    ///
    /// This is used for direct array indexing (e.g. in watch lists or vsids lists).
    /// A common mapping is `2*variable_id + polarity_bit`, where `polarity_bit` is
    /// 0 for one polarity and 1 for the other.
    /// This default implementation uses `polarity_bit = 1` for positive (`polarity() == true`)
    /// and `0` for negative (`polarity() == false`).
    /// So, for variable `v`:
    /// - `!v` (polarity=false) -> `2*v + 0`
    /// - ` v` (polarity=true)  -> `2*v + 1`
    fn index(self) -> usize {
        let polarity_bit = usize::from(self.polarity());
        let var_usize = self.variable() as usize;
        var_usize.wrapping_mul(2).wrapping_add(polarity_bit)
    }

    /// Creates a literal from a `usize` index.
    /// This is the inverse of `self.index()`.
    ///
    /// # Arguments
    ///
    /// * `index`: The `usize` index representing the literal.
    ///
    /// # Panics
    ///
    /// `var as Variable` (where `var` is `usize`) may panic if `var` is too large to fit
    /// in `Variable` (a `u32`). `clippy::cast_possible_truncation` is allowed.
    #[must_use]
    fn from_index(index: usize) -> Self {
        let polarity = (index % 2) != 0;
        let var_usize = index / 2;
        #[allow(clippy::cast_possible_truncation)]
        Self::new(var_usize as Variable, polarity)
    }
}

/// A memory-efficient literal representation using bit packing within a `u32`.
///
/// The lowest 31 bits store the variable ID, and the most significant bit (MSB)
/// stores the polarity.
/// - Variable ID: `self.0 & 0x7FFF_FFFF` (masks out the MSB). Max variable ID is `2^31 - 1`.
/// - Polarity: `(self.0 >> 31) != 0`. `1` for positive, `0` for negative.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct PackedLiteral(u32);

/// Mask to extract the variable ID (lowest 31 bits).
const VAR_MASK: u32 = 0x7FFF_FFFF;
/// Left shift amount to move the polarity bit to the MSB position.
const LSHIFT: u32 = 31;

impl Literal for PackedLiteral {
    /// Creates a new `PackedLiteral`. O(1) complexity.
    /// `var` is masked to fit in 31 bits.
    /// `polarity` (bool) is converted to `u32` (0 or 1) and shifted to the MSB.
    #[inline]
    fn new(var: Variable, polarity: bool) -> Self {
        Self((var & VAR_MASK) | (u32::from(polarity) << LSHIFT))
    }

    /// Extracts the variable ID. O(1) complexity.
    #[inline]
    fn variable(self) -> Variable {
        self.0 & VAR_MASK
    }

    /// Extracts the polarity. O(1) complexity.
    /// Returns `true` if MSB is 1 (positive), `false` if MSB is 0 (negative).
    #[inline]
    fn polarity(self) -> bool {
        (self.0 >> LSHIFT) != 0
    }

    /// Negates the literal by flipping the polarity bit (MSB). O(1) complexity.
    #[inline]
    fn negated(self) -> Self {
        Self(self.0 ^ (1 << LSHIFT))
    }
}

/// A straightforward literal representation using a struct.
///
/// Stores the variable ID and polarity in separate fields.
/// Less memory-efficient than `PackedLiteral` if not optimised well by the compiler,
/// but very clear.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct StructLiteral {
    /// The variable identifier.
    value: u32,
    /// The polarity (true for positive, false for negative).
    polarity: bool,
}

impl Literal for StructLiteral {
    #[inline]
    fn new(var: Variable, polarity: bool) -> Self {
        Self {
            value: var,
            polarity,
        }
    }
    #[inline]
    fn variable(self) -> Variable {
        self.value
    }

    #[inline]
    fn polarity(self) -> bool {
        self.polarity
    }

    #[inline]
    fn negated(self) -> Self {
        Self {
            value: self.value,
            polarity: !self.polarity,
        }
    }
}

/// A literal representation where the literal is encoded as `2*var_id + polarity_bit`.
///
/// This encoding directly matches the `index()` method's logic.
/// Polarity bit: `1` for positive, `0` for negative (if `polarity()` is true for positive).
/// So, `polarity()` `true` -> `val % 2 == 1`.
/// `polarity()` `false` -> `val % 2 == 0`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct DoubleLiteral(u32);

impl Literal for DoubleLiteral {
    /// Creates a new `DoubleLiteral`.
    /// `var * 2 + (1 if polarity is true else 0)`.
    #[inline]
    fn new(var: Variable, polarity: bool) -> Self {
        Self(var.wrapping_mul(2).wrapping_add(u32::from(polarity)))
    }

    /// Extracts the variable ID: `self.0 / 2`.
    #[inline]
    fn variable(self) -> Variable {
        self.0 / 2
    }

    /// Extracts the polarity: `self.0 % 2 != 0`.
    /// (True if odd, meaning polarity bit was 1).
    #[inline]
    fn polarity(self) -> bool {
        (self.0 % 2) != 0
    }

    /// Negates the literal by flipping the LSB (polarity bit).
    /// `(2v+p) XOR 1` results in `2v + (p XOR 1)`.
    #[inline]
    fn negated(self) -> Self {
        Self(self.0 ^ 1)
    }

    /// The internal `u32` value is already the index.
    #[inline]
    fn index(self) -> usize {
        self.0 as usize
    }
}

/// A literal representation using a signed `i32`, similar to DIMACS format.
///
/// Positive `var_id` for `x_var_id`.
/// Negative `-var_id` for `!x_var_id`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct NegativeLiteral(i32);

impl Literal for NegativeLiteral {
    /// Creates a new `NegativeLiteral`.
    /// If `polarity` is true (positive literal), stores `var` as positive `i32`.
    /// If `polarity` is false (negative literal), stores `var` as negative `i32`.
    #[inline]
    fn new(var: Variable, polarity: bool) -> Self {
        #[allow(clippy::cast_possible_wrap)]
        let var = var as i32;
        let p = i32::from(!polarity); // 1 if polarity is false, 0 if true.
        let var = var * (1 - 2 * p);
        Self(var)
    }

    /// Extracts the variable ID (always positive).
    #[inline]
    fn variable(self) -> Variable {
        self.0.unsigned_abs() // Returns u32.
    }

    /// Extracts the polarity. True if `self.0` is positive.
    #[inline]
    fn polarity(self) -> bool {
        self.0.is_positive()
    }

    /// Negates the literal by flipping the sign of the stored `i32`.
    #[inline]
    fn negated(self) -> Self {
        Self(-self.0)
    }
}

/// Converts a literal of one type (`T`) into a literal of another type (`U`).
///
/// This function extracts the variable and polarity from the source literal `lit`
/// and uses them to construct a new literal of the target type `U`.
///
/// # Type Parameters
///
/// * `T`: The source `Literal` type.
/// * `U`: The target `Literal` type.
///
/// # Arguments
///
/// * `lit`: A reference to the source literal of type `T`.
///
/// # Returns
///
/// A new literal of type `U` with the same variable and polarity as `lit`.
pub fn convert<T: Literal, U: Literal>(lit: &T) -> U {
    let var = lit.variable();
    let polarity = lit.polarity();
    U::new(var, polarity)
}

/// Represents a literal that can be one of several implementations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LiteralImpls {
    /// A packed literal using bit manipulation for memory efficiency.
    Packed(PackedLiteral),
    /// A struct-based literal with separate fields for variable and polarity.
    Struct(StructLiteral),
    /// A double literal represented as `2*variable + polarity_bit`.
    Double(DoubleLiteral),
    /// A negative literal represented as a signed integer (DIMACS-style).
    Negative(NegativeLiteral),
}

impl Default for LiteralImpls {
    fn default() -> Self {
        Self::Double(DoubleLiteral::default())
    }
}

impl Literal for LiteralImpls {
    fn new(var: Variable, polarity: bool) -> Self {
        Self::Packed(PackedLiteral::new(var, polarity))
    }

    fn variable(self) -> Variable {
        match self {
            Self::Packed(lit) => lit.variable(),
            Self::Struct(lit) => lit.variable(),
            Self::Double(lit) => lit.variable(),
            Self::Negative(lit) => lit.variable(),
        }
    }

    fn polarity(self) -> bool {
        match self {
            Self::Packed(lit) => lit.polarity(),
            Self::Struct(lit) => lit.polarity(),
            Self::Double(lit) => lit.polarity(),
            Self::Negative(lit) => lit.polarity(),
        }
    }

    fn negated(self) -> Self {
        match self {
            Self::Packed(lit) => Self::Packed(lit.negated()),
            Self::Struct(lit) => Self::Struct(lit.negated()),
            Self::Double(lit) => Self::Double(lit.negated()),
            Self::Negative(lit) => Self::Negative(lit.negated()),
        }
    }
}

/// Represents the type of literal implementation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default, ValueEnum)]
pub enum LiteralType {
    /// A packed literal using bit manipulation for memory efficiency.
    Packed,
    /// A struct-based literal with separate fields for variable and polarity.
    Struct,
    /// A double literal represented as `2*variable + polarity_bit`.
    #[default]
    Double,
    /// A negative literal represented as a signed integer (DIMACS-style).
    Negative,
}

impl Display for LiteralType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Packed => write!(f, "packed"),
            Self::Struct => write!(f, "struct"),
            Self::Double => write!(f, "double"),
            Self::Negative => write!(f, "negative"),
        }
    }
}

impl LiteralType {
    /// Converts a `LiteralType` to its corresponding `Literal` implementation.
    ///
    /// # Arguments
    ///
    /// * `var`: The variable identifier for the literal.
    /// * `polarity`: The polarity of the literal (true for positive, false for negative).
    ///
    /// # Returns
    ///
    /// A new literal of the specified type.
    #[allow(dead_code)]
    #[must_use]
    pub fn to_impl(self, var: Variable, polarity: bool) -> LiteralImpls {
        match self {
            Self::Packed => LiteralImpls::Packed(PackedLiteral::new(var, polarity)),
            Self::Struct => LiteralImpls::Struct(StructLiteral::new(var, polarity)),
            Self::Double => LiteralImpls::Double(DoubleLiteral::new(var, polarity)),
            Self::Negative => LiteralImpls::Negative(NegativeLiteral::new(var, polarity)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_literal_implementation<L: Literal + 'static>(var_id: Variable, initial_polarity: bool) {
        let lit = L::new(var_id, initial_polarity);
        assert_eq!(lit.variable(), var_id, "Variable ID mismatch");
        assert_eq!(
            lit.polarity(),
            initial_polarity,
            "Initial polarity mismatch"
        );

        if initial_polarity {
            assert!(lit.is_positive(), "Should be positive");
            assert!(!lit.is_negated(), "Should not be negated");
        } else {
            assert!(!lit.is_positive(), "Should not be positive");
            assert!(lit.is_negated(), "Should be negated");
        }

        let neg_lit = lit.negated();
        assert_eq!(
            neg_lit.variable(),
            var_id,
            "Variable ID mismatch after negation"
        );
        assert_eq!(
            neg_lit.polarity(),
            !initial_polarity,
            "Polarity should flip after negation"
        );

        let double_neg_lit = neg_lit.negated();
        assert_eq!(
            double_neg_lit.variable(),
            var_id,
            "Variable ID mismatch after double negation"
        );
        assert_eq!(
            double_neg_lit.polarity(),
            initial_polarity,
            "Polarity should revert after double negation"
        );
        assert_eq!(
            double_neg_lit, lit,
            "Double negation should return original literal"
        );

        let i32_val = lit.to_i32();
        let lit_from_i32 = L::from_i32(i32_val);
        assert_eq!(
            lit_from_i32, lit,
            "from_i32(to_i32(lit)) should be lit. Got: L={lit:?}, i32={i32_val}, L'={lit_from_i32:?}"
        );

        #[allow(
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss,
            clippy::cast_possible_wrap
        )]
        let expected_i32_val = if initial_polarity {
            var_id as i32
        } else {
            -(var_id as i32)
        };
        if var_id == 0 && !initial_polarity {
            if var_id != 0 {
                assert_eq!(
                    i32_val, expected_i32_val,
                    "to_i32() value incorrect. Expected {expected_i32_val}, Got {i32_val}"
                );
            }
        } else {
            assert_eq!(
                i32_val, expected_i32_val,
                "to_i32() value incorrect. Expected {expected_i32_val}, Got {i32_val}"
            );
        }

        if std::any::TypeId::of::<L>() != std::any::TypeId::of::<DoubleLiteral>() {
            let idx = lit.index();
            let lit_from_idx = L::from_index(idx);
            assert_eq!(lit_from_idx, lit, "from_index(index(lit)) should be lit");
        }
    }

    #[test]
    fn test_all_literal_implementations() {
        let test_cases = [
            (1u32, true),
            (1u32, false),
            (VAR_MASK, true),
            (VAR_MASK, false),
            (12345u32, true),
            (67890u32, false),
        ];

        for &(var_id, polarity) in &test_cases {
            let packed_var_id = var_id & VAR_MASK;

            test_literal_implementation::<PackedLiteral>(packed_var_id, polarity);
            test_literal_implementation::<StructLiteral>(var_id, polarity);
            test_literal_implementation::<DoubleLiteral>(var_id, polarity);
            if var_id != 0 {
                test_literal_implementation::<NegativeLiteral>(var_id, polarity);
            }
        }
    }

    #[test]
    fn test_double_literal_index() {
        let lit_pos = DoubleLiteral::new(5, true); // 2*5 + 1 = 11
        assert_eq!(lit_pos.index(), 11);
        assert_eq!(DoubleLiteral::from_index(11), lit_pos);

        let lit_neg = DoubleLiteral::new(5, false); // 2*5 + 0 = 10
        assert_eq!(lit_neg.index(), 10);
        assert_eq!(DoubleLiteral::from_index(10), lit_neg);
    }

    #[test]
    fn test_literal_negation_consistency() {
        assert_eq!(
            PackedLiteral::new(1, false).negated().negated(),
            PackedLiteral::new(1, false)
        );
        assert_eq!(
            PackedLiteral::new(1, true).negated().negated(),
            PackedLiteral::new(1, true)
        );

        assert_eq!(
            StructLiteral::new(1, false).negated().negated(),
            StructLiteral::new(1, false)
        );
        assert_eq!(
            StructLiteral::new(1, true).negated().negated(),
            StructLiteral::new(1, true)
        );

        assert_eq!(
            DoubleLiteral::new(1, false).negated().negated(),
            DoubleLiteral::new(1, false)
        );
        assert_eq!(
            DoubleLiteral::new(1, true).negated().negated(),
            DoubleLiteral::new(1, true)
        );

        assert_eq!(
            NegativeLiteral::new(1, false).negated().negated(),
            NegativeLiteral::new(1, false)
        );
        assert_eq!(
            NegativeLiteral::new(1, true).negated().negated(),
            NegativeLiteral::new(1, true)
        );
    }

    #[test]
    fn test_conversion_function() {
        let p_lit = PackedLiteral::new(10, true);
        let s_lit: StructLiteral = convert(&p_lit);
        assert_eq!(s_lit.variable(), 10);
        assert!(s_lit.polarity());

        let d_lit: DoubleLiteral = convert(&s_lit);
        assert_eq!(d_lit.variable(), 10);
        assert!(d_lit.polarity());

        let n_lit: NegativeLiteral = convert(&d_lit);
        assert_eq!(n_lit.variable(), 10);
        assert!(n_lit.polarity());

        let p_lit_again: PackedLiteral = convert(&n_lit);
        assert_eq!(p_lit_again, p_lit);
    }
}
