//
// Copyright 2016 The u12 Developers. See the COPYRIGHT
// file at the top-level directory of this distribution.
//
// Licensed under the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>.
// All files in the project carrying such notice may not be copied, modified, or
// distributed except according to those terms.
//

use std::cmp;
use std::marker;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Not, Rem, Shl, Shr, Sub};

#[cfg(feature = "serde")]
mod serde;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct U12(u16);

// MARK: - Literal Macro

/// Creates a 12-bit value via unchecked-into conversion.
/// This is meant to simplify describing U12 literal values, as the
/// `$x` parameter is first bound to a 16-bit value. This allows the compiler to
/// elide the type of the literal, and does compile-time validation that no
/// literal greater than `0xFFFF` is specified; this will panic for values
/// in the range `0x1000...0xFFFF`.
///
/// # Examples
/// Basic usage:
///
/// ```rust
/// # #[macro_use] extern crate twelve_bit;
/// use twelve_bit::u12::*;
/// # fn main() {
/// assert_eq!(u12![0], U12::min_value());
/// assert_eq!(u12![4095], U12::max_value());
/// # }
/// ```
#[macro_export]
macro_rules! u12 {
    ( $x:expr ) => {{
        let x: u16 = $x;
        let value: U12 = x.unchecked_into();
        value
    }};
}

// MARK: - Public Constants

/// The largest value representable by the `U12` type.
pub const MAX: U12 = U12(0xFFF);

/// The smallest value representable by the `U12` type.
pub const MIN: U12 = U12(0x000);

// MARK: - Implementation

impl U12 {
    /// Returns the smallest value that can be represented by this integer type.
    pub fn min_value() -> Self {
        MIN
    }

    /// Returns the largest value that can be represented by this integer type.
    pub fn max_value() -> Self {
        MAX
    }

    /// Returns the number of ones in the binary representation of `self`.
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![0b000000000000].count_ones(), 0);
    /// assert_eq!(u12![0b001011111100].count_ones(), 7);
    /// assert_eq!(u12![0b111111111111].count_ones(), 12)
    /// # }
    /// ```
    pub fn count_ones(self) -> u32 {
        self.0.count_ones()
    }

    /// Returns the number of zeros in the binary representation of `self`.
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![0b000000000000].count_zeros(), 12);
    /// assert_eq!(u12![0b001011111000].count_zeros(), 6);
    /// assert_eq!(u12![0b111111111111].count_zeros(), 0)
    /// # }
    /// ```
    pub fn count_zeros(self) -> u32 {
        self.0.count_zeros() - 4
    }

    /// Returns the number of leading zeros in the binary representation of `self`.
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![0b111111111111].leading_zeros(), 0);
    /// assert_eq!(u12![0b001011111000].leading_zeros(), 2);
    /// assert_eq!(u12![0b000011111000].leading_zeros(), 4);
    /// assert_eq!(u12![0b000000000000].leading_zeros(), 12);
    /// # }
    /// ```
    pub fn leading_zeros(self) -> u32 {
        self.0.leading_zeros() - 4
    }

    /// Returns the number of trailing zeros in the binary representation of `self`.
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![0b111111111111].trailing_zeros(), 0);
    /// assert_eq!(u12![0b001011111000].trailing_zeros(), 3);
    /// assert_eq!(u12![0b001011110000].trailing_zeros(), 4);
    /// assert_eq!(u12![0b000000000000].trailing_zeros(), 12);
    /// # }
    /// ```
    pub fn trailing_zeros(self) -> u32 {
        cmp::min(self.0.trailing_zeros(), 12)
    }

    /// Checked integer addition.
    /// Computes `self + other`, returning `None` if overflow occurred.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![1].checked_add(u12![1]), Some(u12![2]));
    /// assert_eq!(U12::max_value().checked_add(u12![1]), None);
    /// # }
    /// ```
    pub fn checked_add(self, other: Self) -> Option<Self> {
        match self.0 + other.0 {
            result @ 0..=4095 => Some(U12(result)),
            _ => None,
        }
    }

    /// Saturating integer addition.
    /// Computes `self + other`, saturating at the numeric bounds instead of overflowing.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```
    /// use twelve_bit::u12::U12;
    ///
    /// assert_eq!(U12::from(1u8).saturating_add(1u8.into()), U12::from(2u8));
    /// assert_eq!(U12::max_value().saturating_add(1u8.into()), U12::max_value());
    /// ```
    pub fn saturating_add(self, other: Self) -> Self {
        match self.0 + other.0 {
            result @ 0..=4095 => U12(result),
            _ => Self::max_value(),
        }
    }

    /// Wrapping (modular) addition.
    /// Computes `self + other`, wrapping around at the boundary of the type.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```
    /// use twelve_bit::u12::U12;
    ///
    /// assert_eq!(U12::from(1u8).wrapping_add(1u8.into()), U12::from(2u8));
    /// assert_eq!(U12::max_value().wrapping_add(3u8.into()), U12::from(2u8));
    /// ```
    pub fn wrapping_add(self, other: Self) -> Self {
        U12((self.0 + other.0) & 0xFFF)
    }

    /// Overflowing addition.
    /// Computes `self + other`, returning a tuple of the addition along with a
    /// boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would have occurred then the wrapped value is returned.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```
    /// use twelve_bit::u12::U12;
    ///
    /// assert_eq!(U12::from(1u8).overflowing_add(1u8.into()), (U12::from(2u8), false));
    /// assert_eq!(U12::max_value().overflowing_add(3u8.into()), (U12::from(2u8), true));
    /// ```
    pub fn overflowing_add(self, other: Self) -> (Self, bool) {
        match self.checked_add(other) {
            Some(result) => (result, false),
            None => (self.wrapping_add(other), true),
        }
    }

    /// Checked integer subtraction.
    /// Computes `self - other`, returning `None` if underflow occurred.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```
    /// use twelve_bit::u12::U12;
    ///
    /// assert_eq!(U12::from(1u8).checked_sub(1u8.into()), Some(U12::from(0u8)));
    /// assert_eq!(U12::min_value().checked_sub(1u8.into()), None);
    /// ```
    pub fn checked_sub(self, other: Self) -> Option<Self> {
        self.0.checked_sub(other.0).map(|value| U12(value))
    }

    /// Saturating integer subtraction.
    /// Computes `self - other`, saturating at the numeric bounds instead of overflowing.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```
    /// use twelve_bit::u12::U12;
    ///
    /// assert_eq!(U12::from(1u8).saturating_sub(1u8.into()), U12::min_value());
    /// assert_eq!(U12::min_value().saturating_sub(5u8.into()), U12::min_value());
    /// ```
    pub fn saturating_sub(self, other: Self) -> Self {
        U12(self.0.saturating_sub(other.0))
    }

    /// Wrapping (modular) subtraction.
    /// Computes `self - other`, wrapping around at the boundary of the type.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```
    /// use twelve_bit::u12::*;
    ///
    /// assert_eq!(U12::from(1u8).wrapping_sub(1u8.into()), U12::min_value());
    /// assert_eq!(U12::min_value().wrapping_sub(5u8.into()), (0xFFB as u16).unchecked_into());
    /// ```
    pub fn wrapping_sub(self, other: Self) -> Self {
        U12(self.0.wrapping_sub(other.0) & 0xFFF)
    }

    /// Overflowing subtraction.
    /// Computes `self - other`, returning a tuple of the subtraction result along with a
    /// boolean indicating whether an arithmetic underflow would occur.
    /// If an underflow would have occurred then the wrapped value is returned.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```
    /// use twelve_bit::u12::*;
    ///
    /// assert_eq!(U12::from(1u8).overflowing_sub(1u8.into()), (U12::from(0u8), false));
    /// assert_eq!(U12::min_value().overflowing_sub(1u8.into()), (0xFFFu16.unchecked_into(), true));
    /// ```
    pub fn overflowing_sub(self, other: Self) -> (Self, bool) {
        match self.checked_sub(other) {
            Some(result) => (result, false),
            None => (self.wrapping_sub(other), true),
        }
    }

    /// Checked integer multiplication.
    /// Computes `self * other`, returning `None` if overflow occurred.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```
    /// use twelve_bit::u12::*;
    ///
    /// assert_eq!(U12::from(2u8).checked_mul(255u8.into()), Some((510 as u16).unchecked_into()));
    /// assert_eq!(U12::from(2u8).checked_mul((2048u16).unchecked_into()), None);
    /// assert_eq!(U12::from(2u8).checked_mul((4095u16).unchecked_into()), None);
    /// ```
    pub fn checked_mul(self, other: Self) -> Option<Self> {
        match self.0.checked_mul(other.0) {
            Some(small) if small < 4096 => Some(U12(small)),
            _ => None,
        }
    }

    /// Saturating integer multiplication.
    /// Computes `self * other`, saturating at the numeric bounds instead of overflowing.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```
    /// use twelve_bit::u12::*;
    ///
    /// assert_eq!(U12::from(2u8).saturating_mul(1u8.into()), 2u8.into());
    /// assert_eq!(U12::from(2u8).saturating_mul((2048u16).unchecked_into()), U12::max_value());
    /// assert_eq!(U12::from(2u8).saturating_mul((4095u16).unchecked_into()), U12::max_value());
    /// ```
    pub fn saturating_mul(self, other: Self) -> Self {
        match self.0.checked_mul(other.0) {
            Some(small) if small < 4096 => U12(small),
            _ => Self::max_value(),
        }
    }

    /// Wrapping (modular) multiplication.
    /// Computes `self * other`, wrapping around at the boundary of the type.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```
    /// use twelve_bit::u12::*;
    ///
    /// assert_eq!(U12::from(2u8).wrapping_mul(1u8.into()), 2u8.into());
    /// assert_eq!(U12::from(2u8).wrapping_mul((2048u16).unchecked_into()), 0u8.into());
    /// assert_eq!(U12::from(2u8).wrapping_mul((4095u16).unchecked_into()), (0xFFE as u16).unchecked_into());
    /// ```
    pub fn wrapping_mul(self, other: Self) -> Self {
        U12(self.0.wrapping_mul(other.0) & 0xFFF)
    }

    /// Overflowing multiplication.
    /// Returns a tuple of the multiplication along with a boolean indicating whether an arithmetic
    /// overflow would occur. If an overflow would have occurred then the wrapped value is returned.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![2].overflowing_mul(u12![1]), (u12![2], false));
    /// assert_eq!(u12![2].overflowing_mul(u12![2048]), (u12![0], true));
    /// assert_eq!(u12![2].overflowing_mul(u12![4095]), (u12![0xFFE], true));
    /// # }
    /// ```
    pub fn overflowing_mul(self, other: Self) -> (Self, bool) {
        match self.checked_mul(other) {
            Some(result) => (result, false),
            None => (self.wrapping_mul(other), true),
        }
    }

    /// Checked integer division.
    /// Computes `self / other`,  returning None if other == 0 or the operation results in
    /// underflow or overflow.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```
    /// use twelve_bit::u12::*;
    ///
    /// assert_eq!(U12::from(2u8).checked_div(0u8.into()), None);
    /// assert_eq!(U12::from(2u8).checked_div((2048u16).unchecked_into()), Some(U12::min_value()));
    /// assert_eq!(U12::from(2u8).checked_div(2u8.into()), Some(U12::from(1u8)));
    /// ```
    pub fn checked_div(self, other: Self) -> Option<Self> {
        self.0.checked_div(other.0).map(|small| U12(small))
    }

    /// Wrapping (modular) division.
    /// Computes self / other. Wrapped division on unsigned types is just normal division.
    /// There's no way wrapping could ever happen. This function exists, so that all operations
    /// are accounted for in the wrapping operations.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```
    /// use twelve_bit::u12::*;
    ///
    /// assert_eq!(U12::from(2u8).wrapping_div((2048u16).unchecked_into()), U12::min_value());
    /// assert_eq!(U12::from(2u8).wrapping_div(2u8.into()), U12::from(1u8));
    /// ```
    pub fn wrapping_div(self, other: Self) -> Self {
        U12(self.0.wrapping_div(other.0))
    }

    /// Calculates the divisor when the receiver is divided by `rhs`.
    /// Returns a tuple of the divisor along with a boolean indicating whether an arithmetic
    /// overflow would occur. Note that for unsigned integers overflow never occurs,
    /// so the second value is always false.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![2].overflowing_div(u12![1]), (u12![2], false));
    /// assert_eq!(u12![2048].overflowing_div(u12![2]), (u12![1024], false));
    /// assert_eq!(u12![4095].overflowing_div(u12![2]), (u12![2047], false));
    /// # }
    /// ```
    pub fn overflowing_div(self, other: Self) -> (Self, bool) {
        (self.wrapping_div(other), false)
    }

    /// Checked integer negation.
    /// Computes `-self`, returning `None` unless `self == 0`.
    /// Note that negating any positive integer will overflow.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```
    /// use twelve_bit::u12::*;
    ///
    /// assert_eq!(U12::from(0u8).checked_neg(), Some(0u8.into()));
    /// assert_eq!(U12::from(2u8).checked_neg(), None);
    /// ```
    pub fn checked_neg(self) -> Option<Self> {
        match self.0 {
            0 => Some(self),
            _ => None,
        }
    }

    /// Wrapping (modular) negation.
    /// Computes `-self`, wrapping around at the boundary of the type.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```
    /// use twelve_bit::u12::*;
    ///
    /// assert_eq!(U12::from(2u8).wrapping_neg(), 0xFFEu16.unchecked_into());
    /// assert_eq!(U12::from(255u8).wrapping_neg(), 0xF01u16.unchecked_into());
    /// ```
    pub fn wrapping_neg(self) -> Self {
        U12(self.0.wrapping_neg() & 0xFFF)
    }

    /// Negates self in an overflowing fashion.
    /// Returns `!self + 1` using wrapping operations to return the value that
    /// represents the negation of this unsigned value. Note that for positive
    /// unsigned values overflow always occurs, but negating `0` does not overflow.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```
    /// use twelve_bit::u12::*;
    ///
    /// assert_eq!(U12::from(0u8).overflowing_neg(), (0u8.into(), false));
    /// assert_eq!(U12::from(2u8).overflowing_neg(), (0xFFEu16.unchecked_into(), true));
    /// ```
    pub fn overflowing_neg(self) -> (U12, bool) {
        match self.0 {
            0 => (self, false),
            _ => (self.wrapping_neg(), true),
        }
    }

    /// Checked integer remainder.
    /// Computes `self % other`, returning `None` if `other == 0` or the
    /// operation results in underflow or overflow.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![5].checked_rem(u12![2]), Some(u12![1]));
    /// assert_eq!(u12![5].checked_rem(u12![0]), None);
    /// # }
    /// ```
    pub fn checked_rem(self, other: Self) -> Option<Self> {
        self.0.checked_rem(other.0).map(|value| U12(value))
    }

    /// Wrapping (modular) integer remainder.
    /// Computes `self % other`. Wrapped remainder calculation on unsigned types
    /// is just the regular remainder calculation. There's no way wrapping could ever
    /// happen. This function exists, so that all operations are accounted for in the
    /// wrapping operations.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![100].wrapping_rem(u12![10]), u12![0]);
    /// # }
    /// ```
    pub fn wrapping_rem(self, other: Self) -> Self {
        U12(self.0.wrapping_rem(other.0))
    }

    /// Calculates the remainder when `self` is divided by `other`.
    /// Returns a tuple of the remainder after dividing along with a boolean indicating
    /// whether an arithmetic overflow would occur. Note that for unsigned integers
    /// overflow never occurs, so the second value is always false.
    ///
    /// # Panics
    /// This function will panic if `other` is `0`.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![5].overflowing_rem(u12![2]), (u12![1], false));
    /// # }
    /// ```
    pub fn overflowing_rem(self, other: Self) -> (Self, bool) {
        let (result, overflow) = self.0.overflowing_rem(other.0);
        (U12(result), overflow)
    }

    /// Checked shift left.
    /// Computes `self << rhs`, returning `None` if `rhs` is larger than or equal to
    /// the number of bits in the receiver.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![0b000000000001].checked_shl(12), None);
    /// assert_eq!(u12![0b000000000001].checked_shl(1), Some(u12![0b000000000010]));
    /// assert_eq!(u12![0b000000000001].checked_shl(11), Some(u12![0b100000000000]));
    /// # }
    /// ```
    pub fn checked_shl(self, rhs: u32) -> Option<Self> {
        if rhs >= 12 {
            None
        } else {
            self.0.checked_shl(rhs).map(|value| U12(value))
        }
    }

    /// Panic-free bitwise shift-left; yields `self << mask(rhs)`, where mask removes any
    /// high-order bits of rhs that would cause the shift to exceed the bitwidth of the type.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![0b000000000001].wrapping_shl(12), u12![0b000000000001]);
    /// assert_eq!(u12![0b000000000001].wrapping_shl( 1), u12![0b000000000010]);
    /// assert_eq!(u12![0b000000000001].wrapping_shl(11), u12![0b100000000000]);
    /// # }
    /// ```
    pub fn wrapping_shl(self, rhs: u32) -> Self {
        self.checked_shl(rhs % 12).unwrap()
    }

    /// Shifts self left by rhs bits.
    /// Returns a tuple of the shifted version of the receiver along with a boolean
    /// indicating whether the shift value was larger than or equal to the number of
    /// bits. If the shift value is too large, then value is masked `(N-1)` where N
    /// is the number of bits, and this value is then used to perform the shift.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![0b000000000001].overflowing_shl(12), (u12![0b000000000001], true));
    /// assert_eq!(u12![0b000000000001].overflowing_shl( 1), (u12![0b000000000010], false));
    /// assert_eq!(u12![0b000000000001].overflowing_shl(11), (u12![0b100000000000], false));
    /// # }
    /// ```
    pub fn overflowing_shl(self, rhs: u32) -> (Self, bool) {
        (self.wrapping_shl(rhs), rhs >= 12)
    }

    /// Checked shift right.
    /// Computes `self >> rhs`, returning `None` if `rhs` is larger than or
    /// equal to the number of bits in the receiver.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![0b100000000000].checked_shr(12), None);
    /// assert_eq!(u12![0b100000000000].checked_shr( 1), Some(u12![0b010000000000]));
    /// assert_eq!(u12![0b100000000000].checked_shr(11), Some(u12![0b000000000001]));
    /// # }
    /// ```
    pub fn checked_shr(self, rhs: u32) -> Option<Self> {
        if rhs >= 12 {
            None
        } else {
            self.0.checked_shr(rhs).map(|value| U12(value))
        }
    }

    /// Panic-free bitwise shift-right; yields `self >> mask(rhs)`, where mask removes any
    /// high-order bits of rhs that would cause the shift to exceed the bitwidth of the type.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![0b100000000000].wrapping_shr(12), u12![0b100000000000]);
    /// assert_eq!(u12![0b100000000000].wrapping_shr( 1), u12![0b010000000000]);
    /// assert_eq!(u12![0b100000000000].wrapping_shr(11), u12![0b000000000001]);
    /// # }
    /// ```
    pub fn wrapping_shr(self, rhs: u32) -> Self {
        self.checked_shr(rhs % 12).unwrap()
    }

    /// Shifts the receiver right by `rhs` bits.
    /// Returns a tuple of the shifted version of self along with a boolean indicating
    /// whether the shift value was larger than or equal to the number of bits.
    /// If the shift value is too large, then value is masked `(N-1)` where `N` is the
    /// number of bits, and this value is then used to perform the shift.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![0b100000000000].overflowing_shr(12), (u12![0b100000000000], true));
    /// assert_eq!(u12![0b100000000000].overflowing_shr( 1), (u12![0b010000000000], false));
    /// assert_eq!(u12![0b100000000000].overflowing_shr(11), (u12![0b000000000001], false));
    /// # }
    /// ```
    pub fn overflowing_shr(self, rhs: u32) -> (Self, bool) {
        (self.wrapping_shr(rhs), rhs >= 12)
    }

    /// Checked bitwise-and of the receiver with `rhs`.
    /// Computes `self & rhs`. This method cannot fail.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![0b111100001111].checked_bitand(u12![0b111100000000]), Some(u12![0b111100000000]));
    /// # }
    /// ```
    pub fn checked_bitand(self, rhs: Self) -> Option<Self> {
        Some(U12(self.0.bitand(rhs.0)))
    }

    /// Checked bitwise-or of the receiver with `rhs`.
    /// Computes `self | rhs`. This method cannot fail.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![0b111100001111].checked_bitor(u12![0b111100000000]), Some(u12![0b111100001111]));
    /// # }
    /// ```
    pub fn checked_bitor(self, rhs: Self) -> Option<Self> {
        Some(U12(self.0.bitor(rhs.0)))
    }

    /// Checked bitwise-xor of the receiver with `rhs`.
    /// Computes `self ^ rhs`. This method cannot fail.
    ///
    /// # Examples
    /// Basic usage:
    ///
    /// ```rust
    /// # #[macro_use] extern crate twelve_bit;
    /// use twelve_bit::u12::*;
    /// # fn main() {
    /// assert_eq!(u12![0b111100001111].checked_bitxor(u12![0b111100000000]), Some(u12![0b000000001111]));
    /// # }
    /// ```
    pub fn checked_bitxor(self, rhs: Self) -> Option<Self> {
        Some(U12(self.0.bitxor(rhs.0)))
    }
}

// MARK: - Non-Failable Conversions - From Smaller Types

impl From<u8> for U12 {
    fn from(small: u8) -> Self {
        U12(small as u16)
    }
}

// MARK: - Non-Failable Conversions - Into Larger Types

/// Implements From<U12> for the specified type.
macro_rules! impl_from_u12 {
    ($result:path) => {
        impl From<U12> for $result {
            fn from(small: U12) -> Self {
                small.0 as Self
            }
        }
    };
}

impl_from_u12!(u16);
impl_from_u12!(u32);
impl_from_u12!(u64);
impl_from_u12!(usize);

// MARK: - Failable Conversions - From Larger Types

/// Trait for implementing failable conversions in a generic way.
pub trait FailableInto<T>
where
    Self: marker::Sized,
    T: marker::Sized,
{
    /// Returns the receiver as `Some(T)` if non-truncating, or `None`.
    fn failable_into(self) -> Option<T>;

    /// Returns the receiver as `T` by using `failable_into()` and unwrapping the result.
    ///
    /// # Panics
    /// This method will panic if `failable_into` fails.
    fn unchecked_into(self) -> T {
        match self.failable_into() {
            Some(value) => value,
            None => panic!("unchecked conversion failed"),
        }
    }
}

/// Implements FailableAs<U12> for the specified type.
macro_rules! impl_failable_into_u12 {
    ($source_type:path) => {
        impl FailableInto<U12> for $source_type {
            fn failable_into(self) -> Option<U12> {
                if self > 0xFFF {
                    None
                } else {
                    Some(U12(self as u16))
                }
            }
        }
    };
}

impl_failable_into_u12!(u16);
impl_failable_into_u12!(u32);
impl_failable_into_u12!(u64);
impl_failable_into_u12!(usize);

// MARK: - Default

impl Default for U12 {
    fn default() -> Self {
        U12::min_value()
    }
}

// MARK: - Arithmetic Operator Traits (Add, Sub, Mul, Div)

///
/// Implements an arithmetic trait family for `U12`. This macro generates
/// implementations for an arithmetic trait `$trait_name` such that the
/// it is possible to invoke `$trait_method` on all of `U12.op(U12)`, `(&'a U12).op(U12)`,
/// `U12.op(&'a U12)` and `(&'a U12).op(&'b U12)`. The implementation calls through to
/// `$checked_method` on U12. If the `$checked_method` returns `None`, the
/// trait panics with the message specified as `$message`.
///
macro_rules! impl_arithmetic_trait_family_for_u12 {
    ($trait_name:ident, $trait_method:ident, $checked_method:ident, $message:expr) => {
        // Implementation of U12.op(U12) -> U12.
        impl $trait_name<U12> for U12 {
            type Output = U12;
            fn $trait_method(self, other: U12) -> Self::Output {
                match self.$checked_method(other) {
                    Some(result) => result,
                    None => {
                        panic!($message)
                    }
                }
            }
        }

        // Implementation of (&'a U12).op(U12) -> U12.
        impl<'a> $trait_name<U12> for &'a U12 {
            type Output = U12;
            fn $trait_method(self, other: U12) -> Self::Output {
                (*self).$trait_method(other)
            }
        }

        // Implementation of U12.op(&'a U12) -> U12.
        impl<'a> $trait_name<&'a U12> for U12 {
            type Output = U12;
            fn $trait_method(self, other: &'a U12) -> Self::Output {
                self.$trait_method(*other)
            }
        }

        // Implementation of (&'a U12).op(&'b U12) -> U12.
        impl<'a, 'b> $trait_name<&'a U12> for &'b U12 {
            type Output = U12;
            fn $trait_method(self, other: &'a U12) -> Self::Output {
                (*self).$trait_method(*other)
            }
        }
    };
}

impl_arithmetic_trait_family_for_u12!(Add, add, checked_add, "arithmetic overflow");
impl_arithmetic_trait_family_for_u12!(Sub, sub, checked_sub, "arithmetic underflow");
impl_arithmetic_trait_family_for_u12!(Mul, mul, checked_mul, "arithmetic overflow");
impl_arithmetic_trait_family_for_u12!(Div, div, checked_div, "arithmetic exception");
impl_arithmetic_trait_family_for_u12!(Rem, rem, checked_rem, "arithmetic exception");

// MARK: - Not

impl Not for U12 {
    type Output = U12;
    fn not(self) -> Self::Output {
        U12((!self.0) & 0xFFF)
    }
}

impl<'a> Not for &'a U12 {
    type Output = U12;
    fn not(self) -> Self::Output {
        (*self).not()
    }
}

// MARK: - Bitwise Operations

macro_rules! impl_bitwise_trait_family_for_u12 {
    ($trait_name:ident, $trait_method:ident, $checked_method:ident) => {
        impl_arithmetic_trait_family_for_u12!(
            $trait_name,
            $trait_method,
            $checked_method,
            "<unreachable>"
        );
    };
}

impl_bitwise_trait_family_for_u12!(BitAnd, bitand, checked_bitand);
impl_bitwise_trait_family_for_u12!(BitOr, bitor, checked_bitor);
impl_bitwise_trait_family_for_u12!(BitXor, bitxor, checked_bitxor);

// MARK: - Logic Operations

///
/// Implements an logic trait family for `U12`. This macro generates
/// implementations for an arithmetic trait `$trait_name` such that the
/// it is possible to invoke `$trait_method` on all of `U12.op($rhs_type)`, `(&'a U12).op($rhs_type)`,
/// `U12.op(&'a $rhs_type)` and `(&'a U12).op(&'b $rhs_type)`. The implementation calls through to
/// `$checked_method` on U12. If the RHS value represented as a 64-bit number exceeds
/// 12, the implementation panics with the specified `$message`.
///
macro_rules! impl_shift_trait_family_for_u12 {
    ($rhs_type:ident, $trait_name:ident, $trait_method:ident, $checked_method:ident, $message:expr) => {
        // Implementation of U12.op($rhs_type) -> U12.
        impl $trait_name<$rhs_type> for U12 {
            type Output = U12;
            fn $trait_method(self, other: $rhs_type) -> Self::Output {
                if (other as u64) > (u32::max_value() as u64) {
                    panic!($message)
                } else {
                    match self.$checked_method(other as u32) {
                        Some(result) => result,
                        None => {
                            panic!($message)
                        }
                    }
                }
            }
        }

        // Implementation of (&'a U12).op($rhs_type) -> U12.
        impl<'a> $trait_name<$rhs_type> for &'a U12 {
            type Output = U12;
            fn $trait_method(self, other: $rhs_type) -> Self::Output {
                (*self).$trait_method(other)
            }
        }

        // Implementation of U12.op(&'a $rhs_type) -> U12.
        impl<'a> $trait_name<&'a $rhs_type> for U12 {
            type Output = U12;
            fn $trait_method(self, other: &'a $rhs_type) -> Self::Output {
                self.$trait_method(*other)
            }
        }

        // Implementation of (&'a U12).op(&'b $rhs_type) -> U12.
        impl<'a, 'b> $trait_name<&'a $rhs_type> for &'b U12 {
            type Output = U12;
            fn $trait_method(self, other: &'a $rhs_type) -> Self::Output {
                (*self).$trait_method(*other)
            }
        }
    };
}

// TODO: mm: Implement Shl<U12>

impl_shift_trait_family_for_u12!(u8, Shl, shl, checked_shl, "logic overflow");
impl_shift_trait_family_for_u12!(i8, Shl, shl, checked_shl, "logic overflow");
impl_shift_trait_family_for_u12!(u16, Shl, shl, checked_shl, "logic overflow");
impl_shift_trait_family_for_u12!(i16, Shl, shl, checked_shl, "logic overflow");
impl_shift_trait_family_for_u12!(u32, Shl, shl, checked_shl, "logic overflow");
impl_shift_trait_family_for_u12!(i32, Shl, shl, checked_shl, "logic overflow");
impl_shift_trait_family_for_u12!(u64, Shl, shl, checked_shl, "logic overflow");
impl_shift_trait_family_for_u12!(i64, Shl, shl, checked_shl, "logic overflow");
impl_shift_trait_family_for_u12!(usize, Shl, shl, checked_shl, "logic overflow");
impl_shift_trait_family_for_u12!(isize, Shl, shl, checked_shl, "logic overflow");

// TODO: mm: Implement Shr<U12>

impl_shift_trait_family_for_u12!(u8, Shr, shr, checked_shr, "logic underflow");
impl_shift_trait_family_for_u12!(i8, Shr, shr, checked_shr, "logic underflow");
impl_shift_trait_family_for_u12!(u16, Shr, shr, checked_shr, "logic underflow");
impl_shift_trait_family_for_u12!(i16, Shr, shr, checked_shr, "logic underflow");
impl_shift_trait_family_for_u12!(u32, Shr, shr, checked_shr, "logic underflow");
impl_shift_trait_family_for_u12!(i32, Shr, shr, checked_shr, "logic underflow");
impl_shift_trait_family_for_u12!(u64, Shr, shr, checked_shr, "logic underflow");
impl_shift_trait_family_for_u12!(i64, Shr, shr, checked_shr, "logic underflow");
impl_shift_trait_family_for_u12!(usize, Shr, shr, checked_shr, "logic underflow");
impl_shift_trait_family_for_u12!(isize, Shr, shr, checked_shr, "logic underflow");
