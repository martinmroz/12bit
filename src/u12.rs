
use std::marker;
use std::ops::{Add, Div, Mul, Not, Sub};

#[derive(Debug,Clone,Copy,PartialEq,Eq,PartialOrd,Ord)]
pub struct U12(u16);

// MARK: - Literal Macro

/// Creates a 12-bit value via unchecked-into conversion.
/// This is primarily to simplify describing U12 literal values, as the
/// `$x` parameter is first bound to a 16-bit value. This eliminates the need
/// for the caller to specify the type of the literal and does compile-time
/// validation that no literal greater than `0xFFFF` is specified; this
/// will panic for values in `0x1000...0xFFFF`.
#[macro_export]
macro_rules! u12 {
  ( $x:expr ) => {{
    let x: u16 = $x;
    x.unchecked_into()
  }}
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
  pub fn count_ones(self) -> u32 {
    self.0.count_ones()
  }

  /// Returns the number of zeros in the binary representation of `self`.
  pub fn count_zeros(self) -> u32 {
    self.0.count_zeros() - 4
  }

  /// Returns the number of leading zeros in the binary representation of `self`.
  pub fn leading_zeros(self) -> u32 {
    self.0.leading_zeros() - 4
  }

  /// Returns the number of trailing zeros in the binary representation of `self`.
  pub fn trailing_zeros(self) -> u32 {
    self.0.trailing_zeros()
  }

  /// Checked integer addition. 
  /// Computes `self + other`, returning `None` if overflow occurred.
  ///
  /// # Examples
  /// Basic usage:
  /// 
  /// ```
  /// use twelve_bit::u12::U12;
  ///
  /// assert_eq!(U12::from(1u8).checked_add(1u8.into()), Some(U12::from(2u8)));
  /// assert_eq!(U12::max_value().checked_add(1u8.into()), None);
  /// ```
  pub fn checked_add(self, other: Self) -> Option<Self> {
    match self.0 + other.0 {
      result @ 0...4095 => Some(U12(result)),
      _ => None
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
      result @ 0...4095 => U12(result),
      _ => Self::max_value()
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
              None => (self.wrapping_add(other), true)
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
    match self.0.checked_sub(other.0) {
      Some(value) => Some(U12(value)),
      None => None
    }
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
      _ => None
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
      _ => Self::max_value()
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

  /// Checked integer division.
  /// Computes `self / other`,  returning None if other == 0 or the operation results in underflow or overflow.
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
    match self.0.checked_div(other.0) {
      Some(small) => Some(U12(small)),
      _ => None
    }
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
      _ => None
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
      _ => (self.wrapping_neg(), true)
    }
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
  }
}

impl_from_u12!(u16);
impl_from_u12!(u32);
impl_from_u12!(u64);
impl_from_u12!(usize);

// MARK: - Failable Conversions - From Larger Types

/// Trait for implementing failable conversions in a generic way.
pub trait FailableInto<T> where Self: marker::Sized, T: marker::Sized {

  /// Returns the receiver as `Some(T)` if non-truncating, or `None`.
  fn failable_into(self) -> Option<T>;

  /// Returns the receiver as `T` by using `convert_as()` and unwrapping the result.
  ///
  /// # Panics
  /// This method will panic if `convert_as` fails.
  fn unchecked_into(self) -> T {
    self.failable_into().unwrap()
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
  }
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

    /// Implementation of U12.op(U12) -> U12.
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

    /// Implementation of (&'a U12).op(U12) -> U12.
    impl<'a> $trait_name<U12> for &'a U12 {
      type Output = U12;
      fn $trait_method(self, other: U12) -> Self::Output {
        (*self).$trait_method(other)
      }
    }

    /// Implementation of U12.op(&'a U12) -> U12.
    impl<'a> $trait_name<&'a U12> for U12 {
      type Output = U12;
      fn $trait_method(self, other: &'a U12) -> Self::Output {
        self.$trait_method(*other)
      }
    }

    /// Implementation of (&'a U12).op(&'b U12) -> U12.
    impl<'a,'b> $trait_name<&'a U12> for &'b U12 {
      type Output = U12;
      fn $trait_method(self, other: &'a U12) -> Self::Output {
        (*self).$trait_method(*other)
      }
    }

  }
}

impl_arithmetic_trait_family_for_u12!(Add, add, checked_add, "arithmetic overflow");
impl_arithmetic_trait_family_for_u12!(Sub, sub, checked_sub, "arithmetic underflow");
impl_arithmetic_trait_family_for_u12!(Mul, mul, checked_mul, "arithmetic overflow");
impl_arithmetic_trait_family_for_u12!(Div, div, checked_div, "arithmetic exception");

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
