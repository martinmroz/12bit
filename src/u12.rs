
use std::marker;
use std::ops::Add;

// TODO: mm: Implement from_str_radix()

#[derive(Debug,Clone,Copy,PartialEq,Eq,PartialOrd,Ord)]
pub struct U12(u16);

// MARK: - Public Constants

pub const MAX: U12 = U12(0xFFF);
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
  pub fn checked_add(self, other: Self) -> Option<Self> {
    match self.0 + other.0 {
      result @ 0...4095 => Some(U12(result)),
      _ => None
    }
  }

  /// Saturating integer addition. 
  /// Computes `self + other`, saturating at the numeric bounds instead of overflowing.
  pub fn saturating_add(self, other: Self) -> Self {
    match self.0 + other.0 {
      result @ 0...4095 => U12(result),
      _ => Self::max_value()
    }
  }

  /// Wrapping (modular) addition. 
  /// Computes `self + other`, wrapping around at the boundary of the type.
  pub fn wrapping_add(self, other: Self) -> Self {
    U12((self.0 + other.0) & 0xFFF)
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
  ($from:path) => {
    impl FailableInto<U12> for $from {
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

// MARK: - Default Value

impl Default for U12 {
  fn default() -> Self {
    U12::min_value()
  }
}

// MARK: - Add

impl Add<U12> for U12 {
  type Output = U12;
  fn add(self, other: U12) -> Self::Output {
    match self.checked_add(other) {
      Some(result) => result,
      None => panic!("arithmetic overflow")
    }
  }
}

impl<'a> Add<U12> for &'a U12 {
  type Output = U12;
  fn add(self, other: U12) -> Self::Output {
    (*self).add(other)
  }
}

impl<'a> Add<&'a U12> for U12 {
  type Output = U12;
  fn add(self, other: &'a U12) -> Self::Output {
    self.add(*other)
  }
}

impl<'a,'b> Add<&'a U12> for &'b U12 {
  type Output = U12;
  fn add(self, other: &'a U12) -> Self::Output {
    (*self).add(*other)
  }
}
