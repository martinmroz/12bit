
use std::marker;

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

  /// Shifts the bits to the left by a specified amount, `n`, wrapping the 
  /// truncated bits to the end of the resulting integer.
  pub fn rotate_left(self, n: u32) -> Self {
    let rotate_left_once = |x: Self| {
      let value = x.0;
      let shifted_left = value << 1;
      let shifted_out = if shifted_left > 0xFFF { 1u16 } else { 0u16 };
      U12((shifted_left & 0xFFF) | shifted_out)
    };

    // Rotate self the specified number of times.
    let mut result = self;
    for _ in 0 .. n { result = rotate_left_once(result); }
    result
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
pub trait FailableAs<T> where Self: marker::Sized, T: marker::Sized {

  /// Returns the receiver as `Some(T)` if non-truncating, or `None`.
  fn failable_as(self) -> Option<T>;

  /// Returns the receiver as `T` by using `convert_as()` and unwrapping the result.
  ///
  /// # Panics
  /// This method will panic if `convert_as` fails.
  fn unchecked_failable_as(self) -> T {
    self.failable_as().unwrap()
  }

}

/// Implements FailableAs<U12> for the specified type.
macro_rules! impl_failable_as_u12 {
  ($from:path) => {
    impl FailableAs<U12> for $from {
      fn failable_as(self) -> Option<U12> {
        if self > 0xFFF {
          None
        } else {
          Some(U12(self as u16))
        }
      }
    }
  }
}

impl_failable_as_u12!(u16);
impl_failable_as_u12!(u32);
impl_failable_as_u12!(u64);
impl_failable_as_u12!(usize);

// MARK: - Default Value

impl Default for U12 {
  fn default() -> Self {
    U12::min_value()
  }
}
