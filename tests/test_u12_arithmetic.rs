
#[macro_use]
extern crate twelve_bit;

use twelve_bit::u12::*;

// MARK: - Tests - Addition

#[test]
fn test_add_operator() {
  assert_eq!(u12![0] + u12![0], u12![0]);
  assert_eq!(u12![0] + u12![1], u12![1]);
  assert_eq!(u12![1] + u12![0], u12![1]);
  assert_eq!(u12![0] + U12::max_value(), U12::max_value());
  assert_eq!(U12::max_value() + u12![0], U12::max_value());
}

#[test]
#[should_panic]
fn test_add_operator_overflow() {
  let _ = U12::max_value() + u12![1];
}

#[test]
fn test_checked_add() {
  assert_eq!(u12![0].checked_add(u12![0]), Some(u12![0]));
  assert_eq!(u12![0].checked_add(u12![1]), Some(u12![1]));
  assert_eq!(u12![1].checked_add(u12![0]), Some(u12![1]));
  assert_eq!(u12![0].checked_add(U12::max_value()), Some(U12::max_value()));
  assert_eq!(U12::max_value().checked_add(u12![0]), Some(U12::max_value()));
  assert_eq!(U12::max_value().checked_add(u12![1]), None);
  assert_eq!(U12::max_value().checked_add(u12![2]), None);
  assert_eq!(U12::max_value().checked_add(U12::max_value()), None);
}

#[test]
fn test_saturating_add() {
  assert_eq!(u12![0].saturating_add(u12![0]), u12![0]);
  assert_eq!(u12![0].saturating_add(u12![1]), u12![1]);
  assert_eq!(u12![1].saturating_add(u12![0]), u12![1]);
  assert_eq!(u12![0].saturating_add(U12::max_value()), U12::max_value());
  assert_eq!(U12::max_value().saturating_add(u12![0]), U12::max_value());
  assert_eq!(U12::max_value().saturating_add(u12![1]), U12::max_value());
  assert_eq!(U12::max_value().saturating_add(u12![2]), U12::max_value());
  assert_eq!(U12::max_value().saturating_add(U12::max_value()), U12::max_value());
}

#[test]
fn test_wrapping_add() {
  assert_eq!(u12![0].wrapping_add(u12![0]), u12![0]);
  assert_eq!(u12![0].wrapping_add(u12![1]), u12![1]);
  assert_eq!(u12![1].wrapping_add(u12![0]), u12![1]);
  assert_eq!(u12![0].wrapping_add(U12::max_value()), U12::max_value());
  assert_eq!(U12::max_value().wrapping_add(u12![0]), U12::max_value());
  assert_eq!(U12::max_value().wrapping_add(u12![1]), u12![0]);
  assert_eq!(U12::max_value().wrapping_add(u12![2]), u12![1]);
  assert_eq!(U12::max_value().wrapping_add(U12::max_value()), u12![0xFFE]);
}

#[test]
fn test_overflowing_add() {
  assert_eq!(u12![0].overflowing_add(u12![0]), (u12![0], false));
  assert_eq!(u12![0].overflowing_add(u12![1]), (u12![1], false));
  assert_eq!(u12![1].overflowing_add(u12![0]), (u12![1], false));
  assert_eq!(u12![0].overflowing_add(U12::max_value()), (U12::max_value(), false));
  assert_eq!(U12::max_value().overflowing_add(u12![0]), (U12::max_value(), false));
  assert_eq!(U12::max_value().overflowing_add(u12![1]), (u12![0], true));
  assert_eq!(U12::max_value().overflowing_add(u12![2]), (u12![1], true));
  assert_eq!(U12::max_value().overflowing_add(U12::max_value()), (u12![0xFFE], true));
}

// MARK: - Tests - Subtraction

#[test]
fn test_sub_operator() {
  assert_eq!(u12![0] - u12![0], u12![0]);
  assert_eq!(u12![1] - u12![0], u12![1]);
  assert_eq!(U12::max_value() - u12![0], U12::max_value());
  assert_eq!(U12::max_value() - u12![1], u12![0xFFE]);
}

#[test]
#[should_panic]
fn test_sub_operator_underflow() {
  let _ = U12::min_value() - u12![1];
}

#[test]
fn test_checked_sub() {
  assert_eq!(u12![0].checked_sub(u12![0]), Some(u12![0]));
  assert_eq!(u12![0].checked_sub(u12![1]), None);
  assert_eq!(u12![1].checked_sub(u12![0]), Some(u12![1]));
  assert_eq!(u12![0].checked_sub(U12::max_value()), None);
  assert_eq!(U12::max_value().checked_sub(u12![0]), Some(U12::max_value()));
  assert_eq!(U12::max_value().checked_sub(u12![1]), Some(u12![0xFFE]));
  assert_eq!(U12::max_value().checked_sub(u12![2]), Some(u12![0xFFD]));
  assert_eq!(U12::max_value().checked_sub(U12::max_value()), Some(u12![0]));
}

#[test]
fn test_saturating_sub() {
  assert_eq!(u12![0].saturating_sub(u12![0]), u12![0]);
  assert_eq!(u12![0].saturating_sub(u12![1]), u12![0]);
  assert_eq!(u12![1].saturating_sub(u12![0]), u12![1]);
  assert_eq!(u12![0].saturating_sub(U12::max_value()), u12![0]);
  assert_eq!(U12::max_value().saturating_sub(u12![0]), U12::max_value());
  assert_eq!(U12::max_value().saturating_sub(u12![1]), u12![0xFFE]);
  assert_eq!(U12::max_value().saturating_sub(u12![2]), u12![0xFFD]);
  assert_eq!(U12::max_value().saturating_sub(U12::max_value()), u12![0]);
}

#[test]
fn test_wrapping_sub() {
  assert_eq!(u12![0].wrapping_sub(u12![0]), u12![0]);
  assert_eq!(u12![0].wrapping_sub(u12![1]), U12::max_value());
  assert_eq!(u12![1].saturating_sub(u12![0]), u12![1]);
  assert_eq!(u12![0].wrapping_sub(U12::max_value()), u12![1]);
  assert_eq!(U12::max_value().wrapping_sub(u12![0]), U12::max_value());
  assert_eq!(U12::max_value().wrapping_sub(u12![1]), u12![0xFFE]);
  assert_eq!(U12::max_value().wrapping_sub(u12![2]), u12![0xFFD]);
  assert_eq!(U12::max_value().wrapping_sub(U12::max_value()), u12![0]);
}

// MARK: - Tests - Multiplication

#[test]
fn test_mul_operator() {
  assert_eq!(u12![2] * u12![0], U12::min_value());
  assert_eq!(U12::max_value() * U12::min_value(), U12::min_value());
  assert_eq!(u12![2] * u12![255], u12![510]);
  assert_eq!(u12![255] * u12![2], u12![510]);
}

#[test]
#[should_panic]
fn test_mul_operator_overflow() {
  let _ = u12![2] * u12![2048];
}

#[test]
fn test_checked_mul() {
  assert_eq!(u12![2].checked_mul(u12![0]), Some(U12::min_value()));
  assert_eq!(u12![2].checked_mul(u12![255]), Some(u12![510]));
  assert_eq!(u12![255].checked_mul(u12![2]), Some(u12![510]));
  assert_eq!(u12![2].checked_mul(u12![2048]), None);
  assert_eq!(u12![2].checked_mul(u12![4095]), None);
}

#[test]
fn test_saturating_mul() {
  assert_eq!(u12![2].saturating_mul(u12![0]), U12::min_value());
  assert_eq!(u12![2].saturating_mul(u12![255]), u12![510]);
  assert_eq!(u12![255].saturating_mul(u12![2]), u12![510]);
  assert_eq!(u12![2].saturating_mul(u12![2048]), U12::max_value());
  assert_eq!(u12![2].saturating_mul(u12![4095]), U12::max_value());
}

#[test]
fn test_wrapping_mul() {
  assert_eq!(u12![2].wrapping_mul(u12![0]), U12::min_value());
  assert_eq!(u12![2].wrapping_mul(u12![255]), u12![510]);
  assert_eq!(u12![255].wrapping_mul(u12![2]), u12![510]);
  assert_eq!(u12![2].wrapping_mul(u12![2048]), U12::min_value());
  assert_eq!(u12![2].wrapping_mul(u12![4095]), u12![0xFFE]);
}

// MARK: - Tests - Division

#[test]
fn test_div_operator() {
  assert_eq!(U12::max_value() / U12::max_value(), u12![1]);
  assert_eq!(u12![2] / u12![255], u12![0]);
  assert_eq!(u12![255] / u12![2], u12![127]);
}

#[test]
#[should_panic]
fn test_div_operator_divide_by_zero() {
  let _ = u12![2] / u12![0];
}

#[test]
fn test_checked_div() {
  assert_eq!(U12::max_value().checked_div(U12::max_value()), Some(u12![1]));
  assert_eq!(u12![2].checked_div(u12![255]), Some(u12![0]));
  assert_eq!(u12![255].checked_div(u12![2]), Some(u12![127]));
  assert_eq!(u12![255].checked_div(u12![1]), Some(u12![255]));
  assert_eq!(u12![255].checked_div(u12![0]), None);
}

#[test]
fn test_wrapping_div() {
  assert_eq!(U12::max_value().wrapping_div(U12::max_value()), u12![1]);
  assert_eq!(u12![2].wrapping_div(u12![255]), u12![0]);
  assert_eq!(u12![255].wrapping_div(u12![2]), u12![127]);
  assert_eq!(u12![255].wrapping_div(u12![1]), u12![255]);
}

#[test]
#[should_panic]
fn test_wrapping_div_overflow() {
  let _ = u12![255].wrapping_div(u12![0]);
}

// MARK: - Tests - Negation

#[test]
fn test_checked_neg() {
  assert_eq!(u12![0].checked_neg(), Some(u12![0]));
  assert_eq!(u12![1].checked_neg(), None);
  assert_eq!(u12![2].checked_neg(), None);
  assert_eq!(u12![255].checked_neg(), None);
}

#[test]
fn test_wrapping_neg() {
  assert_eq!(u12![0].wrapping_neg(), u12![0]);
  assert_eq!(u12![1].wrapping_neg(), u12![0xFFF]);
  assert_eq!(u12![2].wrapping_neg(), u12![0xFFE]);
  assert_eq!(u12![255].wrapping_neg(), u12![0xF01]);
}

#[test]
fn test_overflowing_neg() {
  assert_eq!(u12![0].overflowing_neg(), (u12![0], false));
  assert_eq!(u12![1].overflowing_neg(), (u12![0xFFF], true));
  assert_eq!(u12![2].overflowing_neg(), (u12![0xFFE], true));
  assert_eq!(u12![255].overflowing_neg(), (u12![0xF01], true));
}
