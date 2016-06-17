
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
  let zero = U12::min_value();
  let  one = U12::from(1u8);
  let  two = U12::from(2u8);
  let  max = U12::max_value();

  assert_eq!(zero.checked_add(zero), Some(zero));
  assert_eq!(zero.checked_add(one), Some(one));
  assert_eq!(one.checked_add(zero), Some(one));
  assert_eq!(zero.checked_add(max), Some(max));
  assert_eq!(max.checked_add(zero), Some(max));
  assert_eq!(max.checked_add(one), None);
  assert_eq!(max.checked_add(two), None);
  assert_eq!(max.checked_add(max), None);
}

#[test]
fn test_saturating_add() {
  let zero = U12::min_value();
  let  one = U12::from(1u8);
  let  two = U12::from(2u8);
  let  max = U12::max_value();

  assert_eq!(zero.saturating_add(zero), zero);
  assert_eq!(zero.saturating_add(one), one);
  assert_eq!(one.saturating_add(zero), one);
  assert_eq!(zero.saturating_add(max), max);
  assert_eq!(max.saturating_add(zero), max);
  assert_eq!(max.saturating_add(one), max);
  assert_eq!(max.saturating_add(two), max);
  assert_eq!(max.saturating_add(max), max);
}

#[test]
fn test_wrapping_add() {
  let zero = U12::min_value();
  let  one = U12::from(1u8);
  let  two = U12::from(2u8);
  let  max = U12::max_value();

  assert_eq!(zero.wrapping_add(zero), zero);
  assert_eq!(zero.wrapping_add(one), one);
  assert_eq!(one.wrapping_add(zero), one);
  assert_eq!(zero.wrapping_add(max), max);
  assert_eq!(max.wrapping_add(zero), max);
  assert_eq!(max.wrapping_add(one), zero);
  assert_eq!(max.wrapping_add(two), one);
  assert_eq!(max.wrapping_add(max), 0xFFEu16.unchecked_into());
}

#[test]
fn test_overflowing_add() {
  let zero = U12::min_value();
  let  one = U12::from(1u8);
  let  two = U12::from(2u8);
  let  max = U12::max_value();

  assert_eq!(zero.overflowing_add(zero), (zero, false));
  assert_eq!(zero.overflowing_add(one), (one, false));
  assert_eq!(one.overflowing_add(zero), (one, false));
  assert_eq!(zero.overflowing_add(max), (max, false));
  assert_eq!(max.overflowing_add(zero), (max, false));
  assert_eq!(max.overflowing_add(one), (zero, true));
  assert_eq!(max.overflowing_add(two), (one, true));
  assert_eq!(max.overflowing_add(max), (0xFFEu16.unchecked_into(), true));
}

// MARK: - Tests - Subtraction

#[test]
fn test_sub_operator() {
  let zero = U12::min_value();
  let  one = U12::from(1u8);
  let  max = U12::max_value();

  assert_eq!(zero - zero, zero);
  assert_eq!(one - zero, one);
  assert_eq!(max - zero, max);
  assert_eq!(max - one, (0xFFE as u16).unchecked_into());
}

#[test]
#[should_panic]
fn test_sub_operator_underflow() {
  let one = U12::from(1u8);
  let min = U12::min_value();
  let _ = min - one;
}

#[test]
fn test_checked_sub() {
  let zero = U12::min_value();
  let  one = U12::from(1u8);
  let  two = U12::from(2u8);
  let  max = U12::max_value();

  assert_eq!(zero.checked_sub(zero), Some(zero));
  assert_eq!(zero.checked_sub(one), None);
  assert_eq!(one.checked_sub(zero), Some(one));
  assert_eq!(zero.checked_sub(max), None);
  assert_eq!(max.checked_sub(zero), Some(max));
  assert_eq!(max.checked_sub(one), Some((0xFFE as u16).unchecked_into()));
  assert_eq!(max.checked_sub(two), Some((0xFFD as u16).unchecked_into()));
  assert_eq!(max.checked_sub(max), Some(zero));
}

#[test]
fn test_saturating_sub() {
  let zero = U12::min_value();
  let  one = U12::from(1u8);
  let  two = U12::from(2u8);
  let  max = U12::max_value();

  assert_eq!(zero.saturating_sub(zero), zero);
  assert_eq!(zero.saturating_sub(one), zero);
  assert_eq!(one.saturating_sub(zero), one);
  assert_eq!(zero.saturating_sub(max), zero);
  assert_eq!(max.saturating_sub(zero), max);
  assert_eq!(max.saturating_sub(one), (0xFFE as u16).unchecked_into());
  assert_eq!(max.saturating_sub(two), (0xFFD as u16).unchecked_into());
  assert_eq!(max.saturating_sub(max), zero);
}

#[test]
fn test_wrapping_sub() {
  let zero = U12::min_value();
  let  one = U12::from(1u8);
  let  two = U12::from(2u8);
  let  max = U12::max_value();

  assert_eq!(zero.wrapping_sub(zero), zero);
  assert_eq!(zero.wrapping_sub(one), max);
  assert_eq!(one.saturating_sub(zero), one);
  assert_eq!(zero.wrapping_sub(max), one);
  assert_eq!(max.wrapping_sub(zero), max);
  assert_eq!(max.wrapping_sub(one), (0xFFE as u16).unchecked_into());
  assert_eq!(max.wrapping_sub(two), (0xFFD as u16).unchecked_into());
  assert_eq!(max.wrapping_sub(max), zero);
}

// MARK: - Tests - Multiplication

#[test]
fn test_mul_operator() {
  assert_eq!(U12::from(2u8) * U12::from(0u8), U12::min_value());
  assert_eq!(U12::max_value() * U12::min_value(), U12::min_value());
  assert_eq!(U12::from(2u8) * U12::from(255u8), (510 as u16).unchecked_into());
  assert_eq!(U12::from(255u8) * U12::from(2u8), (510 as u16).unchecked_into());
}

#[test]
#[should_panic]
fn test_mul_operator_overflow() {
  let _ = U12::from(2u8) * 2048u16.unchecked_into();
}

#[test]
fn test_checked_mul() {
  assert_eq!(U12::from(2u8).checked_mul(0u8.into()), Some(U12::min_value()));
  assert_eq!(U12::from(2u8).checked_mul(255u8.into()), Some((510 as u16).unchecked_into()));
  assert_eq!(U12::from(255u8).checked_mul(2u8.into()), Some((510 as u16).unchecked_into()));
  assert_eq!(U12::from(2u8).checked_mul((2048u16).unchecked_into()), None);
  assert_eq!(U12::from(2u8).checked_mul((4095u16).unchecked_into()), None);
}

#[test]
fn test_saturating_mul() {
  assert_eq!(U12::from(2u8).saturating_mul(0u8.into()), U12::min_value());
  assert_eq!(U12::from(2u8).saturating_mul(255u8.into()), (510 as u16).unchecked_into());
  assert_eq!(U12::from(255u8).saturating_mul(2u8.into()), (510 as u16).unchecked_into());
  assert_eq!(U12::from(2u8).saturating_mul((2048u16).unchecked_into()), U12::max_value());
  assert_eq!(U12::from(2u8).saturating_mul((4095u16).unchecked_into()), U12::max_value());
}

#[test]
fn test_wrapping_mul() {
  assert_eq!(U12::from(2u8).wrapping_mul(0u8.into()), U12::min_value());
  assert_eq!(U12::from(2u8).wrapping_mul(255u8.into()), (510 as u16).unchecked_into());
  assert_eq!(U12::from(255u8).wrapping_mul(2u8.into()), (510 as u16).unchecked_into());
  assert_eq!(U12::from(2u8).wrapping_mul((2048u16).unchecked_into()), U12::min_value());
  assert_eq!(U12::from(2u8).wrapping_mul((4095u16).unchecked_into()), (0xFFE as u16).unchecked_into());
}

// MARK: - Tests - Division

#[test]
fn test_div_operator() {
  assert_eq!(U12::max_value() / U12::max_value(), U12::from(1u8));
  assert_eq!(U12::from(2u8) / U12::from(255u8), U12::from(0u8));
  assert_eq!(U12::from(255u8) / U12::from(2u8), U12::from(127u8));
}

#[test]
#[should_panic]
fn test_div_operator_divide_by_zero() {
  let _ = U12::from(2u8) / U12::from(0u8);
}

#[test]
fn test_checked_div() {
  assert_eq!(U12::max_value().checked_div(U12::max_value()), Some(U12::from(1u8)));
  assert_eq!(U12::from(2u8).checked_div(U12::from(255u8)), Some(U12::from(0u8)));
  assert_eq!(U12::from(255u8).checked_div(U12::from(2u8)), Some(U12::from(127u8)));
  assert_eq!(U12::from(255u8).checked_div(U12::from(1u8)), Some(U12::from(255u8)));
  assert_eq!(U12::from(255u8).checked_div(U12::from(0u8)), None);
}

#[test]
fn test_wrapping_div() {
  assert_eq!(U12::max_value().wrapping_div(U12::max_value()), U12::from(1u8));
  assert_eq!(U12::from(2u8).wrapping_div(U12::from(255u8)), U12::from(0u8));
  assert_eq!(U12::from(255u8).wrapping_div(U12::from(2u8)), U12::from(127u8));
  assert_eq!(U12::from(255u8).wrapping_div(U12::from(1u8)), U12::from(255u8));
}

#[test]
#[should_panic]
fn test_wrapping_div_overflow() {
  let _ = U12::from(255u8).wrapping_div(U12::from(0u8));
}

// MARK: - Tests - Negation

#[test]
fn test_checked_neg() {
  assert_eq!(U12::from(0u8).checked_neg(), Some(0u8.into()));
  assert_eq!(U12::from(1u8).checked_neg(), None);
  assert_eq!(U12::from(2u8).checked_neg(), None);
  assert_eq!(U12::from(255u8).checked_neg(), None);
}

#[test]
fn test_wrapping_neg() {
  assert_eq!(U12::from(0u8).wrapping_neg(), 0u8.into());
  assert_eq!(U12::from(1u8).wrapping_neg(), 0xFFFu16.unchecked_into());
  assert_eq!(U12::from(2u8).wrapping_neg(), 0xFFEu16.unchecked_into());
  assert_eq!(U12::from(255u8).wrapping_neg(), 0xF01u16.unchecked_into());
}

#[test]
fn test_overflowing_neg() {
  assert_eq!(U12::from(0u8).overflowing_neg(), (0u8.into(), false));
  assert_eq!(U12::from(1u8).overflowing_neg(), (0xFFFu16.unchecked_into(), true));
  assert_eq!(U12::from(2u8).overflowing_neg(), (0xFFEu16.unchecked_into(), true));
  assert_eq!(U12::from(255u8).overflowing_neg(), (0xF01u16.unchecked_into(), true));
}
