
extern crate twelve_bit;

use twelve_bit::u12::*;

// MARK: - Tests - Non-Failable Conversions - From Smaller Types

#[test]
fn test_from_u8() {
  assert_eq!(u16::from(U12::from(0u8)), 0u16);
  assert_eq!(u16::from(U12::from(15u8)), 15u16);
  assert_eq!(u16::from(U12::from(255u8)), 255u16);
}

// MARK: - Tests - Non-Failable Conversions - Into Larger Types

#[test]
fn test_into_larger_types() {
  let into_16_max: u16 = U12::max_value().into();
  let into_16_min: u16 = U12::min_value().into();
  assert_eq!(into_16_max, 4095u16);
  assert_eq!(into_16_min, 0u16);

  let into_32_max: u32 = U12::max_value().into();
  let into_32_min: u32 = U12::min_value().into();
  assert_eq!(into_32_max, 4095u32);
  assert_eq!(into_32_min, 0u32);

  let into_64_max: u64 = U12::max_value().into();
  let into_64_min: u64 = U12::min_value().into();
  assert_eq!(into_64_max, 4095u64);
  assert_eq!(into_64_min, 0u64);

  let into_usize_max: usize = U12::max_value().into();
  let into_usize_min: usize = U12::min_value().into();
  assert_eq!(into_usize_max, 4095usize);
  assert_eq!(into_usize_min, 0usize);
}

// MARK: - Tests - Failable Conversions - From Larger Types

#[test]
fn test_failable_into_with_u16() {
  assert_eq!(0u16.failable_into(), Some(U12::min_value()));
  assert_eq!(0u16.unchecked_into(), U12::min_value());
  assert_eq!(15u16.failable_into(), Some(U12::from(15)));
  assert_eq!(15u16.unchecked_into(), U12::from(15));
  assert_eq!(4096u16.failable_into(), None);
  assert_eq!(u16::max_value().failable_into(), None);
}

#[test]
#[should_panic]
fn test_unchecked_into_with_u16() {
  let _ = 4096u16.unchecked_into();
}

#[test]
fn test_failable_into_with_u32() {
  assert_eq!(0u32.failable_into(), Some(U12::min_value()));
  assert_eq!(0u32.unchecked_into(), U12::min_value());
  assert_eq!(15u32.failable_into(), Some(U12::from(15u8)));
  assert_eq!(15u32.unchecked_into(), U12::from(15));
  assert_eq!(4096u32.failable_into(), None);
  assert_eq!(u32::max_value().failable_into(), None);
}

#[test]
#[should_panic]
fn test_unchecked_into_with_u32() {
  let _ = 4096u32.unchecked_into();
}

#[test]
fn test_failable_into_with_u64() {
  assert_eq!(0u64.failable_into(), Some(U12::min_value()));
  assert_eq!(0u64.unchecked_into(), U12::min_value());
  assert_eq!(15u64.failable_into(), Some(U12::from(15u8)));
  assert_eq!(15u64.unchecked_into(), U12::from(15));
  assert_eq!(4096u64.failable_into(), None);
  assert_eq!(u64::max_value().failable_into(), None);
}

#[test]
#[should_panic]
fn test_unchecked_into_with_u64() {
  let _ = 4096u64.unchecked_into();
}

#[test]
fn test_failable_into_with_usize() {
  assert_eq!(0usize.failable_into(), Some(U12::min_value()));
  assert_eq!(0usize.unchecked_into(), U12::min_value());
  assert_eq!(15usize.failable_into(), Some(U12::from(15u8)));
  assert_eq!(15usize.unchecked_into(), U12::from(15));
  assert_eq!(4096usize.failable_into(), None);
  assert_eq!(usize::max_value().failable_into(), None);
}

#[test]
#[should_panic]
fn test_unchecked_into_with_usize() {
  let _ = 4096usize.unchecked_into();
}

// MARK: - Tests - Default Value

#[test]
fn test_default() {
  assert_eq!(U12::default(), U12::min_value());
}

// MARK: - Tests - Addition

#[test]
fn test_add_operator() {
  let zero = U12::min_value();
  let  one = U12::from(1u8);
  let  max = U12::max_value();

  assert_eq!(zero + zero, zero);
  assert_eq!(zero + one, one);
  assert_eq!(one + zero, one);
  assert_eq!(zero + max, max);
  assert_eq!(max + zero, max);
}

#[test]
#[should_panic]
fn test_add_operator_overflow() {
  let one = U12::from(1u8);
  let max = U12::max_value();
  let _ = max + one;
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
