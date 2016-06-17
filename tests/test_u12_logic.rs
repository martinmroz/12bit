
#[macro_use]
extern crate twelve_bit;

use twelve_bit::u12::*;

// MARK: - Tests - Not

#[test]
fn test_not() {
  assert_eq!(! u12![0b000000000000], u12![0b111111111111]);
  assert_eq!(! u12![0b000000001111], u12![0b111111110000]);
  assert_eq!(! u12![0b000011111111], u12![0b111100000000]);
  assert_eq!(! u12![0b111111111111], u12![0b000000000000]);
}

#[test]
fn test_checked_shl() {
  assert_eq!(u12![0b000000000001].checked_shl( 0), Some(u12![0b000000000001]));
  assert_eq!(u12![0b000000000001].checked_shl( 1), Some(u12![0b000000000010]));
  assert_eq!(u12![0b000000000001].checked_shl( 2), Some(u12![0b000000000100]));
  assert_eq!(u12![0b000000000001].checked_shl( 3), Some(u12![0b000000001000]));
  assert_eq!(u12![0b000000000001].checked_shl( 4), Some(u12![0b000000010000]));
  assert_eq!(u12![0b000000000001].checked_shl( 5), Some(u12![0b000000100000]));
  assert_eq!(u12![0b000000000001].checked_shl( 6), Some(u12![0b000001000000]));
  assert_eq!(u12![0b000000000001].checked_shl( 7), Some(u12![0b000010000000]));
  assert_eq!(u12![0b000000000001].checked_shl( 8), Some(u12![0b000100000000]));
  assert_eq!(u12![0b000000000001].checked_shl( 9), Some(u12![0b001000000000]));
  assert_eq!(u12![0b000000000001].checked_shl(10), Some(u12![0b010000000000]));
  assert_eq!(u12![0b000000000001].checked_shl(11), Some(u12![0b100000000000]));
  assert_eq!(u12![0b000000000001].checked_shl(12), None);
  assert_eq!(u12![0b000000000001].checked_shl(13), None);
  assert_eq!(u12![0b000000000001].checked_shl(u32::max_value()), None);
}

#[test]
fn test_wrapping_shl() {
  assert_eq!(u12![0b000000000001].wrapping_shl( 0), u12![0b000000000001]);
  assert_eq!(u12![0b000000000001].wrapping_shl( 1), u12![0b000000000010]);
  assert_eq!(u12![0b000000000001].wrapping_shl( 2), u12![0b000000000100]);
  assert_eq!(u12![0b000000000001].wrapping_shl( 3), u12![0b000000001000]);
  assert_eq!(u12![0b000000000001].wrapping_shl( 4), u12![0b000000010000]);
  assert_eq!(u12![0b000000000001].wrapping_shl( 5), u12![0b000000100000]);
  assert_eq!(u12![0b000000000001].wrapping_shl( 6), u12![0b000001000000]);
  assert_eq!(u12![0b000000000001].wrapping_shl( 7), u12![0b000010000000]);
  assert_eq!(u12![0b000000000001].wrapping_shl( 8), u12![0b000100000000]);
  assert_eq!(u12![0b000000000001].wrapping_shl( 9), u12![0b001000000000]);
  assert_eq!(u12![0b000000000001].wrapping_shl(10), u12![0b010000000000]);
  assert_eq!(u12![0b000000000001].wrapping_shl(11), u12![0b100000000000]);
  assert_eq!(u12![0b000000000001].wrapping_shl(12), u12![0b000000000001]);
  assert_eq!(u12![0b000000000001].wrapping_shl(13), u12![0b000000000010]);
}

#[test]
fn test_overflowing_shl() {
  assert_eq!(u12![0b000000000001].overflowing_shl( 0), (u12![0b000000000001], false));
  assert_eq!(u12![0b000000000001].overflowing_shl( 1), (u12![0b000000000010], false));
  assert_eq!(u12![0b000000000001].overflowing_shl( 2), (u12![0b000000000100], false));
  assert_eq!(u12![0b000000000001].overflowing_shl( 3), (u12![0b000000001000], false));
  assert_eq!(u12![0b000000000001].overflowing_shl( 4), (u12![0b000000010000], false));
  assert_eq!(u12![0b000000000001].overflowing_shl( 5), (u12![0b000000100000], false));
  assert_eq!(u12![0b000000000001].overflowing_shl( 6), (u12![0b000001000000], false));
  assert_eq!(u12![0b000000000001].overflowing_shl( 7), (u12![0b000010000000], false));
  assert_eq!(u12![0b000000000001].overflowing_shl( 8), (u12![0b000100000000], false));
  assert_eq!(u12![0b000000000001].overflowing_shl( 9), (u12![0b001000000000], false));
  assert_eq!(u12![0b000000000001].overflowing_shl(10), (u12![0b010000000000], false));
  assert_eq!(u12![0b000000000001].overflowing_shl(11), (u12![0b100000000000], false));
  assert_eq!(u12![0b000000000001].overflowing_shl(12), (u12![0b000000000001], true));
  assert_eq!(u12![0b000000000001].overflowing_shl(13), (u12![0b000000000010], true));
}

#[test]
fn test_shl_operator() {
  assert_eq!(u12![0b000000000001] << ( 0), u12![0b000000000001]);
  assert_eq!(u12![0b000000000001] << ( 1), u12![0b000000000010]);
  assert_eq!(u12![0b000000000001] << ( 2), u12![0b000000000100]);
  assert_eq!(u12![0b000000000001] << ( 3), u12![0b000000001000]);
  assert_eq!(u12![0b000000000001] << ( 4), u12![0b000000010000]);
  assert_eq!(u12![0b000000000001] << ( 5), u12![0b000000100000]);
  assert_eq!(u12![0b000000000001] << ( 6), u12![0b000001000000]);
  assert_eq!(u12![0b000000000001] << ( 7), u12![0b000010000000]);
  assert_eq!(u12![0b000000000001] << ( 8), u12![0b000100000000]);
  assert_eq!(u12![0b000000000001] << ( 9), u12![0b001000000000]);
  assert_eq!(u12![0b000000000001] << (10), u12![0b010000000000]);
  assert_eq!(u12![0b000000000001] << (11), u12![0b100000000000]);
}

#[test]
#[should_panic]
fn test_shl_operator_panics_on_wrapping() {
  let _ = u12![0b000000000001] << 12;
}
