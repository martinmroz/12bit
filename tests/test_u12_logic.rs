
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
