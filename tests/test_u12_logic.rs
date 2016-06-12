
extern crate twelve_bit;

use twelve_bit::u12::*;

// MARK: - Tests - Not

#[test]
fn test_not() {
  assert_eq!(!U12::from(0), 0xFFFu16.unchecked_into());
  assert_eq!(!U12::from(15), 0xFF0u16.unchecked_into());
  assert_eq!(!U12::from(255), 0xF00u16.unchecked_into());
  assert_eq!(!0xFFFu16.unchecked_into(), U12::from(0));
}
