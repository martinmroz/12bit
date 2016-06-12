
extern crate twelve_bit;

use twelve_bit::u12::*;

#[test]
pub fn test_from_u8() {
  assert_eq!(u16::from(U12::from(0u8)), 0u16);
  assert_eq!(u16::from(U12::from(15u8)), 15u16);
  assert_eq!(u16::from(U12::from(255u8)), 255u16);
}

#[test]
pub fn test_failable_as_with_u16() {
  assert_eq!(0u16.failable_as(), Some(U12::min_value()));
  assert_eq!(15u16.failable_as(), Some(U12::from(15u8)));
  assert_eq!(4096u16.failable_as(), None);
  assert_eq!(u16::max_value().failable_as(), None);
}

#[test]
pub fn test_failable_as_with_u32() {
  assert_eq!(0u32.failable_as(), Some(U12::min_value()));
  assert_eq!(15u32.failable_as(), Some(U12::from(15u8)));
  assert_eq!(4096u32.failable_as(), None);
  assert_eq!(u32::max_value().failable_as(), None);
}

#[test]
pub fn test_failable_as_with_u64() {
  assert_eq!(0u64.failable_as(), Some(U12::min_value()));
  assert_eq!(15u64.failable_as(), Some(U12::from(15u8)));
  assert_eq!(4096u64.failable_as(), None);
  assert_eq!(u64::max_value().failable_as(), None);
}

#[test]
pub fn test_failable_as_with_usize() {
  assert_eq!(0usize.failable_as(), Some(U12::min_value()));
  assert_eq!(15usize.failable_as(), Some(U12::from(15u8)));
  assert_eq!(4096usize.failable_as(), None);
  assert_eq!(usize::max_value().failable_as(), None);
}
