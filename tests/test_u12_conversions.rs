//
// Copyright 2016 The u12 Developers. See the COPYRIGHT
// file at the top-level directory of this distribution.
//
// Licensed under the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>.
// All files in the project carrying such notice may not be copied, modified, or
// distributed except according to those terms.
//

#[macro_use]
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

// MARK: - Tests - Convenience Macro

#[test]
fn test_convenience_macro_accepts_valid_data() {
    assert_eq!(u12![0], U12::min_value());
    assert_eq!(u12![0x00], U12::min_value());
    assert_eq!(u12![0x0000], U12::min_value());
    assert_eq!(u12![4095], U12::max_value());
    assert_eq!(u12![0xFFF], U12::max_value());
}

#[test]
#[should_panic]
fn test_convenience_macro_panics_on_large_value() {
    assert_eq!(u12![0x1000], U12::max_value());
}

// MARK: - Tests - Default Value

#[test]
fn test_default() {
    assert_eq!(U12::default(), U12::min_value());
}
