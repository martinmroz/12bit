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

// MARK: - Tests - Not

#[test]
fn test_not() {
    assert_eq!(!u12![0b000000000000], u12![0b111111111111]);
    assert_eq!(!u12![0b000000001111], u12![0b111111110000]);
    assert_eq!(!u12![0b000011111111], u12![0b111100000000]);
    assert_eq!(!u12![0b111111111111], u12![0b000000000000]);
}

// MARK: - Tests - Shift Left

#[test]
fn test_checked_shl() {
    assert_eq!(
        u12![0b000000000001].checked_shl(0),
        Some(u12![0b000000000001])
    );
    assert_eq!(
        u12![0b000000000001].checked_shl(1),
        Some(u12![0b000000000010])
    );
    assert_eq!(
        u12![0b000000000001].checked_shl(2),
        Some(u12![0b000000000100])
    );
    assert_eq!(
        u12![0b000000000001].checked_shl(3),
        Some(u12![0b000000001000])
    );
    assert_eq!(
        u12![0b000000000001].checked_shl(4),
        Some(u12![0b000000010000])
    );
    assert_eq!(
        u12![0b000000000001].checked_shl(5),
        Some(u12![0b000000100000])
    );
    assert_eq!(
        u12![0b000000000001].checked_shl(6),
        Some(u12![0b000001000000])
    );
    assert_eq!(
        u12![0b000000000001].checked_shl(7),
        Some(u12![0b000010000000])
    );
    assert_eq!(
        u12![0b000000000001].checked_shl(8),
        Some(u12![0b000100000000])
    );
    assert_eq!(
        u12![0b000000000001].checked_shl(9),
        Some(u12![0b001000000000])
    );
    assert_eq!(
        u12![0b000000000001].checked_shl(10),
        Some(u12![0b010000000000])
    );
    assert_eq!(
        u12![0b000000000001].checked_shl(11),
        Some(u12![0b100000000000])
    );
    assert_eq!(u12![0b000000000001].checked_shl(12), None);
    assert_eq!(u12![0b000000000001].checked_shl(13), None);
    assert_eq!(u12![0b000000000001].checked_shl(u32::max_value()), None);
}

#[test]
fn test_wrapping_shl() {
    assert_eq!(u12![0b000000000001].wrapping_shl(0), u12![0b000000000001]);
    assert_eq!(u12![0b000000000001].wrapping_shl(1), u12![0b000000000010]);
    assert_eq!(u12![0b000000000001].wrapping_shl(2), u12![0b000000000100]);
    assert_eq!(u12![0b000000000001].wrapping_shl(3), u12![0b000000001000]);
    assert_eq!(u12![0b000000000001].wrapping_shl(4), u12![0b000000010000]);
    assert_eq!(u12![0b000000000001].wrapping_shl(5), u12![0b000000100000]);
    assert_eq!(u12![0b000000000001].wrapping_shl(6), u12![0b000001000000]);
    assert_eq!(u12![0b000000000001].wrapping_shl(7), u12![0b000010000000]);
    assert_eq!(u12![0b000000000001].wrapping_shl(8), u12![0b000100000000]);
    assert_eq!(u12![0b000000000001].wrapping_shl(9), u12![0b001000000000]);
    assert_eq!(u12![0b000000000001].wrapping_shl(10), u12![0b010000000000]);
    assert_eq!(u12![0b000000000001].wrapping_shl(11), u12![0b100000000000]);
    assert_eq!(u12![0b000000000001].wrapping_shl(12), u12![0b000000000001]);
    assert_eq!(u12![0b000000000001].wrapping_shl(13), u12![0b000000000010]);
}

#[test]
fn test_overflowing_shl() {
    assert_eq!(
        u12![0b000000000001].overflowing_shl(0),
        (u12![0b000000000001], false)
    );
    assert_eq!(
        u12![0b000000000001].overflowing_shl(1),
        (u12![0b000000000010], false)
    );
    assert_eq!(
        u12![0b000000000001].overflowing_shl(2),
        (u12![0b000000000100], false)
    );
    assert_eq!(
        u12![0b000000000001].overflowing_shl(3),
        (u12![0b000000001000], false)
    );
    assert_eq!(
        u12![0b000000000001].overflowing_shl(4),
        (u12![0b000000010000], false)
    );
    assert_eq!(
        u12![0b000000000001].overflowing_shl(5),
        (u12![0b000000100000], false)
    );
    assert_eq!(
        u12![0b000000000001].overflowing_shl(6),
        (u12![0b000001000000], false)
    );
    assert_eq!(
        u12![0b000000000001].overflowing_shl(7),
        (u12![0b000010000000], false)
    );
    assert_eq!(
        u12![0b000000000001].overflowing_shl(8),
        (u12![0b000100000000], false)
    );
    assert_eq!(
        u12![0b000000000001].overflowing_shl(9),
        (u12![0b001000000000], false)
    );
    assert_eq!(
        u12![0b000000000001].overflowing_shl(10),
        (u12![0b010000000000], false)
    );
    assert_eq!(
        u12![0b000000000001].overflowing_shl(11),
        (u12![0b100000000000], false)
    );
    assert_eq!(
        u12![0b000000000001].overflowing_shl(12),
        (u12![0b000000000001], true)
    );
    assert_eq!(
        u12![0b000000000001].overflowing_shl(13),
        (u12![0b000000000010], true)
    );
}

#[test]
fn test_shl_operator() {
    assert_eq!(u12![0b000000000001] << (0), u12![0b000000000001]);
    assert_eq!(u12![0b000000000001] << (1), u12![0b000000000010]);
    assert_eq!(u12![0b000000000001] << (2), u12![0b000000000100]);
    assert_eq!(u12![0b000000000001] << (3), u12![0b000000001000]);
    assert_eq!(u12![0b000000000001] << (4), u12![0b000000010000]);
    assert_eq!(u12![0b000000000001] << (5), u12![0b000000100000]);
    assert_eq!(u12![0b000000000001] << (6), u12![0b000001000000]);
    assert_eq!(u12![0b000000000001] << (7), u12![0b000010000000]);
    assert_eq!(u12![0b000000000001] << (8), u12![0b000100000000]);
    assert_eq!(u12![0b000000000001] << (9), u12![0b001000000000]);
    assert_eq!(u12![0b000000000001] << (10), u12![0b010000000000]);
    assert_eq!(u12![0b000000000001] << (11), u12![0b100000000000]);
}

#[test]
#[should_panic]
fn test_shl_operator_panics_on_wrapping() {
    let _ = u12![0b000000000001] << 12;
}

// MARK: - Tests - Shift Right

#[test]
fn test_checked_shr() {
    assert_eq!(
        u12![0b100000000000].checked_shr(0),
        Some(u12![0b100000000000])
    );
    assert_eq!(
        u12![0b100000000000].checked_shr(1),
        Some(u12![0b010000000000])
    );
    assert_eq!(
        u12![0b100000000000].checked_shr(2),
        Some(u12![0b001000000000])
    );
    assert_eq!(
        u12![0b100000000000].checked_shr(3),
        Some(u12![0b000100000000])
    );
    assert_eq!(
        u12![0b100000000000].checked_shr(4),
        Some(u12![0b000010000000])
    );
    assert_eq!(
        u12![0b100000000000].checked_shr(5),
        Some(u12![0b000001000000])
    );
    assert_eq!(
        u12![0b100000000000].checked_shr(6),
        Some(u12![0b000000100000])
    );
    assert_eq!(
        u12![0b100000000000].checked_shr(7),
        Some(u12![0b000000010000])
    );
    assert_eq!(
        u12![0b100000000000].checked_shr(8),
        Some(u12![0b000000001000])
    );
    assert_eq!(
        u12![0b100000000000].checked_shr(9),
        Some(u12![0b000000000100])
    );
    assert_eq!(
        u12![0b100000000000].checked_shr(10),
        Some(u12![0b000000000010])
    );
    assert_eq!(
        u12![0b100000000000].checked_shr(11),
        Some(u12![0b000000000001])
    );
    assert_eq!(u12![0b100000000000].checked_shr(12), None);
    assert_eq!(u12![0b100000000000].checked_shr(13), None);
    assert_eq!(u12![0b100000000000].checked_shr(u32::max_value()), None);
}

#[test]
fn test_wrapping_shr() {
    assert_eq!(u12![0b100000000000].wrapping_shr(0), u12![0b100000000000]);
    assert_eq!(u12![0b100000000000].wrapping_shr(1), u12![0b010000000000]);
    assert_eq!(u12![0b100000000000].wrapping_shr(2), u12![0b001000000000]);
    assert_eq!(u12![0b100000000000].wrapping_shr(3), u12![0b000100000000]);
    assert_eq!(u12![0b100000000000].wrapping_shr(4), u12![0b000010000000]);
    assert_eq!(u12![0b100000000000].wrapping_shr(5), u12![0b000001000000]);
    assert_eq!(u12![0b100000000000].wrapping_shr(6), u12![0b000000100000]);
    assert_eq!(u12![0b100000000000].wrapping_shr(7), u12![0b000000010000]);
    assert_eq!(u12![0b100000000000].wrapping_shr(8), u12![0b000000001000]);
    assert_eq!(u12![0b100000000000].wrapping_shr(9), u12![0b000000000100]);
    assert_eq!(u12![0b100000000000].wrapping_shr(10), u12![0b000000000010]);
    assert_eq!(u12![0b100000000000].wrapping_shr(11), u12![0b000000000001]);
    assert_eq!(u12![0b100000000000].wrapping_shr(12), u12![0b100000000000]);
    assert_eq!(u12![0b100000000000].wrapping_shr(13), u12![0b010000000000]);
}

#[test]
fn test_overflowing_shr() {
    assert_eq!(
        u12![0b100000000000].overflowing_shr(0),
        (u12![0b100000000000], false)
    );
    assert_eq!(
        u12![0b100000000000].overflowing_shr(1),
        (u12![0b010000000000], false)
    );
    assert_eq!(
        u12![0b100000000000].overflowing_shr(2),
        (u12![0b001000000000], false)
    );
    assert_eq!(
        u12![0b100000000000].overflowing_shr(3),
        (u12![0b000100000000], false)
    );
    assert_eq!(
        u12![0b100000000000].overflowing_shr(4),
        (u12![0b000010000000], false)
    );
    assert_eq!(
        u12![0b100000000000].overflowing_shr(5),
        (u12![0b000001000000], false)
    );
    assert_eq!(
        u12![0b100000000000].overflowing_shr(6),
        (u12![0b000000100000], false)
    );
    assert_eq!(
        u12![0b100000000000].overflowing_shr(7),
        (u12![0b000000010000], false)
    );
    assert_eq!(
        u12![0b100000000000].overflowing_shr(8),
        (u12![0b000000001000], false)
    );
    assert_eq!(
        u12![0b100000000000].overflowing_shr(9),
        (u12![0b000000000100], false)
    );
    assert_eq!(
        u12![0b100000000000].overflowing_shr(10),
        (u12![0b000000000010], false)
    );
    assert_eq!(
        u12![0b100000000000].overflowing_shr(11),
        (u12![0b000000000001], false)
    );
    assert_eq!(
        u12![0b100000000000].overflowing_shr(12),
        (u12![0b100000000000], true)
    );
    assert_eq!(
        u12![0b100000000000].overflowing_shr(13),
        (u12![0b010000000000], true)
    );
}

#[test]
fn test_shr_operator() {
    assert_eq!(u12![0b100000000000] >> (0), u12![0b100000000000]);
    assert_eq!(u12![0b100000000000] >> (1), u12![0b010000000000]);
    assert_eq!(u12![0b100000000000] >> (2), u12![0b001000000000]);
    assert_eq!(u12![0b100000000000] >> (3), u12![0b000100000000]);
    assert_eq!(u12![0b100000000000] >> (4), u12![0b000010000000]);
    assert_eq!(u12![0b100000000000] >> (5), u12![0b000001000000]);
    assert_eq!(u12![0b100000000000] >> (6), u12![0b000000100000]);
    assert_eq!(u12![0b100000000000] >> (7), u12![0b000000010000]);
    assert_eq!(u12![0b100000000000] >> (8), u12![0b000000001000]);
    assert_eq!(u12![0b100000000000] >> (9), u12![0b000000000100]);
    assert_eq!(u12![0b100000000000] >> (10), u12![0b000000000010]);
    assert_eq!(u12![0b100000000000] >> (11), u12![0b000000000001]);
}

#[test]
#[should_panic]
fn test_shr_operator_panics_on_wrapping() {
    let _ = u12![0b000000000001] >> 12;
}

// MARK: - Tests - And

#[test]
fn test_and_operator() {
    assert_eq!(
        u12![0b000000000000] & u12![0b111111111111],
        u12![0b000000000000]
    );
    assert_eq!(
        u12![0b111111111111] & u12![0b111111111111],
        u12![0b111111111111]
    );
    assert_eq!(
        u12![0b010101010101] & u12![0b010100000101],
        u12![0b010100000101]
    );
    assert_eq!(
        u12![0b010101010101] & u12![0b000000000101],
        u12![0b000000000101]
    );
}

// MARK: - Tests - Or

#[test]
fn test_or_operator() {
    assert_eq!(
        u12![0b000000000000] | u12![0b111111111111],
        u12![0b111111111111]
    );
    assert_eq!(
        u12![0b111111111111] | u12![0b111111111111],
        u12![0b111111111111]
    );
    assert_eq!(
        u12![0b010101010101] | u12![0b010100000101],
        u12![0b010101010101]
    );
    assert_eq!(
        u12![0b010101010101] | u12![0b000000000101],
        u12![0b010101010101]
    );
}

// MARK: - Tests - Xor

#[test]
fn test_xor_operator() {
    assert_eq!(
        u12![0b000000000000] ^ u12![0b111111111111],
        u12![0b111111111111]
    );
    assert_eq!(
        u12![0b111111111111] ^ u12![0b111111111111],
        u12![0b000000000000]
    );
    assert_eq!(
        u12![0b010101010101] ^ u12![0b010100000101],
        u12![0b000001010000]
    );
    assert_eq!(
        u12![0b010101010101] ^ u12![0b000000000101],
        u12![0b010101010000]
    );
}
