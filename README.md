twelve_bit
==========

A Rust library for representing 12-bit unsigned values. This is primarily useful for implementing Chip-8 assemblers and interpreters safely. The type implements bulk of the standard Rust literal semantics and operators, and much of the documentation is adapted from the u16 intrinsic type.

[![](http://meritbadge.herokuapp.com/twelve_bit)](https://crates.io/crates/twelve_bit)
[![Coverage Status](https://coveralls.io/repos/github/martinmroz/12bit/badge.svg?branch=master)](https://coveralls.io/github/martinmroz/12bit?branch=master)

### Usage

Add the following to your `Cargo.toml`:

```toml
[dependencies]
twelve_bit = "0.1"
```

In addition, and this to your crate root:

```rust
#[macro_use]
extern crate twelve_bit;
```

Here is an example demonstrating how to interact with the `U12` data type.


```rust
#[macro_use]
extern crate twelve_bit;

use twelve_bit::u12::*;

fn main() {
  assert_eq!(u12![1] + u12![2], u12![3]);
  assert_eq!(u12![4095], U12::maximum_value());
  assert_eq!(u12![4095].overflowing_add(u12![1]), (u12![0], true));
  assert_eq!(u12![4095].overflowing_add(u12![1]), (u12![0], true));
}
```

# Missing Features
* Support for `ShlAssign` and `ShrAssign`.
* Support for bitwise assignment traits.
* Support for `U12::from_str_radix()`.
* Support for `Display`, `UpperHex`, `LowerHex`, `Octal` and `Binary`.
* Support for `Hash`.
* Support for `Step`.

# License

`twelve_bit` is distributed under the terms of the MIT license.

See LICENSE for details.
