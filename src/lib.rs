// Copyright © 2018–2025 Trevor Spiteri

// This library is free software: you can redistribute it and/or
// modify it under the terms of either
//
//   * the Apache License, Version 2.0 or
//   * the MIT License
//
// at your option.
//
// You should have recieved copies of the Apache License and the MIT
// License along with the library. If not, see
// <https://www.apache.org/licenses/LICENSE-2.0> and
// <https://opensource.org/licenses/MIT>.

/*!
# Fixed-point numbers

The [*fixed* crate] provides fixed-point numbers.

  * [`FixedI8`] and [`FixedU8`] are eight-bit fixed-point numbers.
  * [`FixedI16`] and [`FixedU16`] are 16-bit fixed-point numbers.
  * [`FixedI32`] and [`FixedU32`] are 32-bit fixed-point numbers.
  * [`FixedI64`] and [`FixedU64`] are 64-bit fixed-point numbers.
  * [`FixedI128`] and [`FixedU128`] are 128-bit fixed-point numbers.

An <i>n</i>-bit fixed-point number has <i>f</i>&nbsp;=&nbsp;`Frac` fractional
bits where 0&nbsp;≤&nbsp;<i>f</i>&nbsp;≤&nbsp;<i>n</i>, and
<i>n</i>&nbsp;&minus;&nbsp;<i>f</i> integer bits. For example,
<code>[FixedI32]\<[U24]></code> is a 32-bit signed fixed-point number with
<i>n</i>&nbsp;=&nbsp;32 total bits, <i>f</i>&nbsp;=&nbsp;24 fractional bits, and
<i>n</i>&nbsp;&minus;&nbsp;<i>f</i>&nbsp;=&nbsp;8 integer bits.
<code>[FixedI32]\<[U0]></code> behaves like [`i32`], and
<code>[FixedU32]\<[U0]></code> behaves like [`u32`].

The difference between any two successive representable numbers is constant
throughout the possible range for a fixed-point number:
<i>Δ</i>&nbsp;=&nbsp;1/2<sup><i>f</i></sup>. When <i>f</i>&nbsp;=&nbsp;0, like
in <code>[FixedI32]\<[U0]></code>, <i>Δ</i>&nbsp;=&nbsp;1 because representable
numbers are integers, and the difference between two successive integers is 1.
When <i>f</i>&nbsp;=&nbsp;<i>n</i>, <i>Δ</i>&nbsp;=&nbsp;1/2<sup><i>n</i></sup>
and the value lies in the range &minus;0.5&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;0.5
for signed numbers like <code>[FixedI32]\<[U32]></code>, and in the range
0&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;1 for unsigned numbers like
<code>[FixedU32]\<[U32]></code>.

The main features are

  * Representation of binary fixed-point numbers up to 128 bits wide.
  * Conversions between fixed-point numbers and numeric primitives.
  * Comparisons between fixed-point numbers and numeric primitives.
  * Parsing from strings in decimal, binary, octal and hexadecimal.
  * Display as decimal, binary, octal and hexadecimal.
  * Arithmetic and logic operations.

This crate does *not* provide decimal fixed-point numbers. For example 0.001
cannot be represented exactly, as it is 1/10<sup>3</sup>. It is binary fractions
like 1/2<sup>4</sup> (0.0625) that can be represented exactly, provided there
are enough fractional bits.

This crate does *not* provide general analytic functions.

  * No algebraic functions are provided, for example no `pow`.
  * No trigonometric functions are provided, for example no `sin` or `cos`.
  * No other transcendental functions are provided, for example no `log` or
    `exp`.

These functions are not provided because different implementations can have
different trade-offs, for example trading some correctness for speed.
Implementations can be provided in other crates.

  * The [*cordic* crate] provides various functions implemented using the
    [CORDIC] algorithm.

The conversions supported cover the following cases.

  * Infallible lossless conversions between fixed-point numbers and numeric
    primitives are provided using [`From`] and [`Into`]. These never fail
    (infallible) and do not lose any bits (lossless).
  * Infallible lossy conversions between fixed-point numbers and numeric
    primitives are provided using the [`LossyFrom`] and [`LossyInto`] traits.
    The source can have more fractional bits than the destination.
  * Checked lossless conversions between fixed-point numbers and numeric
    primitives are provided using the [`LosslessTryFrom`] and
    [`LosslessTryInto`] traits. The source cannot have more fractional bits than
    the destination.
  * Checked conversions between fixed-point numbers and numeric primitives are
    provided using the [`FromFixed`] and [`ToFixed`] traits, or using the
    [`from_num`] and [`to_num`] methods and [their checked
    versions][`checked_from_num`].
  * Additionally, [`az`] casts are implemented for conversion between
    fixed-point numbers and numeric primitives.
  * Fixed-point numbers can be parsed from decimal strings using [`FromStr`],
    and from binary, octal and hexadecimal strings using the
    [`from_str_binary`], [`from_str_octal`] and [`from_str_hex`] methods. The
    result is rounded to the nearest, with ties rounded to even.
  * Fixed-point numbers can be converted to strings using [`Display`],
    [`Binary`], [`Octal`], [`LowerHex`], [`UpperHex`], [`LowerExp`] and
    [`UpperExp`]. The output is rounded to the nearest, with ties rounded to
    even.
  * All fixed-point numbers are plain old data, so [`bytemuck`] bit casting
    conversions can be used.

## Quick examples

```rust
use fixed::types::I20F12;

// 19/3 = 6 1/3
let six_and_third = I20F12::from_num(19) / 3;
// four decimal digits for 12 binary digits
assert_eq!(six_and_third.to_string(), "6.3333");
// find the ceil and convert to i32
assert_eq!(six_and_third.ceil().to_num::<i32>(), 7);
// we can also compare directly to integers
assert_eq!(six_and_third.ceil(), 7);
```

The type [`I20F12`] is a 32-bit fixed-point signed number with 20 integer bits
and 12 fractional bits. It is an alias to <code>[FixedI32]\<[U12]></code>. The
unsigned counterpart would be [`U20F12`]. Aliases are provided for all
combinations of integer and fractional bits adding up to a total of eight, 16,
32, 64 or 128 bits.

```rust
use fixed::types::{I4F4, I4F12};

// -8 ≤ I4F4 < 8 with steps of 1/16 (~0.06)
let a = I4F4::from_num(1);
// multiplication and division by integers are possible
let ans1 = a / 5 * 17;
// 1 / 5 × 17 = 3 2/5 (3.4), but we get 3 3/16 (~3.2)
assert_eq!(ans1, I4F4::from_bits((3 << 4) + 3));
assert_eq!(ans1.to_string(), "3.2");

// -8 ≤ I4F12 < 8 with steps of 1/4096 (~0.0002)
let wider_a = I4F12::from(a);
let wider_ans = wider_a / 5 * 17;
let ans2 = I4F4::from_num(wider_ans);
// now the answer is the much closer 3 6/16 (~3.4)
assert_eq!(ans2, I4F4::from_bits((3 << 4) + 6));
assert_eq!(ans2.to_string(), "3.4");
```

The second example shows some precision and conversion issues. The low precision
of `a` means that `a / 5` is 3⁄16 instead of 1⁄5, leading to an inaccurate
result `ans1` = 3 3⁄16 (~3.2). With a higher precision, we get `wider_a / 5`
equal to 819⁄4096, leading to a more accurate intermediate result `wider_ans` =
3 1635⁄4096. When we convert back to four fractional bits, we get `ans2` = 3
6⁄16 (~3.4).

Note that we can convert from [`I4F4`] to [`I4F12`] using [`From`], as the
target type has the same number of integer bits and a larger number of
fractional bits. Converting from [`I4F12`] to [`I4F4`] cannot use [`From`] as we
have less fractional bits, so we use [`from_num`] instead.

## Writing fixed-point constants and values literally

The [`lit`] method, which is available as a `const` function, can be used to
parse literals. It supports
  * underscores as separators;
  * prefixes “`0b`”, “`0o`” and “`0x`” for binary, octal and hexadecimal
    numbers;
  * an optional decimal exponent with separator “`e`” or “`E`” for decimal,
    binary and octal numbers, or with separator “`@`” for all supported radices
    including hexadecimal.

```rust
use fixed::types::I16F16;

// 0.1275e2 is 12.75
const TWELVE_POINT_75: I16F16 = I16F16::lit("0.127_5e2");
// 1.8 hexadecimal is 1.5 decimal, and 18@-1 is 1.8
const ONE_POINT_5: I16F16 = I16F16::lit("0x_18@-1");
// 12.75 + 1.5 = 14.25
let sum = TWELVE_POINT_75 + ONE_POINT_5;
assert_eq!(sum, 14.25);
```

## Using the *fixed* crate

The *fixed* crate is available on [crates.io][*fixed* crate]. To use it in your
crate, add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
fixed = "1.29"
```

The *fixed* crate requires rustc version 1.83.0 or later.

## Optional features

The *fixed* crate has these optional feature:

 1. `arbitrary`, disabled by default. This provides the generation of arbitrary
    fixed-point numbers from raw, unstructured data. This feature requires the
    [*arbitrary* crate].
 2. `borsh`, disabled by default. This implements serialization and
    deserialization using the [*borsh* crate].
 3. `serde`, disabled by default. This provides serialization support for the
    fixed-point types. This feature requires the [*serde* crate].
 4. `std`, disabled by default. This is for features that are not possible under
    `no_std`: currently this is only required for the `serde-str` feature.
 5. `serde-str`, disabled by default. Fixed-point numbers are serialized as
    strings showing the value when using human-readable formats. This feature
    requires the `serde` and the `std` optional features. **Warning:** numbers
    serialized when this feature is enabled cannot be deserialized when this
    feature is disabled, and vice versa.

To enable features, you can add the dependency like this to [*Cargo.toml*]:

```toml
[dependencies.fixed]
features = ["serde"]
version = "1.29"
```

## Experimental optional features

It is not considered a breaking change if the following experimental features
are removed. The removal of experimental features would however require a minor
version bump. Similarly, on a minor version bump, optional dependencies can be
updated to an incompatible newer version.

 1. `num-traits`, disabled by default. This implements some traits from the
    [*num-traits* crate]. (The plan is to promote this to an optional feature
    once the [*num-traits* crate] reaches version 1.0.0.)
 2. `nightly-float`, disabled by default. This requires the nightly compiler,
    and implements conversions and comparisons with the experimental [`f16`] and
    [`f128`] primitives. (The plan is to always implement the conversions and
    comparisons and remove this experimental feature once the primitives are
    stabilized.)

[`f128`]: https://doc.rust-lang.org/nightly/std/primitive.f128.html
[`f16`]: https://doc.rust-lang.org/nightly/std/primitive.f16.html

## Deprecated optional features

The following optional features are deprecated and will be removed in the next
major version of the crate.

 1. `az`, has no effect. Previously required for the [`az`] cast traits. Now
    these cast traits are always provided.
 2. `f16`, has no effect. Previously required for conversion to/from
    <code>[half]::[f16][half::f16]</code> and
    <code>[half]::[bf16][half::bf16]</code>. Now these conversions are always
    provided.

## License

This crate is free software: you can redistribute it and/or modify it under the
terms of either

  * the [Apache License, Version 2.0][LICENSE-APACHE] or
  * the [MIT License][LICENSE-MIT]

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache License, Version 2.0,
shall be dual licensed as above, without any additional terms or conditions.

[*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[*arbitrary* crate]: https://crates.io/crates/arbitrary
[*borsh* crate]: https://crates.io/crates/borsh
[*cordic* crate]: https://crates.io/crates/cordic
[*fixed* crate]: https://crates.io/crates/fixed
[*half* crate]: https://crates.io/crates/half
[*num-traits* crate]: https://crates.io/crates/num-traits
[*serde* crate]: https://crates.io/crates/serde
[*typenum* crate]: https://crates.io/crates/typenum
[CORDIC]: https://en.wikipedia.org/wiki/CORDIC
[LICENSE-APACHE]: https://www.apache.org/licenses/LICENSE-2.0
[LICENSE-MIT]: https://opensource.org/licenses/MIT
[U0]: crate::types::extra::U0
[U24]: crate::types::extra::U24
[`Binary`]: core::fmt::Binary
[`Display`]: core::fmt::Display
[`FromStr`]: core::str::FromStr
[`I20F12`]: crate::types::I20F12
[`I4F12`]: crate::types::I4F12
[`I4F4`]: crate::types::I4F4
[`LosslessTryFrom`]: traits::LosslessTryFrom
[`LosslessTryInto`]: traits::LosslessTryInto
[`LossyFrom`]: traits::LossyFrom
[`LossyInto`]: traits::LossyInto
[`LowerExp`]: core::fmt::LowerExp
[`LowerHex`]: core::fmt::LowerHex
[`Octal`]: core::fmt::Octal
[`U20F12`]: types::U20F12
[`UpperExp`]: core::fmt::UpperExp
[`UpperHex`]: core::fmt::UpperHex
[`checked_from_num`]: FixedI32::checked_from_num
[`from_num`]: FixedI32::from_num
[`from_str_binary`]: FixedI32::from_str_binary
[`from_str_hex`]: FixedI32::from_str_hex
[`from_str_octal`]: FixedI32::from_str_octal
[`lit`]: FixedI32::lit
[`to_num`]: FixedI32::to_num
*/
#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]
#![warn(unsafe_op_in_unsafe_fn)]
#![doc(html_root_url = "https://docs.rs/fixed/~1.29")]
#![doc(html_logo_url = "data:image/svg+xml;base64,
PHN2ZyB3aWR0aD0iMTI4IiBoZWlnaHQ9IjEyOCIgdmVyc2lvbj0iMS4xIiB2aWV3Qm94PSIwIDAgMzMuODY3IDMzLjg2NyIgeG1s
bnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj48ZGVmcz48Y2xpcFBhdGggaWQ9ImIiPjxjaXJjbGUgY3g9IjE2LjkzMyIg
Y3k9IjI4MC4wNyIgcj0iMTYuOTMzIiBmaWxsPSIjMDA3MmIyIi8+PC9jbGlwUGF0aD48Y2xpcFBhdGggaWQ9ImEiPjxjaXJjbGUg
Y3g9IjE2LjkzMyIgY3k9IjI4MC4wNyIgcj0iMTYuOTMzIiBmaWxsPSIjMDA3MmIyIi8+PC9jbGlwUGF0aD48L2RlZnM+PGcgdHJh
bnNmb3JtPSJ0cmFuc2xhdGUoMCAtMjYzLjEzKSI+PGNpcmNsZSBjeD0iMTYuOTMzIiBjeT0iMjgwLjA3IiByPSIxNi45MzMiIGZp
bGw9IiNmN2YxYTEiLz48ZyBmaWxsPSIjMDA3MmIyIj48cGF0aCBkPSJtMTUuMzQ2IDI4My41MWgzLjE3NXMwIDAuNzkzNzYgMC41
MjkxNyAxLjg1MjFoLTQuMjMzM2MwLjUyOTE2LTEuMDU4MyAwLjUyOTE2LTEuODUyMSAwLjUyOTE2LTEuODUyMXoiIHN0cm9rZS13
aWR0aD0iLjUyOTE3Ii8+PHBhdGggZD0ibTM0LjExMiAyODUuNTRjMi4yODYgMCAzLjgxLTEuMjg2OSAzLjgxLTIuOTgwMyAwLTEu
NDIyNC0wLjgyOTczLTIuMjUyMS0xLjg2MjctMi44MTA5di0wLjA2NzdjMC43NDUwNy0wLjQ5MTA3IDEuNDA1NS0xLjMyMDggMS40
MDU1LTIuMzUzNyAwLTEuNzc4LTEuMzAzOS0yLjk0NjQtMy4yNjgxLTIuOTQ2NC0xLjk5ODEgMC0zLjQzNzUgMS4xMzQ1LTMuNDM3
NSAyLjk2MzMgMCAxLjEzNDUgMC42MDk2IDEuOTEzNSAxLjQzOTMgMi41NHYwLjA2NzdjLTEuMDE2IDAuNTQxODctMS44Mjg4IDEu
MzM3Ny0xLjgyODggMi42NDE2IDAgMS43NDQxIDEuNTkxNyAyLjk0NjQgMy43NDIzIDIuOTQ2NHptMC42NzczMy02LjQ2ODVjLTEu
MTAwNy0wLjQyMzMzLTEuODQ1Ny0wLjg0NjY3LTEuODQ1Ny0xLjcyNzIgMC0wLjgyOTczIDAuNTQxODctMS4yMzYxIDEuMjAyMy0x
LjIzNjEgMC44MTI4IDAgMS4zMDM5IDAuNTU4OCAxLjMwMzkgMS4zODg1IDAgMC41NTg4LTAuMjM3MDcgMS4wODM3LTAuNjYwNCAx
LjU3NDh6bS0wLjYyNjUzIDQuNzQxM2MtMC44OTc0NiAwLTEuNjU5NS0wLjU1ODgtMS42NTk1LTEuNTA3MSAwLTAuNjYwNCAwLjM1
NTYtMS4yNyAwLjgyOTczLTEuNzEwMyAxLjM1NDcgMC41NzU3MyAyLjI2OTEgMC45MzEzMyAyLjI2OTEgMS44Nzk2IDAgMC44OTc0
Ny0wLjYwOTYgMS4zMzc3LTEuNDM5MyAxLjMzNzd6IiBjbGlwLXBhdGg9InVybCgjYikiLz48cGF0aCBkPSJtMjEuMzQ0IDI4NS4z
NGg3LjU2OTJ2LTIuMDk5N2gtMi40MDQ1Yy0wLjQ5MTA3IDAtMS4yMzYxIDAuMDY3Ny0xLjc5NDkgMC4xMzU0NyAxLjkxMzUtMS44
Nzk2IDMuNjc0NS0zLjY0MDcgMy42NzQ1LTUuNTg4IDAtMi4wNDg5LTEuNDM5My0zLjQwMzYtMy41NTYtMy40MDM2LTEuNTA3MSAw
LTIuNTIzMSAwLjU5MjY3LTMuNTU2IDEuNzYxMWwxLjMwMzkgMS4yODY5YzAuNTQxODctMC41NzU3MyAxLjEzNDUtMS4xMDA3IDEu
OTEzNS0xLjEwMDcgMC45MzEzMyAwIDEuNTI0IDAuNTc1NzQgMS41MjQgMS42MjU2IDAgMS41MDcxLTEuOTY0MyAzLjQzNzUtNC42
NzM2IDUuODQyeiIvPjxwYXRoIGQ9Im0xNi45MzMgMjg0LjE2YzEuNzI3MiAwIDMuMDE0MS0xLjM1NDcgMy4wMTQxLTMuMTE1NyAw
LTEuNzk0OS0xLjI4NjktMy4xNDk2LTMuMDE0MS0zLjE0OTYtMS43MjcyIDAtMy4wMTQxIDEuMzU0Ny0zLjAxNDEgMy4xNDk2IDAg
MS43NjExIDEuMjg2OSAzLjExNTcgMy4wMTQxIDMuMTE1N3oiLz48cGF0aCBkPSJtOC45MTU0IDI4MC4zOGMwLjgxMjggMCAxLjQw
NTUgMC40MjMzNCAxLjQwNTUgMS41NTc5IDAgMS4yMTkyLTAuNjA5NiAxLjc0NDEtMS4zNTQ3IDEuNzQ0MXMtMS40NTYzLTAuNTQx
ODYtMS42NzY0LTIuMjM1MmMwLjQ0MDI3LTAuNzYyIDEuMDY2OC0xLjA2NjggMS42MjU2LTEuMDY2OHptMC4xMDE2IDUuMTY0N2Mx
Ljk0NzMgMCAzLjU3MjktMS4zNzE2IDMuNTcyOS0zLjYwNjggMC0yLjI2OTEtMS4zNTQ3LTMuMzE4OS0zLjIwMDQtMy4zMTg5LTAu
NjYwNCAwLTEuNTkxNyAwLjQyMzMzLTIuMTUwNSAxLjEzNDUgMC4wODQ2NjctMi41MDYxIDEuMDMyOS0zLjM1MjggMi4yMTgzLTMu
MzUyOCAwLjYyNjUzIDAgMS4zMDM5IDAuMzU1NiAxLjY3NjQgMC43NjJsMS4zMDM5LTEuNDkwMWMtMC42NzczMy0wLjY5NDI3LTEu
NzEwMy0xLjI4NjktMy4xMzI3LTEuMjg2OS0yLjI2OTEgMC00LjM1MTkgMS44MTE5LTQuMzUxOSA1LjgyNTEgMCAzLjc3NjEgMS45
ODEyIDUuMzM0IDQuMDY0IDUuMzM0eiIvPjxwYXRoIGQ9Im0tMC4yMTE2NyAyODUuNTRjMi4zMDI5IDAgMy44NDM5LTEuOTY0MyAz
Ljg0MzktNS42MjE5cy0xLjU0MDktNS41MzcyLTMuODQzOS01LjUzNzJjLTIuMzAyOSAwLTMuODQzOSAxLjg3OTYtMy44NDM5IDUu
NTM3MnMxLjU0MDkgNS42MjE5IDMuODQzOSA1LjYyMTl6bTAtMS45MzA0Yy0wLjgyOTczIDAtMS40OTAxLTAuNzYyLTEuNDkwMS0z
LjY5MTUgMC0yLjk0NjQgMC42NjA0LTMuNjA2OCAxLjQ5MDEtMy42MDY4IDAuODQ2NjcgMCAxLjQ5MDEgMC42NjA0IDEuNDkwMSAz
LjYwNjggMCAyLjkyOTUtMC42NDM0NyAzLjY5MTUtMS40OTAxIDMuNjkxNXoiIGNsaXAtcGF0aD0idXJsKCNhKSIvPjwvZz48L2c+
PC9zdmc+Cg==
")]
#![doc(test(attr(deny(warnings))))]
#![cfg_attr(feature = "fail-on-warnings", deny(warnings))]
#![cfg_attr(feature = "nightly-float", feature(f16, f128))]

#[cfg(all(not(feature = "std"), test))]
extern crate std;

#[macro_use]
mod macros;

mod arith;
#[cfg(feature = "borsh")]
mod borshize;
mod bytes;
mod cast;
mod cmp;
mod cmp_fixed;
pub mod consts;
mod convert;
mod debug_hex;
mod display;
pub mod f128;
mod float_helper;
mod from_str;
mod helpers;
mod hypot;
#[cfg(feature = "arbitrary")]
mod impl_arbitrary;
mod impl_bytemuck;
#[cfg(feature = "num-traits")]
mod impl_num_traits;
mod int256;
mod int_helper;
mod inv_lerp;
mod lerp;
mod log;
mod log10;
mod prim_traits;
mod saturating;
#[cfg(feature = "serde")]
mod serdeize;
mod sqrt;
pub mod traits;
mod traits_bits;
pub mod types;
mod unwrapped;
mod wrapping;

pub use crate::f128::private::F128;
pub use crate::from_str::ParseFixedError;
#[cfg(feature = "num-traits")]
pub use crate::impl_num_traits::RadixParseFixedError;
use crate::log::Base;
pub use crate::saturating::Saturating;
use crate::traits::{FromFixed, ToFixed};
use crate::types::extra::{
    Diff, IsLessOrEqual, LeEqU8, LeEqU16, LeEqU32, LeEqU64, LeEqU128, Sum, True, U0, U4, U5, U6,
    U7, U8, U12, U13, U14, U15, U16, U28, U29, U30, U31, U32, U60, U61, U62, U63, U64, U124, U125,
    U126, U127, U128, Unsigned,
};
pub use crate::unwrapped::Unwrapped;
pub use crate::wrapping::Wrapping;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::num::NonZero;
use core::ops::{Add, Sub};

/// A prelude to import useful traits.
///
/// This prelude is similar to the [standard library’s prelude][std::prelude] in
/// that you’ll almost always want to import its entire contents, but unlike the
/// standard library’s prelude you’ll have to do so manually:
///
/// ```rust
/// # #[allow(unused_imports)]
/// use fixed::prelude::*;
/// ```
///
/// The prelude may grow over time as additional items see ubiquitous use.
///
/// # Contents
///
/// The prelude re-exports the following:
///
///  * <code>[traits]::{[FromFixed], [ToFixed]}</code>, checked conversions
///    from/to fixed-point numbers.
///  * <code>[traits]::{[LossyFrom], [LossyInto]}</code>, infallible lossy
///    conversions.
///  * <code>[traits]::{[LosslessTryFrom], [LosslessTryInto]}</code>, checked
///    lossless conversions.
///
/// [LosslessTryFrom]: crate::traits::LosslessTryFrom
/// [LosslessTryInto]: crate::traits::LosslessTryInto
/// [LossyFrom]: crate::traits::LossyFrom
/// [LossyInto]: crate::traits::LossyInto
pub mod prelude {
    pub use crate::traits::{
        FromFixed, LosslessTryFrom, LosslessTryInto, LossyFrom, LossyInto, ToFixed,
    };
}

#[macro_use]
mod macros_from_to;
#[macro_use]
mod macros_round;
#[macro_use]
mod macros_no_frac;
#[macro_use]
mod macros_frac;
#[macro_use]
mod macros_const;

macro_rules! fixed {
    (
        description = $description:literal,
        {Self, Inner} = {$Self:ident, $Inner:ident},
        Signedness = $Signedness:ident,
        LeEqU = $LeEqU:ident,
        {Unm1, Un} = {$Unm1:ident, $Un:ident},
        [nm4 ..= np1]
            = [$nm4:literal, $nm3:literal, $nm2:literal, $nm1:literal, $n:literal, $np1:literal],
        {ISelf, IInner} = {$ISelf:ident, $IInner:ident},
        {USelf, UInner} = {$USelf:ident, $UInner:ident},
        [LeEqUC0 ..= LeEqUC3] = [$LeEqUC0:ident, $LeEqUC1:ident, $LeEqUC2:ident, $LeEqUC3:ident],
        nbytes = $nbytes:literal,
        {bytes_val, rev_bytes_val} = {$bytes_val:literal, $rev_bytes_val:literal $(,)?},
        {be_bytes, le_bytes} = {$be_bytes:literal, $le_bytes:literal $(,)?},
        $(
            n2 = $n2:literal,
            {Double, DoubleInner} = {$Double:ident, $DoubleInner:ident},
            {IDouble, IDoubleInner} = {$IDouble:ident, $IDoubleInner:ident},
        )?
    ) => {
        comment! {
            $description, "-bit ",
            if_signed_unsigned!($Signedness, "signed", "unsigned"),
            " number with `Frac` fractional bits.

The number has ", $n, " bits, of which <i>f</i>&nbsp;=&nbsp;`Frac` are
fractional bits and ", $n, "&nbsp;&minus;&nbsp;<i>f</i> are integer bits.
The value <i>x</i> can lie in the range ",
            if_signed_unsigned!(
                $Signedness,
                concat!("&minus;2<sup>", $nm1, "</sup>/2<sup><i>f</i></sup>"),
                "0",
            ),
            "&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;2<sup>",
            if_signed_unsigned!($Signedness, $nm1, $n),
            "</sup>/2<sup><i>f</i></sup>. The difference between successive
numbers is constant throughout the range: <i>Δ</i>&nbsp;=&nbsp;1/2<sup><i>f</i></sup>.

For <code>", stringify!($Self), "\\<[U0]></code>, <i>f</i>&nbsp;=&nbsp;0 and
<i>Δ</i>&nbsp;=&nbsp;1, and the fixed-point number behaves like ",
            if_signed_unsigned!($Signedness, "an", "a"),
            " [`", stringify!($Inner), "`] with the value lying in the range ",
            if_signed_unsigned!(
                $Signedness,
                concat!("&minus;2<sup>", $nm1, "</sup>"),
                "0",
            ),
            "&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;2<sup>",
            if_signed_unsigned!($Signedness, $nm1, $n),
            "</sup>. For <code>", stringify!($Self), "\\<[U", $n, "]></code>,
<i>f</i>&nbsp;=&nbsp;", $n, " and
<i>Δ</i>&nbsp;=&nbsp;1/2<sup>", $n, "</sup>, and the value lies in the
range ",
            if_signed_unsigned!(
                $Signedness,
                "&minus;1/2&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;1/2",
                "0&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;1",
            ),
            ".

`Frac` is an [`Unsigned`] as provided by the [*typenum* crate].

`", stringify!($Self), "<Frac>` has the same size, alignment and ABI as
[`", stringify!($Inner), "`]; it is `#[repr(transparent)]` with
[`", stringify!($Inner), "`] as the only non-zero-sized field.

# Examples

```rust
use fixed::types::extra::U3;
use fixed::", stringify!($Self), ";
let eleven = ", stringify!($Self), "::<U3>::from_num(11);
assert_eq!(eleven, ", stringify!($Self), "::<U3>::from_bits(11 << 3));
assert_eq!(eleven, 11);
assert_eq!(eleven.to_string(), \"11\");
let two_point_75 = eleven / 4;
assert_eq!(two_point_75, ", stringify!($Self), "::<U3>::from_bits(11 << 1));
assert_eq!(two_point_75, 2.75);
assert_eq!(two_point_75.to_string(), \"2.8\");
```

[*typenum* crate]: https://crates.io/crates/typenum
[U", $n, "]: crate::types::extra::U", $n, "
[U0]: crate::types::extra::U0
";
            #[repr(transparent)]
            pub struct $Self<Frac> {
                pub(crate) bits: $Inner,
                phantom: PhantomData<Frac>,
            }
        }

        impl<Frac> Clone for $Self<Frac> {
            #[inline]
            fn clone(&self) -> $Self<Frac> {
                *self
            }
        }

        impl<Frac> Copy for $Self<Frac> {}

        impl<Frac> Default for $Self<Frac> {
            #[inline]
            fn default() -> Self {
                $Self {
                    bits: Default::default(),
                    phantom: PhantomData,
                }
            }
        }

        impl<Frac> Hash for $Self<Frac> {
            #[inline]
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.bits.hash(state);
            }
        }

        // inherent methods that do not require Frac bounds, some of which can thus be const
        fixed_no_frac! {
            {Self, Inner} = {$Self, $Inner},
            Signedness = $Signedness,
            LeEqU = $LeEqU,
            {Unm1, Un} = {$Unm1, $Un},
            [nm4 ..= np1] = [$nm4, $nm3, $nm2, $nm1, $n, $np1],
            {ISelf, IInner} = {$ISelf, $IInner},
            {USelf, UInner} = {$USelf, $UInner},
            nbytes = $nbytes,
            {bytes_val, rev_bytes_val} = {$bytes_val, $rev_bytes_val},
            {be_bytes, le_bytes} = {$be_bytes, $le_bytes},
            $(
                n2 = $n2,
                {Double, DoubleInner} = {$Double, $DoubleInner},
                {IDouble, IDoubleInner} = {$IDouble, $IDoubleInner},
            )?
        }
        // inherent methods that require Frac bounds, and cannot be const
        fixed_frac! {
            {Self, Inner} = {$Self, $Inner},
            Signedness = $Signedness,
            LeEqU = $LeEqU,
            {nm4, nm1, n} = {$nm4, $nm1, $n},
            {USelf, UInner} = {$USelf, $UInner},
        }
        fixed_const! {
            Self = $Self,
            Signedness = $Signedness,
            LeEqU = $LeEqU,
            [nm4 ..= n] = [$nm4, $nm3, $nm2, $nm1, $n],
            [LeEqUC0 ..= LeEqUC3] = [$LeEqUC0, $LeEqUC1, $LeEqUC2, $LeEqUC3],
        }
    };
}

fixed! {
    description = "An eight",
    {Self, Inner} = {FixedU8, u8},
    Signedness = Unsigned,
    LeEqU = LeEqU8,
    {Unm1, Un} = {U7, U8},
    [nm4 ..= np1] = [4, 5, 6, 7, 8, 9],
    {ISelf, IInner} = {FixedI8, i8},
    {USelf, UInner} = {FixedU8, u8},
    [LeEqUC0 ..= LeEqUC3] = [U8, U7, U6, U5],
    nbytes = 1,
    {bytes_val, rev_bytes_val} = {"0x12", "0x12"},
    {be_bytes, le_bytes} = {"[0x12]", "[0x12]"},
    n2 = 16,
    {Double, DoubleInner} = {FixedU16, u16},
    {IDouble, IDoubleInner} = {FixedI16, i16},
}
fixed! {
    description = "A 16",
    {Self, Inner} = {FixedU16, u16},
    Signedness = Unsigned,
    LeEqU = LeEqU16,
    {Unm1, Un} = {U15, U16},
    [nm4 ..= np1] = [12, 13, 14, 15, 16, 17],
    {ISelf, IInner} = {FixedI16, i16},
    {USelf, UInner} = {FixedU16, u16},
    [LeEqUC0 ..= LeEqUC3] = [U16, U15, U14, U13],
    nbytes = 2,
    {bytes_val, rev_bytes_val} = {"0x1234", "0x3412"},
    {be_bytes, le_bytes} = {"[0x12, 0x34]", "[0x34, 0x12]"},
    n2 = 32,
    {Double, DoubleInner} = {FixedU32, u32},
    {IDouble, IDoubleInner} = {FixedI32, i32},
}
fixed! {
    description = "A 32",
    {Self, Inner} = {FixedU32, u32},
    Signedness = Unsigned,
    LeEqU = LeEqU32,
    {Unm1, Un} = {U31, U32},
    [nm4 ..= np1] = [28, 29, 30, 31, 32, 33],
    {ISelf, IInner} = {FixedI32, i32},
    {USelf, UInner} = {FixedU32, u32},
    [LeEqUC0 ..= LeEqUC3] = [U32, U31, U30, U29],
    nbytes = 4,
    {bytes_val, rev_bytes_val} = {"0x1234_5678", "0x7856_3412"},
    {be_bytes, le_bytes} = {"[0x12, 0x34, 0x56, 0x78]", "[0x78, 0x56, 0x34, 0x12]"},
    n2 = 64,
    {Double, DoubleInner} = {FixedU64, u64},
    {IDouble, IDoubleInner} = {FixedI64, i64},
}
fixed! {
    description = "A 64",
    {Self, Inner} = {FixedU64, u64},
    Signedness = Unsigned,
    LeEqU = LeEqU64,
    {Unm1, Un} = {U63, U64},
    [nm4 ..= np1] = [60, 61, 62, 63, 64, 65],
    {ISelf, IInner} = {FixedI64, i64},
    {USelf, UInner} = {FixedU64, u64},
    [LeEqUC0 ..= LeEqUC3] = [U64, U63, U62, U61],
    nbytes = 8,
    {bytes_val, rev_bytes_val} = {"0x1234_5678_9ABC_DE0F", "0x0FDE_BC9A_7856_3412"},
    {be_bytes, le_bytes} = {
        "[0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0x0F]",
        "[0x0F, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]",
    },
    n2 = 128,
    {Double, DoubleInner} = {FixedU128, u128},
    {IDouble, IDoubleInner} = {FixedI128, i128},
}
fixed! {
    description = "A 128",
    {Self, Inner} = {FixedU128, u128},
    Signedness = Unsigned,
    LeEqU = LeEqU128,
    {Unm1, Un} = {U127, U128},
    [nm4 ..= np1] = [124, 125, 126, 127, 128, 129],
    {ISelf, IInner} = {FixedI128, i128},
    {USelf, UInner} = {FixedU128, u128},
    [LeEqUC0 ..= LeEqUC3] = [U128, U127, U126, U125],
    nbytes = 16,
    {bytes_val, rev_bytes_val} = {
        "0x1234_5678_9ABC_DEF0_0102_0304_0506_0708",
        "0x0807_0605_0403_0201_F0DE_BC9A_7856_3412",
    },
    {be_bytes, le_bytes} = {
        "[0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0, \
         0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]",
        "[0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01, \
         0xF0, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]",
    },
}
fixed! {
    description = "An eight",
    {Self, Inner} = {FixedI8, i8},
    Signedness = Signed,
    LeEqU = LeEqU8,
    {Unm1, Un} = {U7, U8},
    [nm4 ..= np1] = [4, 5, 6, 7, 8, 9],
    {ISelf, IInner} = {FixedI8, i8},
    {USelf, UInner} = {FixedU8, u8},
    [LeEqUC0 ..= LeEqUC3] = [U7, U6, U5, U4],
    nbytes = 1,
    {bytes_val, rev_bytes_val} = {"0x12", "0x12"},
    {be_bytes, le_bytes} = {"[0x12]", "[0x12]"},
    n2 = 16,
    {Double, DoubleInner} = {FixedI16, i16},
    {IDouble, IDoubleInner} = {FixedI16, i16},
}
fixed! {
    description = "A 16",
    {Self, Inner} = {FixedI16, i16},
    Signedness = Signed,
    LeEqU = LeEqU16,
    {Unm1, Un} = {U15, U16},
    [nm4 ..= np1] = [12, 13, 14, 15, 16, 17],
    {ISelf, IInner} = {FixedI16, i16},
    {USelf, UInner} = {FixedU16, u16},
    [LeEqUC0 ..= LeEqUC3] = [U15, U14, U13, U12],
    nbytes = 2,
    {bytes_val, rev_bytes_val} = {"0x1234", "0x3412"},
    {be_bytes, le_bytes} = {"[0x12, 0x34]", "[0x34, 0x12]"},
    n2 = 32,
    {Double, DoubleInner} = {FixedI32, i32},
    {IDouble, IDoubleInner} = {FixedI32, i32},
}
fixed! {
    description = "A 32",
    {Self, Inner} = {FixedI32, i32},
    Signedness = Signed,
    LeEqU = LeEqU32,
    {Unm1, Un} = {U31, U32},
    [nm4 ..= np1] = [28, 29, 30, 31, 32, 33],
    {ISelf, IInner} = {FixedI32, i32},
    {USelf, UInner} = {FixedU32, u32},
    [LeEqUC0 ..= LeEqUC3] = [U31, U30, U29, U28],
    nbytes = 4,
    {bytes_val, rev_bytes_val} = {"0x1234_5678", "0x7856_3412"},
    {be_bytes, le_bytes} = {"[0x12, 0x34, 0x56, 0x78]", "[0x78, 0x56, 0x34, 0x12]"},
    n2 = 64,
    {Double, DoubleInner} = {FixedI64, i64},
    {IDouble, IDoubleInner} = {FixedI64, i64},
}
fixed! {
    description = "A 64",
    {Self, Inner} = {FixedI64, i64},
    Signedness = Signed,
    LeEqU = LeEqU64,
    {Unm1, Un} = {U63, U64},
    [nm4 ..= np1] = [60, 61, 62, 63, 64, 65],
    {ISelf, IInner} = {FixedI64, i64},
    {USelf, UInner} = {FixedU64, u64},
    [LeEqUC0 ..= LeEqUC3] = [U63, U62, U61, U60],
    nbytes = 8,
    {bytes_val, rev_bytes_val} = {"0x1234_5678_9ABC_DE0F", "0x0FDE_BC9A_7856_3412"},
    {be_bytes, le_bytes} = {
        "[0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0x0F]",
        "[0x0F, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]",
    },
    n2 = 128,
    {Double, DoubleInner} = {FixedI128, i128},
    {IDouble, IDoubleInner} = {FixedI128, i128},
}
fixed! {
    description = "A 128",
    {Self, Inner} = {FixedI128, i128},
    Signedness = Signed,
    LeEqU = LeEqU128,
    {Unm1, Un} = {U127, U128},
    [nm4 ..= np1] = [124, 125, 126, 127, 128, 129],
    {ISelf, IInner} = {FixedI128, i128},
    {USelf, UInner} = {FixedU128, u128},
    [LeEqUC0 ..= LeEqUC3] = [U127, U126, U125, U124],
    nbytes = 16,
    {bytes_val, rev_bytes_val} = {
        "0x1234_5678_9ABC_DEF0_0102_0304_0506_0708",
        "0x0807_0605_0403_0201_F0DE_BC9A_7856_3412",
    },
    {be_bytes, le_bytes} = {
        "[0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0, \
         0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]",
        "[0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01, \
         0xF0, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]",
    },
}

/// The bit representation of a *binary128* floating-point number (`f128`).
///
/// This type can be used to
///
///   * convert between fixed-point numbers and the bit representation of
///     128-bit floating-point numbers.
///   * compare fixed-point numbers and the bit representation of 128-bit
///     floating-point numbers.
///
/// This is deprecated, and [`F128`] should be used instead. There are two main
/// differences to keep in mind when switching to [`F128`]:
///
///   * The ordering for `F128Bits` is total ordering, not regular
///     floating-point number ordering, while the ordering for [`F128`] is
///     similar to ordering for standard floating-point numbers.
///   * The underlying [`u128`] value for `F128Bits` is accessible as a public
///     field, while for [`F128`] it is accessible only through the [`to_bits`]
///     and [`from_bits`] methods.
///
/// [`from_bits`]: F128::from_bits
/// [`to_bits`]: F128::to_bits
#[deprecated(since = "1.18.0", note = "use `F128` instead")]
#[repr(transparent)]
#[derive(Clone, Copy, Default, Hash, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct F128Bits(pub u128);

#[allow(deprecated)]
impl F128Bits {
    #[inline]
    pub(crate) fn to_bits(self) -> u128 {
        self.0
    }

    #[inline]
    pub(crate) fn from_bits(bits: u128) -> F128Bits {
        F128Bits(bits)
    }
}

/// Defines constant fixed-point numbers from integer expressions.
///
/// This macro was useful because [`from_num`][FixedI32::from_num] cannot be
/// used in constant expressions. Now constant fixed-point numbers can be
/// created using the [`const_from_int`][FixedI32::const_from_int] method or the
/// [`lit`][FixedI32::lit] method, so this macro is deprecated.
///
/// # Examples
///
/// ```rust
/// # #![allow(deprecated)]
/// use fixed::const_fixed_from_int;
/// use fixed::types::I16F16;
/// const_fixed_from_int! {
///     // define a constant using an integer
///     const FIVE: I16F16 = 5;
///     // define a constant using an integer expression
///     const SUM: I16F16 = 3 + 2;
/// }
/// assert_eq!(FIVE, 5);
/// assert_eq!(SUM, 5);
/// ```
///
/// This can now be rewritten as
///
/// ```rust
/// use fixed::types::I16F16;
/// const FIVE: I16F16 = I16F16::const_from_int(5);
/// const SUM: I16F16 = I16F16::const_from_int(3 + 2);
/// assert_eq!(FIVE, 5);
/// assert_eq!(SUM, 5);
/// ```
#[macro_export]
#[deprecated(since = "1.20.0", note = "use the `const_from_int` method instead")]
macro_rules! const_fixed_from_int {
    ($($vis:vis const $NAME:ident: $Fixed:ty = $int:expr;)*) => { $(
        $vis const $NAME: $Fixed = <$Fixed>::const_from_int($int);
    )* };
}

/// These are doc tests that should not appear in the docs, but are useful as
/// doc tests can check to ensure compilation failure.
///
/// The first snippet succeeds, and acts as a control.
///
/// ```rust
/// use fixed::types::*;
/// const ZERO_I0: I0F32 = I0F32::const_from_int(0);
/// const ZERO_I1: I32F0 = I32F0::const_from_int(0);
/// const ZERO_U0: U0F32 = U0F32::const_from_int(0);
/// const ZERO_U1: U32F0 = U32F0::const_from_int(0);
///
/// const ONE_I0: I2F30 = I2F30::const_from_int(1);
/// const ONE_I1: I32F0 = I32F0::const_from_int(1);
/// const ONE_U0: U1F31 = U1F31::const_from_int(1);
/// const ONE_U1: U32F0 = U32F0::const_from_int(1);
///
/// const MINUS_ONE_I0: I1F31 = I1F31::const_from_int(-1);
/// const MINUS_ONE_I1: I32F0 = I32F0::const_from_int(-1);
///
/// const MINUS_TWO_I0: I2F30 = I2F30::const_from_int(-2);
/// const MINUS_TWO_I1: I32F0 = I32F0::const_from_int(-2);
///
/// mod test_pub {
///     use fixed::types::*;
///
///     pub const PUB: I32F0 = I32F0::const_from_int(0);
/// }
///
/// assert_eq!(ZERO_I0, 0);
/// assert_eq!(ZERO_I1, 0);
/// assert_eq!(ZERO_U0, 0);
/// assert_eq!(ZERO_U1, 0);
///
/// assert_eq!(ONE_I0, 1);
/// assert_eq!(ONE_I1, 1);
/// assert_eq!(ONE_U0, 1);
/// assert_eq!(ONE_U1, 1);
///
/// assert_eq!(MINUS_ONE_I0, -1);
/// assert_eq!(MINUS_ONE_I1, -1);
///
/// assert_eq!(MINUS_TWO_I0, -2);
/// assert_eq!(MINUS_TWO_I1, -2);
///
/// assert_eq!(test_pub::PUB, 0);
/// ```
///
/// The rest of the tests should all fail compilation.
///
/// Not enough integer bits for 1.
/// ```rust,compile_fail
/// use fixed::types::*;
/// const _ONE: I0F32 = I0F32::const_from_int(1);
/// ```
/// ```rust,compile_fail
/// use fixed::types::*;
/// const _ONE: I1F31 = I1F31::const_from_int(1);
/// ```
/// ```rust,compile_fail
/// use fixed::types::*;
/// const _ONE: U0F32 = U0F32::const_from_int(1);
/// ```
///
/// Not enough integer bits for -1.
/// ```rust,compile_fail
/// use fixed::types::*;
/// const _MINUS_ONE: I0F32 = I0F32::const_from_int(-1);
/// ```
///
/// Not enough integer bits for -2.
/// ```rust,compile_fail
/// use fixed::types::*;
/// const _MINUS_TWO: I1F31 = I1F31::const_from_int(-2);
/// ```
fn _compile_fail_tests() {}

#[cfg(test)]
mod tests {
    use crate::types::{I0F32, I1F31, I16F16, U0F32, U16F16};

    #[test]
    fn rounding_signed() {
        // -0.5
        let f = I0F32::from_bits(-1 << 31);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I0F32::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I0F32::ZERO, true));
        assert_eq!(f.overflowing_round(), (I0F32::ZERO, true));
        assert_eq!(f.overflowing_round_ties_even(), (I0F32::ZERO, false));

        // -0.5 + Δ
        let f = I0F32::from_bits((-1 << 31) + 1);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I0F32::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I0F32::ZERO, true));
        assert_eq!(f.overflowing_round(), (I0F32::ZERO, false));
        assert_eq!(f.overflowing_round_ties_even(), (I0F32::ZERO, false));

        // 0
        let f = I0F32::from_bits(0);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I0F32::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I0F32::ZERO, false));
        assert_eq!(f.overflowing_round(), (I0F32::ZERO, false));
        assert_eq!(f.overflowing_round_ties_even(), (I0F32::ZERO, false));

        // 0.5 - Δ
        let f = I0F32::from_bits((1 << 30) - 1 + (1 << 30));
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I0F32::ZERO, true));
        assert_eq!(f.overflowing_floor(), (I0F32::ZERO, false));
        assert_eq!(f.overflowing_round(), (I0F32::ZERO, false));
        assert_eq!(f.overflowing_round_ties_even(), (I0F32::ZERO, false));

        // -1
        let f = I1F31::from_bits((-1) << 31);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), -1);
        assert_eq!(f.overflowing_ceil(), (I1F31::NEG_ONE, false));
        assert_eq!(f.overflowing_floor(), (I1F31::NEG_ONE, false));
        assert_eq!(f.overflowing_round(), (I1F31::NEG_ONE, false));
        assert_eq!(f.overflowing_round_ties_even(), (I1F31::NEG_ONE, false));

        // -0.5 - Δ
        let f = I1F31::from_bits(((-1) << 30) - 1);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I1F31::NEG_ONE, false));
        assert_eq!(f.overflowing_round(), (I1F31::NEG_ONE, false));
        assert_eq!(f.overflowing_round_ties_even(), (I1F31::NEG_ONE, false));

        // -0.5
        let f = I1F31::from_bits((-1) << 30);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I1F31::NEG_ONE, false));
        assert_eq!(f.overflowing_round(), (I1F31::NEG_ONE, false));
        assert_eq!(f.overflowing_round_ties_even(), (I1F31::ZERO, false));

        // -0.5 + Δ
        let f = I1F31::from_bits(((-1) << 30) + 1);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I1F31::NEG_ONE, false));
        assert_eq!(f.overflowing_round(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_round_ties_even(), (I1F31::ZERO, false));

        // 0.5 - Δ
        let f = I1F31::from_bits((1 << 30) - 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::NEG_ONE, true));
        assert_eq!(f.overflowing_floor(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_round(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_round_ties_even(), (I1F31::ZERO, false));

        // 0.5
        let f = I1F31::from_bits(1 << 30);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::NEG_ONE, true));
        assert_eq!(f.overflowing_floor(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_round(), (I1F31::NEG_ONE, true));
        assert_eq!(f.overflowing_round_ties_even(), (I1F31::ZERO, false));

        // 0
        let f = I1F31::from_bits(0);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_round(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_round_ties_even(), (I1F31::ZERO, false));

        // 0.5 + Δ
        let f = I1F31::from_bits((1 << 30) + 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::NEG_ONE, true));
        assert_eq!(f.overflowing_floor(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_round(), (I1F31::NEG_ONE, true));
        assert_eq!(f.overflowing_round_ties_even(), (I1F31::NEG_ONE, true));

        // -3.5 - Δ
        let f = I16F16::from_bits(((-7) << 15) - 1);
        assert_eq!(f.to_num::<i32>(), -4);
        assert_eq!(f.round_to_zero(), -3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(-3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(-4), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(-4), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (I16F16::from_num(-4), false)
        );

        // -3.5
        let f = I16F16::from_bits((-7) << 15);
        assert_eq!(f.to_num::<i32>(), -4);
        assert_eq!(f.round_to_zero(), -3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(-3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(-4), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(-4), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (I16F16::from_num(-4), false)
        );

        // -3.5 + Δ
        let f = I16F16::from_bits(((-7) << 15) + 1);
        assert_eq!(f.to_num::<i32>(), -4);
        assert_eq!(f.round_to_zero(), -3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(-3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(-4), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(-3), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (I16F16::from_num(-3), false)
        );

        // -2.5 - Δ
        let f = I16F16::from_bits(((-5) << 15) - 1);
        assert_eq!(f.to_num::<i32>(), -3);
        assert_eq!(f.round_to_zero(), -2);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(-2), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(-3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(-3), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (I16F16::from_num(-3), false)
        );

        // -2.5
        let f = I16F16::from_bits((-5) << 15);
        assert_eq!(f.to_num::<i32>(), -3);
        assert_eq!(f.round_to_zero(), -2);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(-2), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(-3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(-3), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (I16F16::from_num(-2), false)
        );

        // -2.5 + Δ
        let f = I16F16::from_bits(((-5) << 15) + 1);
        assert_eq!(f.to_num::<i32>(), -3);
        assert_eq!(f.round_to_zero(), -2);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(-2), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(-3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(-2), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (I16F16::from_num(-2), false)
        );

        // -1
        let f = I16F16::from_bits((-1) << 16);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), -1);
        assert_eq!(f.overflowing_ceil(), (I16F16::NEG_ONE, false));
        assert_eq!(f.overflowing_floor(), (I16F16::NEG_ONE, false));
        assert_eq!(f.overflowing_round(), (I16F16::NEG_ONE, false));
        assert_eq!(f.overflowing_round_ties_even(), (I16F16::NEG_ONE, false));

        // -0.5 - Δ
        let f = I16F16::from_bits(((-1) << 15) - 1);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I16F16::NEG_ONE, false));
        assert_eq!(f.overflowing_round(), (I16F16::NEG_ONE, false));
        assert_eq!(f.overflowing_round_ties_even(), (I16F16::NEG_ONE, false));

        // -0.5
        let f = I16F16::from_bits((-1) << 15);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I16F16::NEG_ONE, false));
        assert_eq!(f.overflowing_round(), (I16F16::NEG_ONE, false));
        assert_eq!(f.overflowing_round_ties_even(), (I16F16::ZERO, false));

        // -0.5 + Δ
        let f = I16F16::from_bits(((-1) << 15) + 1);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I16F16::NEG_ONE, false));
        assert_eq!(f.overflowing_round(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_round_ties_even(), (I16F16::ZERO, false));

        // 0
        let f = I16F16::from_bits(0);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_round(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_round_ties_even(), (I16F16::ZERO, false));

        // 0.5 - Δ
        let f = I16F16::from_bits((1 << 15) - 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::ONE, false));
        assert_eq!(f.overflowing_floor(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_round(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_round_ties_even(), (I16F16::ZERO, false));

        // 0.5
        let f = I16F16::from_bits(1 << 15);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::ONE, false));
        assert_eq!(f.overflowing_floor(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_round(), (I16F16::ONE, false));
        assert_eq!(f.overflowing_round_ties_even(), (I16F16::ZERO, false));

        // 0.5 + Δ
        let f = I16F16::from_bits((1 << 15) + 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::ONE, false));
        assert_eq!(f.overflowing_floor(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_round(), (I16F16::ONE, false));
        assert_eq!(f.overflowing_round_ties_even(), (I16F16::ONE, false));

        // 1
        let f = I16F16::from_bits(1 << 16);
        assert_eq!(f.to_num::<i32>(), 1);
        assert_eq!(f.round_to_zero(), 1);
        assert_eq!(f.overflowing_ceil(), (I16F16::ONE, false));
        assert_eq!(f.overflowing_floor(), (I16F16::ONE, false));
        assert_eq!(f.overflowing_round(), (I16F16::ONE, false));
        assert_eq!(f.overflowing_round_ties_even(), (I16F16::ONE, false));

        // 2.5 - Δ
        let f = I16F16::from_bits((5 << 15) - 1);
        assert_eq!(f.to_num::<i32>(), 2);
        assert_eq!(f.round_to_zero(), 2);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(2), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(2), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (I16F16::from_num(2), false)
        );

        // 2.5
        let f = I16F16::from_bits(5 << 15);
        assert_eq!(f.to_num::<i32>(), 2);
        assert_eq!(f.round_to_zero(), 2);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(2), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(3), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (I16F16::from_num(2), false)
        );

        // 2.5 + Δ
        let f = I16F16::from_bits((5 << 15) + 1);
        assert_eq!(f.to_num::<i32>(), 2);
        assert_eq!(f.round_to_zero(), 2);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(2), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(3), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (I16F16::from_num(3), false)
        );

        // 3.5 - Δ
        let f = I16F16::from_bits((7 << 15) - 1);
        assert_eq!(f.to_num::<i32>(), 3);
        assert_eq!(f.round_to_zero(), 3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(4), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(3), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (I16F16::from_num(3), false)
        );

        // 3.5
        let f = I16F16::from_bits(7 << 15);
        assert_eq!(f.to_num::<i32>(), 3);
        assert_eq!(f.round_to_zero(), 3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(4), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(4), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (I16F16::from_num(4), false)
        );

        // 3.5 + Δ
        let f = I16F16::from_bits((7 << 15) + 1);
        assert_eq!(f.to_num::<i32>(), 3);
        assert_eq!(f.round_to_zero(), 3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(4), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(4), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (I16F16::from_num(4), false)
        );
    }

    #[test]
    fn rounding_unsigned() {
        // 0
        let f = U0F32::from_bits(0);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U0F32::ZERO, false));
        assert_eq!(f.overflowing_floor(), (U0F32::ZERO, false));
        assert_eq!(f.overflowing_round(), (U0F32::ZERO, false));
        assert_eq!(f.overflowing_round_ties_even(), (U0F32::ZERO, false));

        // 0.5 - Δ
        let f = U0F32::from_bits((1 << 31) - 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U0F32::ZERO, true));
        assert_eq!(f.overflowing_floor(), (U0F32::ZERO, false));
        assert_eq!(f.overflowing_round(), (U0F32::ZERO, false));
        assert_eq!(f.overflowing_round_ties_even(), (U0F32::ZERO, false));

        // 0.5
        let f = U0F32::from_bits(1 << 31);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U0F32::ZERO, true));
        assert_eq!(f.overflowing_floor(), (U0F32::ZERO, false));
        assert_eq!(f.overflowing_round(), (U0F32::ZERO, true));
        assert_eq!(f.overflowing_round_ties_even(), (U0F32::ZERO, false));

        // 0.5 + Δ
        let f = U0F32::from_bits((1 << 31) + 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U0F32::ZERO, true));
        assert_eq!(f.overflowing_floor(), (U0F32::ZERO, false));
        assert_eq!(f.overflowing_round(), (U0F32::ZERO, true));
        assert_eq!(f.overflowing_round_ties_even(), (U0F32::ZERO, true));

        // 0
        let f = U16F16::from_bits(0);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U16F16::ZERO, false));
        assert_eq!(f.overflowing_floor(), (U16F16::ZERO, false));
        assert_eq!(f.overflowing_round(), (U16F16::ZERO, false));
        assert_eq!(f.overflowing_round_ties_even(), (U16F16::ZERO, false));

        // 0.5 - Δ
        let f = U16F16::from_bits((1 << 15) - 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U16F16::ONE, false));
        assert_eq!(f.overflowing_floor(), (U16F16::ZERO, false));
        assert_eq!(f.overflowing_round(), (U16F16::ZERO, false));
        assert_eq!(f.overflowing_round_ties_even(), (U16F16::ZERO, false));

        // 0.5
        let f = U16F16::from_bits(1 << 15);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U16F16::ONE, false));
        assert_eq!(f.overflowing_floor(), (U16F16::ZERO, false));
        assert_eq!(f.overflowing_round(), (U16F16::ONE, false));
        assert_eq!(f.overflowing_round_ties_even(), (U16F16::ZERO, false));

        // 0.5 + Δ
        let f = U16F16::from_bits((1 << 15) + 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U16F16::ONE, false));
        assert_eq!(f.overflowing_floor(), (U16F16::ZERO, false));
        assert_eq!(f.overflowing_round(), (U16F16::ONE, false));
        assert_eq!(f.overflowing_round_ties_even(), (U16F16::ONE, false));

        // 1
        let f = U16F16::from_bits(1 << 16);
        assert_eq!(f.to_num::<i32>(), 1);
        assert_eq!(f.round_to_zero(), 1);
        assert_eq!(f.overflowing_ceil(), (U16F16::ONE, false));
        assert_eq!(f.overflowing_floor(), (U16F16::ONE, false));
        assert_eq!(f.overflowing_round(), (U16F16::ONE, false));
        assert_eq!(f.overflowing_round_ties_even(), (U16F16::ONE, false));

        // 2.5 - Δ
        let f = U16F16::from_bits((5 << 15) - 1);
        assert_eq!(f.to_num::<i32>(), 2);
        assert_eq!(f.round_to_zero(), 2);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_num(3), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_num(2), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_num(2), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (U16F16::from_num(2), false)
        );

        // 2.5
        let f = U16F16::from_bits(5 << 15);
        assert_eq!(f.to_num::<i32>(), 2);
        assert_eq!(f.round_to_zero(), 2);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_num(3), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_num(2), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_num(3), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (U16F16::from_num(2), false)
        );

        // 2.5 + Δ
        let f = U16F16::from_bits((5 << 15) + 1);
        assert_eq!(f.to_num::<i32>(), 2);
        assert_eq!(f.round_to_zero(), 2);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_num(3), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_num(2), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_num(3), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (U16F16::from_num(3), false)
        );

        // 3.5 - Δ
        let f = U16F16::from_bits((7 << 15) - 1);
        assert_eq!(f.to_num::<i32>(), 3);
        assert_eq!(f.round_to_zero(), 3);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_num(4), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_num(3), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_num(3), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (U16F16::from_num(3), false)
        );

        // 3.5
        let f = U16F16::from_bits(7 << 15);
        assert_eq!(f.to_num::<i32>(), 3);
        assert_eq!(f.round_to_zero(), 3);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_num(4), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_num(3), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_num(4), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (U16F16::from_num(4), false)
        );

        // 3.5 + Δ
        let f = U16F16::from_bits((7 << 15) + 1);
        assert_eq!(f.to_num::<i32>(), 3);
        assert_eq!(f.round_to_zero(), 3);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_num(4), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_num(3), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_num(4), false));
        assert_eq!(
            f.overflowing_round_ties_even(),
            (U16F16::from_num(4), false)
        );
    }

    #[test]
    fn reciprocals() {
        // 4/3 wraps to 1/3 = 0x0.5555_5555
        assert_eq!(
            U0F32::from_num(0.75).overflowing_recip(),
            (U0F32::from_bits(0x5555_5555), true)
        );
        // 8/3 wraps to 2/3 = 0x0.AAAA_AAAA
        assert_eq!(
            U0F32::from_num(0.375).overflowing_recip(),
            (U0F32::from_bits(0xAAAA_AAAA), true)
        );

        // 8/3 wraps to 2/3 = 0x0.AAAA_AAAA, which is -0x0.5555_5556
        assert_eq!(
            I0F32::from_num(0.375).overflowing_recip(),
            (I0F32::from_bits(-0x5555_5556), true)
        );
        assert_eq!(
            I0F32::from_num(-0.375).overflowing_recip(),
            (I0F32::from_bits(0x5555_5556), true)
        );
        // -2 wraps to 0
        assert_eq!(
            I0F32::from_num(-0.5).overflowing_recip(),
            (I0F32::ZERO, true)
        );

        // 8/3 wraps to 2/3 = 0x0.AAAA_AAAA (bits 0x5555_5555)
        assert_eq!(
            I1F31::from_num(0.375).overflowing_recip(),
            (I1F31::from_bits(0x5555_5555), true)
        );
        assert_eq!(
            I1F31::from_num(-0.375).overflowing_recip(),
            (I1F31::from_bits(-0x5555_5555), true)
        );
        // 4/3 = 0x1.5555_5554 (bits 0xAAAA_AAAA, or -0x5555_5556)
        assert_eq!(
            I1F31::from_num(0.75).overflowing_recip(),
            (I1F31::from_bits(-0x5555_5556), true)
        );
        assert_eq!(
            I1F31::from_num(-0.75).overflowing_recip(),
            (I1F31::from_bits(0x5555_5556), true)
        );
        // -2 wraps to 0
        assert_eq!(
            I1F31::from_num(-0.5).overflowing_recip(),
            (I1F31::ZERO, true)
        );
        // -1 does not overflow
        assert_eq!(I1F31::NEG_ONE.overflowing_recip(), (I1F31::NEG_ONE, false));
    }

    #[test]
    fn wide_mul_mixed() {
        // +7FFF.FFFF * 7FFF.FFFF = +3FFF_FFFE.0000_0001
        // 7FFF.FFFF * 7FFF.FFFF = 3FFF_FFFE.0000_0001
        // +7FFF.FFFF * +7FFF.FFFF = +3FFF_FFFE.0000_0001
        let s = I16F16::MAX;
        let u = U16F16::MAX >> 1u32;
        let t = U16F16::from_bits(s.to_bits() as u32);
        let v = I16F16::from_bits(u.to_bits() as i32);
        assert_eq!(s.wide_mul_unsigned(u).to_bits(), 0x3FFF_FFFF_0000_0001);
        assert_eq!(t.wide_mul(u).to_bits(), 0x3FFF_FFFF_0000_0001);
        assert_eq!(s.wide_mul(v).to_bits(), 0x3FFF_FFFF_0000_0001);
        assert_eq!(s.wide_mul_unsigned(u), u.wide_mul_signed(s));
        assert_eq!(t.wide_mul(u), u.wide_mul(t));
        assert_eq!(s.wide_mul(v), v.wide_mul(s));

        // +7FFF.FFFF * 8000.0000 = +3FFF_FFFF.8000_0000
        // 7FFF.FFFF * 8000.0000 = 3FFF_FFFF.8000_0000
        // +7FFF.FFFF * -8000.0000 = -3FFF_FFFF.8000_0000
        let s = I16F16::MAX;
        let u = !(U16F16::MAX >> 1u32);
        let t = U16F16::from_bits(s.to_bits() as u32);
        let v = I16F16::from_bits(u.to_bits() as i32);
        assert_eq!(s.wide_mul_unsigned(u).to_bits(), 0x3FFF_FFFF_8000_0000);
        assert_eq!(t.wide_mul(u).to_bits(), 0x3FFF_FFFF_8000_0000);
        assert_eq!(s.wide_mul(v).to_bits(), -0x3FFF_FFFF_8000_0000);
        assert_eq!(s.wide_mul_unsigned(u), u.wide_mul_signed(s));
        assert_eq!(t.wide_mul(u), u.wide_mul(t));
        assert_eq!(s.wide_mul(v), v.wide_mul(s));

        // +7FFF.FFFF * FFFF.FFFF = +7FFF_FFFE.8000_0001
        // 7FFF.FFFF * FFFF.FFFF = 7FFF_FFFE.8000_0001
        // +7FFF.FFFF * -0000.0001 = -0000_0000.7FFF_FFFF
        let s = I16F16::MAX;
        let u = U16F16::MAX;
        let t = U16F16::from_bits(s.to_bits() as u32);
        let v = I16F16::from_bits(u.to_bits() as i32);
        assert_eq!(s.wide_mul_unsigned(u).to_bits(), 0x7FFF_FFFE_8000_0001);
        assert_eq!(t.wide_mul(u).to_bits(), 0x7FFF_FFFE_8000_0001);
        assert_eq!(s.wide_mul(v).to_bits(), -0x0000_0000_7FFF_FFFF);
        assert_eq!(s.wide_mul_unsigned(u), u.wide_mul_signed(s));
        assert_eq!(t.wide_mul(u), u.wide_mul(t));
        assert_eq!(s.wide_mul(v), v.wide_mul(s));

        // -8000.0000 * 7FFF.FFFF = -3FFF_FFFF.8000_0000
        // 8000.0000 * 7FFF.FFFF = 3FFF_FFFF.8000_0000
        // -8000.0000 * +7FFF.FFFF = -3FFF_FFFF.8000_0000
        let s = I16F16::MIN;
        let u = U16F16::MAX >> 1u32;
        let t = U16F16::from_bits(s.to_bits() as u32);
        let v = I16F16::from_bits(u.to_bits() as i32);
        assert_eq!(s.wide_mul_unsigned(u).to_bits(), -0x3FFF_FFFF_8000_0000);
        assert_eq!(t.wide_mul(u).to_bits(), 0x3FFF_FFFF_8000_0000);
        assert_eq!(s.wide_mul(v).to_bits(), -0x3FFF_FFFF_8000_0000);
        assert_eq!(s.wide_mul_unsigned(u), u.wide_mul_signed(s));
        assert_eq!(t.wide_mul(u), u.wide_mul(t));
        assert_eq!(s.wide_mul(v), v.wide_mul(s));

        // -8000.0000 * 8000.0000 = -4000_0000.0000_0000
        // 8000.0000 * 8000.0000 = 4000_0000.0000_0000
        // -8000.0000 * -8000.0000 = +4000_0000.0000_0000
        let s = I16F16::MIN;
        let u = !(U16F16::MAX >> 1u32);
        let t = U16F16::from_bits(s.to_bits() as u32);
        let v = I16F16::from_bits(u.to_bits() as i32);
        assert_eq!(s.wide_mul_unsigned(u).to_bits(), -0x4000_0000_0000_0000);
        assert_eq!(t.wide_mul(u).to_bits(), 0x4000_0000_0000_0000);
        assert_eq!(s.wide_mul(v).to_bits(), 0x4000_0000_0000_0000);
        assert_eq!(s.wide_mul_unsigned(u), u.wide_mul_signed(s));
        assert_eq!(t.wide_mul(u), u.wide_mul(t));
        assert_eq!(s.wide_mul(v), v.wide_mul(s));

        // -8000.0000 * FFFF.FFFF = -7FFF_FFFF.8000_0000
        // 8000.0000 * FFFF.FFFF = 7FFF_FFFF.8000_0000
        // -8000.0000 * -0000.0001 = +0000_0000.8000_0000
        let s = I16F16::MIN;
        let u = U16F16::MAX;
        let t = U16F16::from_bits(s.to_bits() as u32);
        let v = I16F16::from_bits(u.to_bits() as i32);
        assert_eq!(s.wide_mul_unsigned(u).to_bits(), -0x7FFF_FFFF_8000_0000);
        assert_eq!(t.wide_mul(u).to_bits(), 0x7FFF_FFFF_8000_0000);
        assert_eq!(s.wide_mul(v).to_bits(), 0x8000_0000);
        assert_eq!(s.wide_mul_unsigned(u), u.wide_mul_signed(s));
        assert_eq!(t.wide_mul(u), u.wide_mul(t));
        assert_eq!(s.wide_mul(v), v.wide_mul(s));

        // -0000.0001 * 7FFF.FFFF = -0000_0000.7FFF_FFFF
        // FFFF.FFFF * 7FFF.FFFF = 7FFF_FFFE.8000_0001
        // -0000.0001 * +7FFF.FFFF = -0000_0000.7FFF_FFFF
        let s = -I16F16::DELTA;
        let u = U16F16::MAX >> 1u32;
        let t = U16F16::from_bits(s.to_bits() as u32);
        let v = I16F16::from_bits(u.to_bits() as i32);
        assert_eq!(s.wide_mul_unsigned(u).to_bits(), -0x0000_0000_7FFF_FFFF);
        assert_eq!(t.wide_mul(u).to_bits(), 0x7FFF_FFFE_8000_0001);
        assert_eq!(s.wide_mul(v).to_bits(), -0x0000_0000_7FFF_FFFF);
        assert_eq!(s.wide_mul_unsigned(u), u.wide_mul_signed(s));
        assert_eq!(t.wide_mul(u), u.wide_mul(t));
        assert_eq!(s.wide_mul(v), v.wide_mul(s));

        // -0000.0001 * 8000.0000 = -0000_0000.8000_0000
        // FFFF.FFFF * 8000.0000 = 7FFF_FFFF.8000_0000
        // -0000.0001 * -8000.0000 = +0000_0000.8000_0000
        let s = -I16F16::DELTA;
        let u = !(U16F16::MAX >> 1u32);
        let t = U16F16::from_bits(s.to_bits() as u32);
        let v = I16F16::from_bits(u.to_bits() as i32);
        assert_eq!(s.wide_mul_unsigned(u).to_bits(), -0x0000_0000_8000_0000);
        assert_eq!(t.wide_mul(u).to_bits(), 0x7FFF_FFFF_8000_0000);
        assert_eq!(s.wide_mul(v).to_bits(), 0x0000_0000_8000_0000);
        assert_eq!(s.wide_mul_unsigned(u), u.wide_mul_signed(s));
        assert_eq!(t.wide_mul(u), u.wide_mul(t));
        assert_eq!(s.wide_mul(v), v.wide_mul(s));

        // -0000.0001 * FFFF.FFFF = -0000_0000.FFFF_FFFF
        // FFFF.FFFF * FFFF.FFFF = FFFF_FFFE.0000_0001
        // -0000.0001 * -0000.0001 = +0000_0000.0000_0001
        let s = -I16F16::DELTA;
        let u = U16F16::MAX;
        let t = U16F16::from_bits(s.to_bits() as u32);
        let v = I16F16::from_bits(u.to_bits() as i32);
        assert_eq!(s.wide_mul_unsigned(u).to_bits(), -0x0000_0000_FFFF_FFFF);
        assert_eq!(t.wide_mul(u).to_bits(), 0xFFFF_FFFE_0000_0001);
        assert_eq!(s.wide_mul(v).to_bits(), 0x0000_0000_0000_0001);
        assert_eq!(s.wide_mul_unsigned(u), u.wide_mul_signed(s));
        assert_eq!(t.wide_mul(u), u.wide_mul(t));
        assert_eq!(s.wide_mul(v), v.wide_mul(s));
    }
}
