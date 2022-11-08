// Copyright © 2018–2022 Trevor Spiteri

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
// <https://opensource.org/licenses/MIT>

/*!
# Fixed-point numbers

**Alpha:** This is an alpha release of the new major version 2.0.0 that makes
use of const generics instead of the [*typenum*
crate](https://crates.io/crate/typenum). This version requires the nightly
compiler with the [`generic_const_exprs` feature] enabled. The stable version
2.0.0 itself will not be released before the [`generic_const_exprs` feature] is
stabilized. See the documentation for [porting from version 1 to version 2].

[`generic_const_exprs` feature]: https://github.com/rust-lang/rust/issues/76560
[porting from version 1 to version 2]: #porting-from-version-1-to-version-2

The [*fixed* crate] provides fixed-point numbers.

  * [`FixedI8`] and [`FixedU8`] are eight-bit fixed-point numbers.
  * [`FixedI16`] and [`FixedU16`] are 16-bit fixed-point numbers.
  * [`FixedI32`] and [`FixedU32`] are 32-bit fixed-point numbers.
  * [`FixedI64`] and [`FixedU64`] are 64-bit fixed-point numbers.
  * [`FixedI128`] and [`FixedU128`] are 128-bit fixed-point numbers.

An <i>n</i>-bit fixed-point number has <i>f</i>&nbsp;=&nbsp;`FRAC` fractional
bits, and <i>n</i>&nbsp;&minus;&nbsp;<i>f</i> integer bits. For example,
<code>[FixedI32]\<24></code> is a 32-bit signed fixed-point number with
<i>n</i>&nbsp;=&nbsp;32 total bits, <i>f</i>&nbsp;=&nbsp;24 fractional bits, and
<i>n</i>&nbsp;&minus;&nbsp;<i>f</i>&nbsp;=&nbsp;8 integer bits.
<code>[FixedI32]\<0></code> behaves like [`i32`], and
<code>[FixedU32]\<0></code> behaves like [`u32`].

The difference between any two successive representable numbers is constant
throughout the possible range for a fixed-point number:
<i>Δ</i>&nbsp;=&nbsp;1/2<sup><i>f</i></sup>. When <i>f</i>&nbsp;=&nbsp;0, like
in <code>[FixedI32]\<0></code>, <i>Δ</i>&nbsp;=&nbsp;1 because representable
numbers are integers, and the difference between two successive integers is 1.
When <i>f</i>&nbsp;=&nbsp;<i>n</i>, <i>Δ</i>&nbsp;=&nbsp;1/2<sup><i>n</i></sup>
and the value lies in the range &minus;0.5&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;0.5
for signed numbers like <code>[FixedI32]\<32></code>, and in the range
0&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;1 for unsigned numbers like
<code>[FixedU32]\<32></code>.

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

  * No algebraic functions are provided, for example no `sqrt` or `pow`.
  * No trigonometric functions are provided, for example no `sin` or `cos`.
  * No other transcendental functions are provided, for example no `log` or
    `exp`.

These functions are not provided because different implementations can have
different trade-offs, for example trading some correctness for speed.
Implementations can be provided in other crates.

  * The [*fixed-sqrt* crate] provides the square root operation.
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
    [`Binary`], [`Octal`], [`LowerHex`] and [`UpperHex`]. The output is rounded
    to the nearest, with ties rounded to even.
  * All fixed-point numbers are plain old data, so [`bytemuck`] bit casting
    conversions can be used.

## Quick examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

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
and 12 fractional bits. It is an alias to <code>[FixedI32]\<12></code>. The
unsigned counterpart would be [`U20F12`]. Aliases are provided for all
combinations of integer and fractional bits adding up to a total of eight, 16,
32, 64 or 128 bits.

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

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

The parsing methods are available as `const` functions.

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::types::I16F16;

const TWELVE_POINT_75: I16F16 = I16F16::unwrapped_from_str("12.75");
// 1.1 binary is 1.5 decimal
const ONE_POINT_5: I16F16 = I16F16::unwrapped_from_str_binary("1.1");
// 12.75 + 1.5 = 14.25
let sum = TWELVE_POINT_75 + ONE_POINT_5;
assert_eq!(sum, 14.25);
```

The [*fixed-macro* crate] is an alternative which provides a convenient macro to
write down fixed-point constants literally in the code. It supports underscores
as separators, scientific notation, and binary/octal/hexadecimal integers, but
it does not support binary/octal/hexadecimal fractions as they cannot be parsed
by the Rust compiler.

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

# #[cfg(feature = "skip-this-test")] {
use fixed::types::I16F16;
use fixed_macro::fixed;

// 0.1275e2 is 12.75
const NUM1: I16F16 = fixed!(0.127_5e2: I16F16);
// 11 binary is 3 decimal
let num2 = NUM1 + fixed!(0b11: I16F16);
// 12.75 + 3 = 15.75
assert_eq!(num2, 15.75);
# }
```

## Using the *fixed* crate

The *fixed* crate is available on [crates.io][*fixed* crate]. To use it in your
crate, add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
fixed = "2.0.0-alpha.6"
```

This alpha version of the *fixed* crate requires the nightly compiler with the
[`generic_const_exprs` feature] enabled.

[`generic_const_exprs` feature]: https://github.com/rust-lang/rust/issues/76560

## Optional features

The *fixed* crate has these optional feature:

 1. `arbitrary`, disabled by default. This provides the generation of arbitrary
    fixed-point numbers from raw, unstructured data. This feature requires the
    [*arbitrary* crate].
 2. `serde`, disabled by default. This provides serialization support for the
    fixed-point types. This feature requires the [*serde* crate].
 3. `std`, disabled by default. This is for features that are not possible under
    `no_std`: currently the implementation of the [`Error`] trait for
    [`ParseFixedError`].
 4. `serde-str`, disabled by default. Fixed-point numbers are serialized as
    strings showing the value when using human-readable formats. This feature
    requires the `serde` and the `std` optional features. With this feature,
    serialization is only supported for fixed-point numbers where the number of
    fractional bits is from zero to the total number of bits. **Warning:**
    numbers serialized when this feature is enabled cannot be deserialized when
    this feature is disabled, and vice versa.

To enable features, you can add the dependency like this to [*Cargo.toml*]:

```toml
[dependencies.fixed]
version = "2.0.0-alpha.6"
features = ["serde"]
```

## Experimental optional features

It is not considered a breaking change if the following experimental features
are removed. The removal of experimental features would however require a minor
version bump. Similarly, on a minor version bump, optional dependencies can be
updated to an incompatible newer version.

 1. `borsh`, disabled by default. This implements serialization and
    deserialization using the [*borsh* crate]. (The plan is to promote this to
    an optional feature once the [*borsh* crate] reaches version 1.0.0.)
 2. `num-traits`, disabled by default. This implements some traits from the
    [*num-traits* crate]. (The plan is to promote this to an optional feature
    once the [*num-traits* crate] reaches version 1.0.0.)

## Porting from version 1 to version 2

To port from version 1 to version 2, the following is required:

  * Temporary change required until the [`generic_const_exprs` feature] are
    stabilized: use the nightly compiler and enable the [`generic_const_exprs`
    feature] using

    ```rust
    #![feature(generic_const_exprs)]
    # #![allow(incomplete_features)]
    ```

  * Use integer literals instead of typenum integer constants, for example
    <code>[FixedI32][`FixedI32`]&lt;8></code> instead of
    <code>[FixedI32][`FixedI32`]&lt;[U8]></code>.

    [U8]: https://docs.rs/fixed/1/fixed/types/extra/type.U8.html

  * The [`Fixed`] trait constraints have been relaxed, and the methods which
    needed the strict constraints have been moved to the subtrait
    [`FixedStrict`]. For code that uses these trait methods, [`Fixed`] should be
    replaced by [`FixedStrict`].

    [`Fixed`]: traits::Fixed
    [`FixedStrict`]: traits::FixedStrict

  * The [`FRAC_NBITS`] and [`INT_NBITS`] associated constants of type [`u32`]
    were replaced by [`FRAC_BITS`] and [`INT_BITS`] of type [`i32`].

    [`FRAC_BITS`]: FixedI32::FRAC_BITS
    [`FRAC_NBITS`]: https://docs.rs/fixed/1/fixed/struct.FixedI32.html#associatedconstant.FRAC_NBITS
    [`INT_BITS`]: FixedI32::INT_BITS
    [`INT_NBITS`]: https://docs.rs/fixed/1/fixed/struct.FixedI32.html#associatedconstant.INT_NBITS

  * The deprecated [`F128Bits`] struct has been removed. It was replaced by
    [`F128`] in version 1.18.0

    [`F128Bits`]: https://docs.rs/fixed/1/fixed/struct.F128Bits.html

  * For the [`Unwrapped`] wrapper, the methods [`from_str_binary`][u-fsb],
    [`from_str_octal`][u-fso] and [`from_str_hex`][u-fsh] return the value
    directly instead of a [`Result`].

    [u-fsb]: Unwrapped#method.from_str_binary
    [u-fsh]: Unwrapped#method.from_str_hex
    [u-fso]: Unwrapped#method.from_str_octal

  * The deprecated optional features `az` and `f16` were removed. These features
    had no effect, as their functionality has been unconditionally enabled since
    version 1.7.0.

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
[*fixed-macro* crate]: https://crates.io/crates/fixed-macro
[*fixed-sqrt* crate]: https://crates.io/crates/fixed-sqrt
[*half* crate]: https://crates.io/crates/half
[*num-traits* crate]: https://crates.io/crates/num-traits
[*serde* crate]: https://crates.io/crates/serde
[CORDIC]: https://en.wikipedia.org/wiki/CORDIC
[LICENSE-APACHE]: https://www.apache.org/licenses/LICENSE-2.0
[LICENSE-MIT]: https://opensource.org/licenses/MIT
[`Binary`]: core::fmt::Binary
[`Display`]: core::fmt::Display
[`Error`]: std::error::Error
[`FromStr`]: core::str::FromStr
[`I20F12`]: crate::types::I20F12
[`I4F12`]: crate::types::I4F12
[`I4F4`]: crate::types::I4F4
[`LosslessTryFrom`]: traits::LosslessTryFrom
[`LosslessTryInto`]: traits::LosslessTryInto
[`LossyFrom`]: traits::LossyFrom
[`LossyInto`]: traits::LossyInto
[`LowerHex`]: core::fmt::LowerHex
[`Octal`]: core::fmt::Octal
[`U20F12`]: types::U20F12
[`UpperHex`]: core::fmt::UpperHex
[`bf16`]: half::bf16
[`checked_from_num`]: FixedI32::checked_from_num
[`f16`]: half::f16
[`from_num`]: FixedI32::from_num
[`from_str_binary`]: FixedI32::from_str_binary
[`from_str_hex`]: FixedI32::from_str_hex
[`from_str_octal`]: FixedI32::from_str_octal
[`to_num`]: FixedI32::to_num
*/
#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]
#![warn(unsafe_op_in_unsafe_fn)]
#![doc(html_root_url = "https://docs.rs/fixed/2.0.0-alpha.6")]
#![doc(test(attr(deny(warnings))))]
#![cfg_attr(feature = "fail-on-warnings", deny(warnings))]
#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

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
pub mod consts;
mod convert;
mod debug_hex;
mod display;
pub mod f128;
mod fixed_from_bits;
mod float_helper;
mod from_str;
mod helpers;
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
#[cfg(feature = "serde")]
mod serdeize;
pub mod traits;
mod traits_bits;
pub mod types;
mod unwrapped;
mod wrapping;

#[cfg(feature = "num-traits")]
pub use crate::impl_num_traits::RadixParseFixedError;
pub use crate::{
    f128::private::F128, from_str::ParseFixedError, unwrapped::Unwrapped, wrapping::Wrapping,
};
use crate::{
    traits::{FromFixed, ToFixed},
    types::extra::{If, True},
};
use core::hash::{Hash, Hasher};

/// A prelude to import useful traits.
///
/// This prelude is similar to the [standard library’s prelude][std::prelude] in
/// that you’ll almost always want to import its entire contents, but unlike the
/// standard library’s prelude you’ll have to do so manually:
///
/// ```rust
/// #![feature(generic_const_exprs)]
/// # #![allow(incomplete_features)]
///
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
///     from/to fixed-point numbers.
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
        $description:expr,
        $Fixed:ident(
            $Inner:ident, $s_nbits:expr,
            $s_nbits_p1:expr, $s_nbits_m1:expr, $s_nbits_m2:expr, $s_nbits_m3:expr, $s_nbits_m4:expr
        ),
        $nbytes:expr, $nbits:expr, $nbits_m1:expr,
        $bytes_val:expr, $rev_bytes_val:expr, $be_bytes:expr, $le_bytes:expr,
        $IFixed:ident, $UFixed:ident, $IInner:ident, $UInner:ident, $Signedness:tt,
        $nbits_cm3:expr, $nbits_cm2:expr, $nbits_cm1:expr,
        $nbits_c0:expr, $nbits_c1:expr, $nbits_c2:expr, $nbits_c3:expr,
        $HasDouble:tt, $s_nbits_2:expr,
        $Double:ident, $DoubleInner:ty, $IDouble:ident, $IDoubleInner:ty
    ) => {
        fixed! {
            $description,
            $Fixed[stringify!($Fixed)](
                $Inner[stringify!($Inner)], $s_nbits,
                $s_nbits_p1, $s_nbits_m1, $s_nbits_m2, $s_nbits_m3, $s_nbits_m4
            ),
            $nbytes, $nbits, $nbits_m1,
            $bytes_val, $rev_bytes_val, $be_bytes, $le_bytes,
            $IFixed[stringify!($IFixed)], $UFixed[stringify!($UFixed)],
            $IInner, $UInner, $Signedness,
            $nbits_cm3, $nbits_cm2, $nbits_cm1, $nbits_c0, $nbits_c1, $nbits_c2, $nbits_c3,
            $HasDouble, $s_nbits_2,
            $Double[stringify!($Double)], $DoubleInner, $IDouble, $IDoubleInner
        }
    };
    (
        $description:expr,
        $Fixed:ident[$s_fixed:expr](
            $Inner:ident[$s_inner:expr], $s_nbits:expr,
            $s_nbits_p1:expr, $s_nbits_m1:expr, $s_nbits_m2:expr, $s_nbits_m3:expr, $s_nbits_m4:expr
        ),
        $nbytes:expr, $nbits:expr, $nbits_m1:expr,
        $bytes_val:expr, $rev_bytes_val:expr, $be_bytes:expr, $le_bytes:expr,
        $IFixed:ident[$s_ifixed:expr], $UFixed:ident[$s_ufixed:expr],
        $IInner:ident, $UInner:ident, $Signedness:tt,
        $nbits_cm3:expr, $nbits_cm2:expr, $nbits_cm1:expr,
        $nbits_c0:expr, $nbits_c1:expr, $nbits_c2:expr, $nbits_c3:expr,
        $HasDouble:tt, $s_nbits_2:expr,
        $Double:ident[$s_double:expr], $DoubleInner:ty, $IDouble:ident, $IDoubleInner:ty
    ) => {
        comment! {
            $description, "-bit ",
            if_signed_unsigned!($Signedness, "signed", "unsigned"),
            " number with `FRAC` fractional bits.

The number has ", $s_nbits, " bits, of which <i>f</i>&nbsp;=&nbsp;`FRAC` are
fractional bits and ", $s_nbits, "&nbsp;&minus;&nbsp;<i>f</i> are integer bits.
The value <i>x</i> can lie in the range ",
            if_signed_unsigned!(
                $Signedness,
                concat!("&minus;2<sup>", $s_nbits_m1, "</sup>/2<sup><i>f</i></sup>"),
                "0",
            ),
            "&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;2<sup>",
            if_signed_unsigned!($Signedness, $s_nbits_m1, $s_nbits),
            "</sup>/2<sup><i>f</i></sup>. The difference between successive
numbers is constant throughout the range: <i>Δ</i>&nbsp;=&nbsp;1/2<sup><i>f</i></sup>.

For <code>", $s_fixed, "\\<0></code>, <i>f</i>&nbsp;=&nbsp;0 and
<i>Δ</i>&nbsp;=&nbsp;1, and the fixed-point number behaves like ",
            if_signed_unsigned!($Signedness, "an", "a"),
            " [`", $s_inner, "`] with the value lying in the range ",
            if_signed_unsigned!(
                $Signedness,
                concat!("&minus;2<sup>", $s_nbits_m1, "</sup>"),
                "0",
            ),
            "&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;2<sup>",
            if_signed_unsigned!($Signedness, $s_nbits_m1, $s_nbits),
            "</sup>. For <code>", $s_fixed, "\\<", $s_nbits, "></code>,
<i>f</i>&nbsp;=&nbsp;", $s_nbits, " and
<i>Δ</i>&nbsp;=&nbsp;1/2<sup>", $s_nbits, "</sup>, and the value lies in the
range ",
            if_signed_unsigned!(
                $Signedness,
                "&minus;1/2&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;1/2",
                "0&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;1",
            ),
            ".

`", $s_fixed, "<FRAC>` has the same size, alignment and ABI as [`", $s_inner, "`];
it is `#[repr(transparent)]` with [`", $s_inner, "`] as the only non-zero-sized field.

# Examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::", $s_fixed, ";
let eleven = ", $s_fixed, "::<3>::from_num(11);
assert_eq!(eleven, ", $s_fixed, "::<3>::from_bits(11 << 3));
assert_eq!(eleven, 11);
assert_eq!(eleven.to_string(), \"11\");
let two_point_75 = eleven / 4;
assert_eq!(two_point_75, ", $s_fixed, "::<3>::from_bits(11 << 1));
assert_eq!(two_point_75, 2.75);
assert_eq!(two_point_75.to_string(), \"2.8\");
```
";
            #[repr(transparent)]
            pub struct $Fixed<const FRAC: i32> {
                pub(crate) bits: $Inner,
            }
        }

        impl<const FRAC: i32> Clone for $Fixed<FRAC> {
            #[inline]
            fn clone(&self) -> $Fixed<FRAC> {
                $Fixed { bits: self.bits }
            }
        }

        impl<const FRAC: i32> Copy for $Fixed<FRAC> {}

        impl<const FRAC: i32> Default for $Fixed<FRAC> {
            #[inline]
            fn default() -> Self {
                $Fixed {
                    bits: Default::default(),
                }
            }
        }

        impl<const FRAC: i32> Hash for $Fixed<FRAC> {
            #[inline]
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.bits.hash(state);
            }
        }

        // inherent methods that do not require FRAC bounds, some of which can thus be const
        fixed_no_frac! {
            $Fixed[$s_fixed](
                $Inner[$s_inner], $s_nbits, $s_nbits_p1, $s_nbits_m1, $s_nbits_m2, $s_nbits_m3
            ),
            $nbytes, $nbits, $nbits_m1, $bytes_val, $rev_bytes_val, $be_bytes, $le_bytes,
            $IFixed[$s_ifixed], $UFixed[$s_ufixed],
            $IInner, $UInner, $Signedness,
            $HasDouble, $s_nbits_2,
            $Double[$s_double], $DoubleInner, $IDouble, $IDoubleInner
        }
        // inherent methods that require FRAC bounds, and cannot be const
        fixed_frac! {
            $Fixed[$s_fixed]($Inner[$s_inner], $nbits, $s_nbits, $s_nbits_m1, $s_nbits_m4),
            $UFixed, $UInner, $Signedness
        }
        fixed_const! {
            $Fixed[$s_fixed]($nbits, $s_nbits, $s_nbits_m1, $s_nbits_m2, $s_nbits_m3, $s_nbits_m4),
            $nbits_cm3, $nbits_cm2, $nbits_cm1, $nbits_c0, $nbits_c1, $nbits_c2, $nbits_c3,
            $Signedness
        }
    };
}

fixed! {
    "An eight",
    FixedU8(u8, "8", "9", "7", "6", "5", "4"),
    1, 8, 7, "0x12", "0x12", "[0x12]", "[0x12]",
    FixedI8, FixedU8, i8, u8, Unsigned,
    11, 10, 9, 8, 7, 6, 5,
    True, "16", FixedU16, u16, FixedI16, i16
}
fixed! {
    "A 16",
    FixedU16(u16, "16", "17", "15", "14", "13", "12"),
    2, 16, 15, "0x1234", "0x3412", "[0x12, 0x34]", "[0x34, 0x12]",
    FixedI16, FixedU16, i16, u16, Unsigned,
    19, 18, 17, 16, 15, 14, 13,
    True, "32", FixedU32, u32, FixedI32, i32
}
fixed! {
    "A 32",
    FixedU32(u32, "32", "33", "31", "30", "29", "28"),
    4, 32, 31, "0x1234_5678", "0x7856_3412", "[0x12, 0x34, 0x56, 0x78]", "[0x78, 0x56, 0x34, 0x12]",
    FixedI32, FixedU32, i32, u32, Unsigned,
    35, 34, 33, 32, 31, 30, 29,
    True, "64", FixedU64, u64, FixedI64, i64
}
fixed! {
    "A 64",
    FixedU64(u64, "64", "65", "63", "62", "61", "60"),
    8, 64, 63, "0x1234_5678_9ABC_DE0F", "0x0FDE_BC9A_7856_3412",
    "[0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0x0F]",
    "[0x0F, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]",
    FixedI64, FixedU64, i64, u64, Unsigned,
    67, 66, 65, 64, 63, 62, 61,
    True, "128", FixedU128, u128, FixedI128, i128
}
fixed! {
    "A 128",
    FixedU128(u128, "128", "129", "127", "126", "125", "124"),
    16, 128, 127, "0x1234_5678_9ABC_DEF0_0102_0304_0506_0708",
    "0x0807_0605_0403_0201_F0DE_BC9A_7856_3412",
    "[0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0, \
     0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]",
    "[0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01, \
     0xF0, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]",
    FixedI128, FixedU128, i128, u128, Unsigned,
    131, 130, 129, 128, 127, 126, 125,
    False, "128", FixedU128, u128, FixedI128, i128
}
fixed! {
    "An eight",
    FixedI8(i8, "8", "9", "7", "6", "5", "4"),
    1, 8, 7, "0x12", "0x12", "[0x12]", "[0x12]",
    FixedI8, FixedU8, i8, u8, Signed,
    10, 9, 8, 7, 6, 5, 4,
    True, "16", FixedI16, i16, FixedI16, i16
}
fixed! {
    "A 16",
    FixedI16(i16, "16", "17", "15", "14", "13", "12"),
    2, 16, 15, "0x1234", "0x3412", "[0x12, 0x34]", "[0x34, 0x12]",
    FixedI16, FixedU16, i16, u16, Signed,
    18, 17, 16, 15, 14, 13, 12,
    True, "32", FixedI32, i32, FixedI32, i32
}
fixed! {
    "A 32",
    FixedI32(i32, "32", "33", "31", "30", "29", "28"),
    4, 32, 31, "0x1234_5678", "0x7856_3412", "[0x12, 0x34, 0x56, 0x78]", "[0x78, 0x56, 0x34, 0x12]",
    FixedI32, FixedU32, i32, u32, Signed,
    34, 33, 32, 31, 30, 29, 28,
    True, "64", FixedI64, i64, FixedI64, i64
}
fixed! {
    "A 64",
    FixedI64(i64, "64", "65", "63", "62", "61", "60"),
    8, 64, 63, "0x1234_5678_9ABC_DE0F", "0x0FDE_BC9A_7856_3412",
    "[0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0x0F]",
    "[0x0F, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]",
    FixedI64, FixedU64, i64, u64, Signed,
    66, 65, 64, 63, 62, 61, 60,
    True, "128", FixedI128, i128, FixedI128, i128
}
fixed! {
    "A 128",
    FixedI128(i128, "128", "129", "127", "126", "125", "124"),
    16, 128, 127, "0x1234_5678_9ABC_DEF0_0102_0304_0506_0708",
    "0x0807_0605_0403_0201_F0DE_BC9A_7856_3412",
    "[0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0, \
     0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]",
    "[0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01, \
     0xF0, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]",
    FixedI128, FixedU128, i128, u128, Signed,
    130, 129, 128, 127, 126, 125, 124,
    False, "128", FixedI128, i128, FixedI128, i128
}

/// These are doc tests that should not appear in the docs, but are useful as
/// doc tests can check to ensure compilation failure.
///
/// The first snippet succeeds, and acts as a control.
///
/// ```rust
/// #![feature(generic_const_exprs)]
/// # #![allow(incomplete_features)]
///
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
/// #![feature(generic_const_exprs)]
/// # #![allow(incomplete_features)]
///
/// use fixed::types::*;
/// const _ONE: I0F32 = I0F32::const_from_int(1);
/// ```
/// ```rust,compile_fail
/// #![feature(generic_const_exprs)]
/// # #![allow(incomplete_features)]
///
/// use fixed::types::*;
/// const _ONE: I1F31 = I1F31::const_from_int(1);
/// ```
/// ```rust,compile_fail
/// #![feature(generic_const_exprs)]
/// # #![allow(incomplete_features)]
///
/// use fixed::types::*;
/// const _ONE: U0F32 = U0F32::const_from_int(1);
/// ```
///
/// Not enough integer bits for -1.
/// ```rust,compile_fail
/// #![feature(generic_const_exprs)]
/// # #![allow(incomplete_features)]
///
/// use fixed::types::*;
/// const _MINUS_ONE: I0F32 = I0F32::const_from_int(-1);
/// ```
///
/// Not enough integer bits for -2.
/// ```rust,compile_fail
/// #![feature(generic_const_exprs)]
/// # #![allow(incomplete_features)]
///
/// use fixed::types::*;
/// const _MINUS_TWO: I1F31 = I1F31::const_from_int(-2);
/// ```
fn _compile_fail_tests() {}

#[cfg(test)]
mod tests {
    use crate::types::{I0F32, I16F16, I1F31, U0F32, U16F16};

    #[test]
    fn rounding_signed() {
        // -0.5
        let f = I0F32::from_bits(-1 << 31);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I0F32::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I0F32::ZERO, true));
        assert_eq!(f.overflowing_round(), (I0F32::ZERO, true));
        assert_eq!(f.overflowing_round_ties_to_even(), (I0F32::ZERO, false));

        // -0.5 + Δ
        let f = I0F32::from_bits((-1 << 31) + 1);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I0F32::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I0F32::ZERO, true));
        assert_eq!(f.overflowing_round(), (I0F32::ZERO, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I0F32::ZERO, false));

        // 0
        let f = I0F32::from_bits(0);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I0F32::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I0F32::ZERO, false));
        assert_eq!(f.overflowing_round(), (I0F32::ZERO, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I0F32::ZERO, false));

        // 0.5 - Δ
        let f = I0F32::from_bits((1 << 30) - 1 + (1 << 30));
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I0F32::ZERO, true));
        assert_eq!(f.overflowing_floor(), (I0F32::ZERO, false));
        assert_eq!(f.overflowing_round(), (I0F32::ZERO, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I0F32::ZERO, false));

        // -1
        let f = I1F31::from_bits((-1) << 31);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), -1);
        assert_eq!(f.overflowing_ceil(), (I1F31::NEG_ONE, false));
        assert_eq!(f.overflowing_floor(), (I1F31::NEG_ONE, false));
        assert_eq!(f.overflowing_round(), (I1F31::NEG_ONE, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I1F31::NEG_ONE, false));

        // -0.5 - Δ
        let f = I1F31::from_bits(((-1) << 30) - 1);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I1F31::NEG_ONE, false));
        assert_eq!(f.overflowing_round(), (I1F31::NEG_ONE, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I1F31::NEG_ONE, false));

        // -0.5
        let f = I1F31::from_bits((-1) << 30);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I1F31::NEG_ONE, false));
        assert_eq!(f.overflowing_round(), (I1F31::NEG_ONE, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I1F31::ZERO, false));

        // -0.5 + Δ
        let f = I1F31::from_bits(((-1) << 30) + 1);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I1F31::NEG_ONE, false));
        assert_eq!(f.overflowing_round(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I1F31::ZERO, false));

        // 0.5 - Δ
        let f = I1F31::from_bits((1 << 30) - 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::NEG_ONE, true));
        assert_eq!(f.overflowing_floor(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_round(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I1F31::ZERO, false));

        // 0.5
        let f = I1F31::from_bits(1 << 30);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::NEG_ONE, true));
        assert_eq!(f.overflowing_floor(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_round(), (I1F31::NEG_ONE, true));
        assert_eq!(f.overflowing_round_ties_to_even(), (I1F31::ZERO, false));

        // 0
        let f = I1F31::from_bits(0);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_round(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I1F31::ZERO, false));

        // 0.5 + Δ
        let f = I1F31::from_bits((1 << 30) + 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I1F31::NEG_ONE, true));
        assert_eq!(f.overflowing_floor(), (I1F31::ZERO, false));
        assert_eq!(f.overflowing_round(), (I1F31::NEG_ONE, true));
        assert_eq!(f.overflowing_round_ties_to_even(), (I1F31::NEG_ONE, true));

        // -3.5 - Δ
        let f = I16F16::from_bits(((-7) << 15) - 1);
        assert_eq!(f.to_num::<i32>(), -4);
        assert_eq!(f.round_to_zero(), -3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(-3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(-4), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(-4), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
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
            f.overflowing_round_ties_to_even(),
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
            f.overflowing_round_ties_to_even(),
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
            f.overflowing_round_ties_to_even(),
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
            f.overflowing_round_ties_to_even(),
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
            f.overflowing_round_ties_to_even(),
            (I16F16::from_num(-2), false)
        );

        // -1
        let f = I16F16::from_bits((-1) << 16);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), -1);
        assert_eq!(f.overflowing_ceil(), (I16F16::NEG_ONE, false));
        assert_eq!(f.overflowing_floor(), (I16F16::NEG_ONE, false));
        assert_eq!(f.overflowing_round(), (I16F16::NEG_ONE, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I16F16::NEG_ONE, false));

        // -0.5 - Δ
        let f = I16F16::from_bits(((-1) << 15) - 1);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I16F16::NEG_ONE, false));
        assert_eq!(f.overflowing_round(), (I16F16::NEG_ONE, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I16F16::NEG_ONE, false));

        // -0.5
        let f = I16F16::from_bits((-1) << 15);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I16F16::NEG_ONE, false));
        assert_eq!(f.overflowing_round(), (I16F16::NEG_ONE, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I16F16::ZERO, false));

        // -0.5 + Δ
        let f = I16F16::from_bits(((-1) << 15) + 1);
        assert_eq!(f.to_num::<i32>(), -1);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I16F16::NEG_ONE, false));
        assert_eq!(f.overflowing_round(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I16F16::ZERO, false));

        // 0
        let f = I16F16::from_bits(0);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_floor(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_round(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I16F16::ZERO, false));

        // 0.5 - Δ
        let f = I16F16::from_bits((1 << 15) - 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::ONE, false));
        assert_eq!(f.overflowing_floor(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_round(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I16F16::ZERO, false));

        // 0.5
        let f = I16F16::from_bits(1 << 15);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::ONE, false));
        assert_eq!(f.overflowing_floor(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_round(), (I16F16::ONE, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I16F16::ZERO, false));

        // 0.5 + Δ
        let f = I16F16::from_bits((1 << 15) + 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::ONE, false));
        assert_eq!(f.overflowing_floor(), (I16F16::ZERO, false));
        assert_eq!(f.overflowing_round(), (I16F16::ONE, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I16F16::ONE, false));

        // 1
        let f = I16F16::from_bits(1 << 16);
        assert_eq!(f.to_num::<i32>(), 1);
        assert_eq!(f.round_to_zero(), 1);
        assert_eq!(f.overflowing_ceil(), (I16F16::ONE, false));
        assert_eq!(f.overflowing_floor(), (I16F16::ONE, false));
        assert_eq!(f.overflowing_round(), (I16F16::ONE, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (I16F16::ONE, false));

        // 2.5 - Δ
        let f = I16F16::from_bits((5 << 15) - 1);
        assert_eq!(f.to_num::<i32>(), 2);
        assert_eq!(f.round_to_zero(), 2);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_num(3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_num(2), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_num(2), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
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
            f.overflowing_round_ties_to_even(),
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
            f.overflowing_round_ties_to_even(),
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
            f.overflowing_round_ties_to_even(),
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
            f.overflowing_round_ties_to_even(),
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
            f.overflowing_round_ties_to_even(),
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
        assert_eq!(f.overflowing_round_ties_to_even(), (U0F32::ZERO, false));

        // 0.5 - Δ
        let f = U0F32::from_bits((1 << 31) - 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U0F32::ZERO, true));
        assert_eq!(f.overflowing_floor(), (U0F32::ZERO, false));
        assert_eq!(f.overflowing_round(), (U0F32::ZERO, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (U0F32::ZERO, false));

        // 0.5
        let f = U0F32::from_bits(1 << 31);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U0F32::ZERO, true));
        assert_eq!(f.overflowing_floor(), (U0F32::ZERO, false));
        assert_eq!(f.overflowing_round(), (U0F32::ZERO, true));
        assert_eq!(f.overflowing_round_ties_to_even(), (U0F32::ZERO, false));

        // 0.5 + Δ
        let f = U0F32::from_bits((1 << 31) + 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U0F32::ZERO, true));
        assert_eq!(f.overflowing_floor(), (U0F32::ZERO, false));
        assert_eq!(f.overflowing_round(), (U0F32::ZERO, true));
        assert_eq!(f.overflowing_round_ties_to_even(), (U0F32::ZERO, true));

        // 0
        let f = U16F16::from_bits(0);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U16F16::ZERO, false));
        assert_eq!(f.overflowing_floor(), (U16F16::ZERO, false));
        assert_eq!(f.overflowing_round(), (U16F16::ZERO, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (U16F16::ZERO, false));

        // 0.5 - Δ
        let f = U16F16::from_bits((1 << 15) - 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U16F16::ONE, false));
        assert_eq!(f.overflowing_floor(), (U16F16::ZERO, false));
        assert_eq!(f.overflowing_round(), (U16F16::ZERO, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (U16F16::ZERO, false));

        // 0.5
        let f = U16F16::from_bits(1 << 15);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U16F16::ONE, false));
        assert_eq!(f.overflowing_floor(), (U16F16::ZERO, false));
        assert_eq!(f.overflowing_round(), (U16F16::ONE, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (U16F16::ZERO, false));

        // 0.5 + Δ
        let f = U16F16::from_bits((1 << 15) + 1);
        assert_eq!(f.to_num::<i32>(), 0);
        assert_eq!(f.round_to_zero(), 0);
        assert_eq!(f.overflowing_ceil(), (U16F16::ONE, false));
        assert_eq!(f.overflowing_floor(), (U16F16::ZERO, false));
        assert_eq!(f.overflowing_round(), (U16F16::ONE, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (U16F16::ONE, false));

        // 1
        let f = U16F16::from_bits(1 << 16);
        assert_eq!(f.to_num::<i32>(), 1);
        assert_eq!(f.round_to_zero(), 1);
        assert_eq!(f.overflowing_ceil(), (U16F16::ONE, false));
        assert_eq!(f.overflowing_floor(), (U16F16::ONE, false));
        assert_eq!(f.overflowing_round(), (U16F16::ONE, false));
        assert_eq!(f.overflowing_round_ties_to_even(), (U16F16::ONE, false));

        // 2.5 - Δ
        let f = U16F16::from_bits((5 << 15) - 1);
        assert_eq!(f.to_num::<i32>(), 2);
        assert_eq!(f.round_to_zero(), 2);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_num(3), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_num(2), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_num(2), false));
        assert_eq!(
            f.overflowing_round_ties_to_even(),
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
            f.overflowing_round_ties_to_even(),
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
            f.overflowing_round_ties_to_even(),
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
            f.overflowing_round_ties_to_even(),
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
            f.overflowing_round_ties_to_even(),
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
            f.overflowing_round_ties_to_even(),
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
