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
// <https://opensource.org/licenses/MIT>.

macro_rules! fixed_const {
    (
        $Fixed:ident[$s_fixed:expr](
            $nbits:expr, $s_nbits:expr,
            $s_nbits_m1:expr, $s_nbits_m2:expr, $s_nbits_m3:expr, $s_nbits_m4:expr
        ),
        $nbits_cm3:expr, $nbits_cm2:expr, $nbits_cm1:expr,
        $nbits_c0:expr, $nbits_c1:expr, $nbits_c2:expr, $nbits_c3:expr,
        $Signedness:tt
    ) => {
        impl<const FRAC: i32> $Fixed<FRAC> {
            const fn from_const<const SRC_FRAC: i32>(src: FixedU128<SRC_FRAC>) -> $Fixed<FRAC> {
                let shift_right = SRC_FRAC.saturating_sub(FRAC);
                if shift_right < 0 {
                    panic!("overflow");
                }
                let bits128 = if shift_right >= 128 {
                    0
                } else {
                    src.to_bits() >> shift_right
                };
                $Fixed::from_bits(bits128 as _)
            }

            const fn one() -> $Fixed<FRAC> {
                const U128_ONE: FixedU128<127> = FixedU128::<127>::DELTA.unwrapped_shl(127);
                Self::from_const(U128_ONE)
            }

            if_signed! {
                $Signedness;
                const fn neg_one() -> $Fixed<FRAC> {
                    if FRAC >= $nbits {
                        panic!("overflow");
                    }
                    Self::from_bits(if FRAC <= 0 { -1 } else { -1 << FRAC })
                }
            }
        }

        comment! {
            "This block contains constants in the range 0.125&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;0.25.

These constants are not representable in ",
            if_signed_unsigned!($Signedness, "signed", "unsigned"),
            " fixed-point numbers with less than ",
            if_signed_unsigned!($Signedness, "&minus;1", "&minus;2"),
            " integer bits.

# Examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<", stringify!($nbits_cm2), ">;
assert_eq!(Fix::FRAC_1_TAU, Fix::from_num(consts::FRAC_1_TAU));
```

The following example fails to compile, since the maximum representable value
with ", stringify!($nbits_cm3), " fractional bits and ",
            if_signed_unsigned!($Signedness, "&minus;2", "&minus;3"),
            " integer bits is <&nbsp;0.125.

```rust,compile_fail
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<", stringify!($nbits_cm3), ">;
let _ = Fix::FRAC_1_TAU;
```
";
            impl<const FRAC: i32> $Fixed<FRAC>
            where
                If<{ FRAC <= $nbits_cm2 }>: True,
            {
                /// 1/τ = 0.159154…
                pub const FRAC_1_TAU: $Fixed<FRAC> = Self::from_const(consts::PREC_FRAC_1_TAU);
            }
        }

        comment! {
            "This block contains constants in the range 0.25&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;0.5.

These constants are not representable in ",
            if_signed_unsigned!($Signedness, "signed", "unsigned"),
            " fixed-point numbers with less than ",
            if_signed_unsigned!($Signedness, "0", "&minus;1"),
            " integer bits.

# Examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<", stringify!($nbits_cm1), ">;
assert_eq!(Fix::LOG10_2, Fix::from_num(consts::LOG10_2));
```

The following example fails to compile, since the maximum representable value
with ", stringify!($nbits_cm2), " fractional bits and ",
            if_signed_unsigned!($Signedness, "&minus;1", "&minus;2"),
            " integer bits is <&nbsp;0.25.

```rust,compile_fail
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<", stringify!($nbits_cm2), ">;
let _ = Fix::LOG10_2;
```
";
            impl<const FRAC: i32> $Fixed<FRAC>
            where
                If<{ FRAC <= $nbits_cm1 }>: True,
            {
                /// 2/τ = 0.318309…
                pub const FRAC_2_TAU: $Fixed<FRAC> = Self::from_const(consts::PREC_FRAC_2_TAU);

                /// π/8 = 0.392699…
                pub const FRAC_PI_8: $Fixed<FRAC> = Self::from_const(consts::PREC_FRAC_PI_8);

                /// 1/π = 0.318309…
                pub const FRAC_1_PI: $Fixed<FRAC> = Self::from_const(consts::PREC_FRAC_1_PI);

                /// log<sub>10</sub> 2 = 0.301029…
                pub const LOG10_2: $Fixed<FRAC> = Self::from_const(consts::PREC_LOG10_2);

                /// log<sub>10</sub> e = 0.434294…
                pub const LOG10_E: $Fixed<FRAC> = Self::from_const(consts::PREC_LOG10_E);
            }
        }

        comment! {
            "This block contains constants in the range 0.5&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;1",
            if_signed_else_empty_str!{ $Signedness; ", and &minus;1" },
            ".

These constants are not representable in ",
            if_signed_unsigned!($Signedness, "signed", "unsigned"),
            " fixed-point numbers with less than ",
            if_signed_unsigned!($Signedness, "1 integer bit", "0 integer bits"),
            ".

# Examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<", stringify!($nbits_c0), ">;
assert_eq!(Fix::LN_2, Fix::from_num(consts::LN_2));
assert!(0.5 <= Fix::LN_2  && Fix::LN_2 < 1);
```

The following example fails to compile, since the maximum representable value
with ", stringify!($nbits_cm1), " fractional bits and ",
            if_signed_unsigned!($Signedness, "0", "&minus;1"),
            " integer bits is <&nbsp;0.5.

```rust,compile_fail
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<", stringify!($nbits_cm1), ">;
let _ = Fix::LN_2;
```
";
            impl<const FRAC: i32> $Fixed<FRAC>
            where
                If<{ FRAC <= $nbits_c0 }>: True,
            {
                if_signed! {
                    $Signedness;
                    comment! {
                        "Negative one.

# Examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::", $s_fixed, ";
type Fix = ", $s_fixed, "<", $s_nbits_m1, ">;
assert_eq!(Fix::NEG_ONE, Fix::from_num(-1));
```

The following would fail as
<code>[", $s_fixed, "]&lt;", $s_nbits_m1, "></code>
cannot represent 1, so there is no
<code>[", $s_fixed, "]::&lt;", $s_nbits_m1, ">::[ONE]</code>.

[ONE]: ", $s_fixed, "::ONE

```rust,compile_fail
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::", $s_fixed, ";
const _ERROR: ", $s_fixed, "<", $s_nbits_m1, "> = ", $s_fixed, "::ONE.unwrapped_neg();
```
";
                        pub const NEG_ONE: $Fixed<FRAC> = Self::neg_one();
                    }
                }

                /// τ/8 = 0.785398…
                pub const FRAC_TAU_8: $Fixed<FRAC> = Self::from_const(consts::FRAC_TAU_8);

                /// τ/12 = 0.523598…
                pub const FRAC_TAU_12: $Fixed<FRAC> = Self::from_const(consts::FRAC_TAU_12);

                /// 4/τ = 0.636619…
                pub const FRAC_4_TAU: $Fixed<FRAC> = Self::from_const(consts::FRAC_4_TAU);

                /// π/4 = 0.785398…
                pub const FRAC_PI_4: $Fixed<FRAC> = Self::from_const(consts::FRAC_PI_4);

                /// π/6 = 0.523598…
                pub const FRAC_PI_6: $Fixed<FRAC> = Self::from_const(consts::FRAC_PI_6);

                /// 2/π = 0.636619…
                pub const FRAC_2_PI: $Fixed<FRAC> = Self::from_const(consts::FRAC_2_PI);

                /// 1/√π = 0.564189…
                pub const FRAC_1_SQRT_PI: $Fixed<FRAC> = Self::from_const(consts::FRAC_1_SQRT_PI);

                /// 1/√2 = 0.707106…
                pub const FRAC_1_SQRT_2: $Fixed<FRAC> = Self::from_const(consts::FRAC_1_SQRT_2);

                /// 1/√3 = 0.577350…
                pub const FRAC_1_SQRT_3: $Fixed<FRAC> = Self::from_const(consts::FRAC_1_SQRT_3);

                /// ln 2 = 0.693147…
                pub const LN_2: $Fixed<FRAC> = Self::from_const(consts::LN_2);

                /// The golden ratio conjugate, Φ = 1/φ = 0.618033…
                pub const FRAC_1_PHI: $Fixed<FRAC> = Self::from_const(consts::FRAC_1_PHI);

                /// The Euler-Mascheroni constant, γ = 0.577215…
                pub const GAMMA: $Fixed<FRAC> = Self::from_const(consts::GAMMA);

                /// Catalan’s constant = 0.915965…
                pub const CATALAN: $Fixed<FRAC> = Self::from_const(consts::CATALAN);
            }
        }

        comment! {
            "This block contains constants in the range 1&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;2.

These constants are not representable in ",
            if_signed_unsigned!($Signedness, "signed", "unsigned"),
            " fixed-point numbers with less than ",
            if_signed_unsigned!($Signedness, "2 integer bits", "1 integer bit"),
            ".

# Examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<", stringify!($nbits_c1), ">;
assert_eq!(Fix::LOG2_E, Fix::from_num(consts::LOG2_E));
assert!(1 <= Fix::LOG2_E && Fix::LOG2_E < 2);
```

The following example fails to compile, since the maximum representable value
with ", stringify!($nbits_c0), " fractional bits and ",
            if_signed_unsigned!($Signedness, "1 integer bit", "0 integer bits"),
            " is <&nbsp;1.

```rust,compile_fail
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<", stringify!($nbits_c0), ">;
let _ = Fix::LOG2_E;
```
";
            impl<const FRAC: i32> $Fixed<FRAC>
            where
                If<{ FRAC <= $nbits_c1 }>: True,
            {
                comment! {
                    "One.

# Examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::", $s_fixed, ";
type Fix = ", $s_fixed, "<4>;
assert_eq!(Fix::ONE, Fix::from_num(1));
```
";
                    pub const ONE: $Fixed<FRAC> = Self::one();
                }

                /// τ/4 = 1.57079…
                pub const FRAC_TAU_4: $Fixed<FRAC> = Self::from_const(consts::FRAC_TAU_4);

                /// τ/6 = 1.04719…
                pub const FRAC_TAU_6: $Fixed<FRAC> = Self::from_const(consts::FRAC_TAU_6);

                /// π/2 = 1.57079…
                pub const FRAC_PI_2: $Fixed<FRAC> = Self::from_const(consts::FRAC_PI_2);

                /// π/3 = 1.04719…
                pub const FRAC_PI_3: $Fixed<FRAC> = Self::from_const(consts::FRAC_PI_3);

                /// √π = 1.77245…
                pub const SQRT_PI: $Fixed<FRAC> = Self::from_const(consts::SQRT_PI);

                /// 2/√π = 1.12837…
                pub const FRAC_2_SQRT_PI: $Fixed<FRAC> = Self::from_const(consts::FRAC_2_SQRT_PI);

                /// √2 = 1.41421…
                pub const SQRT_2: $Fixed<FRAC> = Self::from_const(consts::SQRT_2);

                /// √3 = 1.73205…
                pub const SQRT_3: $Fixed<FRAC> = Self::from_const(consts::SQRT_3);

                /// √e = 1.64872…
                pub const SQRT_E: $Fixed<FRAC> = Self::from_const(consts::SQRT_E);

                /// log<sub>2</sub> e = 1.44269…
                pub const LOG2_E: $Fixed<FRAC> = Self::from_const(consts::LOG2_E);

                /// The golden ratio, φ = 1.61803…
                pub const PHI: $Fixed<FRAC> = Self::from_const(consts::PHI);

                /// √φ = 1.27201…
                pub const SQRT_PHI: $Fixed<FRAC> = Self::from_const(consts::SQRT_PHI);
            }
        }

        comment! {
            "This block contains constants in the range 2&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;4.

These constants are not representable in ",
            if_signed_unsigned!($Signedness, "signed", "unsigned"),
            " fixed-point numbers with less than ",
            if_signed_unsigned!($Signedness, "3", "2"),
            " integer bits.

# Examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<", stringify!($nbits_c2), ">;
assert_eq!(Fix::E, Fix::from_num(consts::E));
assert!(2 <= Fix::E && Fix::E < 4);
```

The following example fails to compile, since the maximum representable value
with ", stringify!($nbits_c1), " fractional bits and ",
            if_signed_unsigned!($Signedness, "2 integer bits", "1 integer bit"),
            " is <&nbsp;2.

```rust,compile_fail
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<", stringify!($nbits_c1), ">;
let _ = Fix::E;
```
";
            impl<const FRAC: i32> $Fixed<FRAC>
            where
                If<{ FRAC <= $nbits_c2 }>: True,
            {
                /// τ/2 = 3.14159…
                pub const FRAC_TAU_2: $Fixed<FRAC> = Self::from_const(consts::FRAC_TAU_2);

                /// τ/3 = 2.09439…
                pub const FRAC_TAU_3: $Fixed<FRAC> = Self::from_const(consts::FRAC_TAU_3);

                /// Archimedes’ constant, π = 3.14159…
                pub const PI: $Fixed<FRAC> = Self::from_const(consts::PI);

                /// Euler’s number, e = 2.71828…
                pub const E: $Fixed<FRAC> = Self::from_const(consts::E);

                /// log<sub>2</sub> 10 = 3.32192…
                pub const LOG2_10: $Fixed<FRAC> = Self::from_const(consts::LOG2_10);

                /// ln 10 = 2.30258…
                pub const LN_10: $Fixed<FRAC> = Self::from_const(consts::LN_10);
            }
        }

        comment! {
            "This block contains constants in the range 4&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;8.

These constants are not representable in ",
            if_signed_unsigned!($Signedness, "signed", "unsigned"),
            " fixed-point numbers with less than ",
            if_signed_unsigned!($Signedness, "4", "3"),
            " integer bits.

# Examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<", stringify!($nbits_c3), ">;
assert_eq!(Fix::TAU, Fix::from_num(consts::TAU));
assert!(4 <= Fix::TAU && Fix::TAU < 8);
```

The following example fails to compile, since the maximum representable value
with ", stringify!($nbits_c2), " fractional bits and ",
            if_signed_unsigned!($Signedness, "3", "2"),
            " integer bits is <&nbsp;4.

```rust,compile_fail
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<", stringify!($nbits_c2), ">;
let _ = Fix::TAU;
```
";
            impl<const FRAC: i32> $Fixed<FRAC>
            where
                If<{ FRAC <= $nbits_c3 }>: True,
            {
                /// A turn, τ = 6.28318…
                pub const TAU: $Fixed<FRAC> = Self::from_const(consts::TAU);
            }
        }
    };
}
