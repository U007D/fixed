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

macro_rules! shift {
    // in case of 128, split shift in two parts to avoid >> 128
    ($SRC:ident, $Fixed:ident<$FRAC:ident>) => {
        $Fixed::<$FRAC>::from_bits(
            (consts::$SRC.to_bits() >> (64 - $FRAC / 2) >> (64 + $FRAC / 2 - $FRAC)) as _,
        )
    };
    ($SRC:ident, $src_frac_nbits:literal, $Fixed:ident<$FRAC:ident>) => {
        $Fixed::<$FRAC>::from_bits((consts::$SRC.to_bits() >> ($src_frac_nbits - $FRAC)) as _)
    };
}

macro_rules! fixed_const {
    (
        $Fixed:ident[$s_fixed:expr](
            $nbits:expr, $s_nbits:expr,
            $s_nbits_m1:expr, $s_nbits_m2:expr, $s_nbits_m3:expr, $s_nbits_m4:expr
        ),
        $nbits_c0:expr, $nbits_c1:expr, $nbits_c2:expr, $nbits_c3:expr,
        $Signedness:tt
    ) => {
        comment! {
            "This block contains constants in the range 0&nbsp;<&nbsp;<i>x</i>&nbsp;<&nbsp;0.5.

# Examples

```rust
use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<", $s_nbits, ">;
assert_eq!(Fix::LOG10_2, Fix::from_num(consts::LOG10_2));
```
";
            impl<const FRAC: i32> $Fixed<FRAC>
            where
                If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True,
            {
                /// 1/τ = 0.159154…
                pub const FRAC_1_TAU: $Fixed<FRAC> = shift!(FRAC_1_TAU, $Fixed<FRAC>);

                /// 2/τ = 0.318309…
                pub const FRAC_2_TAU: $Fixed<FRAC> = shift!(FRAC_2_TAU, $Fixed<FRAC>);

                /// π/8 = 0.392699…
                pub const FRAC_PI_8: $Fixed<FRAC> = shift!(FRAC_PI_8, $Fixed<FRAC>);

                /// 1/π = 0.318309…
                pub const FRAC_1_PI: $Fixed<FRAC> = shift!(FRAC_1_PI, $Fixed<FRAC>);

                /// log<sub>10</sub> 2 = 0.301029…
                pub const LOG10_2: $Fixed<FRAC> = shift!(LOG10_2, $Fixed<FRAC>);

                /// log<sub>10</sub> e = 0.434294…
                pub const LOG10_E: $Fixed<FRAC> = shift!(LOG10_E, $Fixed<FRAC>);
            }
        }

        comment! {
            "This block contains constants in the range 0.5&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;1.

",
            if_signed_else_empty_str! {
                $Signedness;
                "These constants are not representable in signed
fixed-point numbers with less than 1 integer bit.

"
            },
            "# Examples

```rust
use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<",
            if_signed_unsigned!($Signedness, $s_nbits_m1, $s_nbits),
            ">;
assert_eq!(Fix::LN_2, Fix::from_num(consts::LN_2));
assert!(0.5 <= Fix::LN_2  && Fix::LN_2 < 1);
```
",
            if_signed_else_empty_str! {
                $Signedness;
                "
The following example fails to compile, since the maximum
representable value with ", $s_nbits, " fractional bits and 0 integer
bits is <&nbsp;0.5.

```rust,compile_fail
use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<", $s_nbits, ">;
let _ = Fix::LN_2;
```
"
            };
            impl<const FRAC: i32> $Fixed<FRAC>
            where
                If<{ (0 <= FRAC) & (FRAC <= $nbits_c0) }>: True,
            {
                /// τ/8 = 0.785398…
                pub const FRAC_TAU_8: $Fixed<FRAC> = shift!(FRAC_TAU_8, $Fixed<FRAC>);

                /// τ/12 = 0.523598…
                pub const FRAC_TAU_12: $Fixed<FRAC> = shift!(FRAC_TAU_12, $Fixed<FRAC>);

                /// 4/τ = 0.636619…
                pub const FRAC_4_TAU: $Fixed<FRAC> = shift!(FRAC_4_TAU, $Fixed<FRAC>);

                /// π/4 = 0.785398…
                pub const FRAC_PI_4: $Fixed<FRAC> = shift!(FRAC_PI_4, $Fixed<FRAC>);

                /// π/6 = 0.523598…
                pub const FRAC_PI_6: $Fixed<FRAC> = shift!(FRAC_PI_6, $Fixed<FRAC>);

                /// 2/π = 0.636619…
                pub const FRAC_2_PI: $Fixed<FRAC> = shift!(FRAC_2_PI, $Fixed<FRAC>);

                /// 1/√π = 0.564189…
                pub const FRAC_1_SQRT_PI: $Fixed<FRAC> = shift!(FRAC_1_SQRT_PI, $Fixed<FRAC>);

                /// 1/√2 = 0.707106…
                pub const FRAC_1_SQRT_2: $Fixed<FRAC> = shift!(FRAC_1_SQRT_2, $Fixed<FRAC>);

                /// 1/√3 = 0.577350…
                pub const FRAC_1_SQRT_3: $Fixed<FRAC> = shift!(FRAC_1_SQRT_3, $Fixed<FRAC>);

                /// ln 2 = 0.693147…
                pub const LN_2: $Fixed<FRAC> = shift!(LN_2, $Fixed<FRAC>);

                /// The golden ratio conjugate, Φ = 1/φ = 0.618033…
                pub const FRAC_1_PHI: $Fixed<FRAC> = shift!(FRAC_1_PHI, $Fixed<FRAC>);

                /// The Euler-Mascheroni constant, γ = 0.577215…
                pub const GAMMA: $Fixed<FRAC> = shift!(GAMMA, $Fixed<FRAC>);

                /// Catalan’s constant = 0.915965…
                pub const CATALAN: $Fixed<FRAC> = shift!(CATALAN, $Fixed<FRAC>);
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
use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<",
            if_signed_unsigned!($Signedness, $s_nbits_m2, $s_nbits_m1),
            ">;
assert_eq!(Fix::LOG2_E, Fix::from_num(consts::LOG2_E));
assert!(1 <= Fix::LOG2_E && Fix::LOG2_E < 2);
```

The following example fails to compile, since the maximum
representable value with ",
            if_signed_unsigned!($Signedness, $s_nbits_m1, $s_nbits),
            " fractional bits and ",
            if_signed_unsigned!($Signedness, "1 integer bit", "0 integer bits"),
            " is <&nbsp;1.

```rust,compile_fail
use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<",
            if_signed_unsigned!($Signedness, $s_nbits_m1, $s_nbits),
            ">;
let _ = Fix::LOG2_E;
```
";
            impl<const FRAC: i32> $Fixed<FRAC>
            where
                If<{ (0 <= FRAC) & (FRAC <= $nbits_c1) }>: True,
            {
                comment! {
                    "One.

# Examples

```rust
use fixed::", $s_fixed, ";
type Fix = ", $s_fixed, "<4>;
assert_eq!(Fix::ONE, Fix::from_num(1));
```
";
                    pub const ONE: $Fixed<FRAC> =
                        $Fixed::from_bits($Fixed::<FRAC>::DELTA.to_bits() << FRAC);
                }

                /// τ/4 = 1.57079…
                pub const FRAC_TAU_4: $Fixed<FRAC> = shift!(FRAC_TAU_4, 127, $Fixed<FRAC>);

                /// τ/6 = 1.04719…
                pub const FRAC_TAU_6: $Fixed<FRAC> = shift!(FRAC_TAU_6, 127, $Fixed<FRAC>);

                /// π/2 = 1.57079…
                pub const FRAC_PI_2: $Fixed<FRAC> = shift!(FRAC_PI_2, 127, $Fixed<FRAC>);

                /// π/3 = 1.04719…
                pub const FRAC_PI_3: $Fixed<FRAC> = shift!(FRAC_PI_3, 127, $Fixed<FRAC>);

                /// √π = 1.77245…
                pub const SQRT_PI: $Fixed<FRAC> = shift!(SQRT_PI, 127, $Fixed<FRAC>);

                /// 2/√π = 1.12837…
                pub const FRAC_2_SQRT_PI: $Fixed<FRAC> = shift!(FRAC_2_SQRT_PI, 127, $Fixed<FRAC>);

                /// √2 = 1.41421…
                pub const SQRT_2: $Fixed<FRAC> = shift!(SQRT_2, 127, $Fixed<FRAC>);

                /// √3 = 1.73205…
                pub const SQRT_3: $Fixed<FRAC> = shift!(SQRT_3, 127, $Fixed<FRAC>);

                /// √e = 1.64872…
                pub const SQRT_E: $Fixed<FRAC> = shift!(SQRT_E, 127, $Fixed<FRAC>);

                /// log<sub>2</sub> e = 1.44269…
                pub const LOG2_E: $Fixed<FRAC> = shift!(LOG2_E, 127, $Fixed<FRAC>);

                /// The golden ratio, φ = 1.61803…
                pub const PHI: $Fixed<FRAC> = shift!(PHI, 127, $Fixed<FRAC>);

                /// √φ = 1.27201…
                pub const SQRT_PHI: $Fixed<FRAC> = shift!(SQRT_PHI, 127, $Fixed<FRAC>);
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
use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<",
            if_signed_unsigned!($Signedness, $s_nbits_m3, $s_nbits_m2),
            ">;
assert_eq!(Fix::E, Fix::from_num(consts::E));
assert!(2 <= Fix::E && Fix::E < 4);
```

The following example fails to compile, since the maximum
representable value with ",
            if_signed_unsigned!($Signedness, $s_nbits_m2, $s_nbits_m1),
            " fractional bits and ",
            if_signed_unsigned!($Signedness, "2 integer bits", "1 integer bit"),
            " is <&nbsp;2.

```rust,compile_fail
use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<",
            if_signed_unsigned!($Signedness, $s_nbits_m2, $s_nbits_m1),
            ">;
let _ = Fix::E;
```
";
            impl<const FRAC: i32> $Fixed<FRAC>
            where
                If<{ (0 <= FRAC) & (FRAC <= $nbits_c2) }>: True,
            {
                /// τ/2 = 3.14159…
                pub const FRAC_TAU_2: $Fixed<FRAC> = shift!(FRAC_TAU_2, 126, $Fixed<FRAC>);

                /// τ/3 = 2.09439…
                pub const FRAC_TAU_3: $Fixed<FRAC> = shift!(FRAC_TAU_3, 126, $Fixed<FRAC>);

                /// Archimedes’ constant, π = 3.14159…
                pub const PI: $Fixed<FRAC> = shift!(PI, 126, $Fixed<FRAC>);

                /// Euler’s number, e = 2.71828…
                pub const E: $Fixed<FRAC> = shift!(E, 126, $Fixed<FRAC>);

                /// log<sub>2</sub> 10 = 3.32192…
                pub const LOG2_10: $Fixed<FRAC> = shift!(LOG2_10, 126, $Fixed<FRAC>);

                /// ln 10 = 2.30258…
                pub const LN_10: $Fixed<FRAC> = shift!(LN_10, 126, $Fixed<FRAC>);
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
use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<",
            if_signed_unsigned!($Signedness, $s_nbits_m4, $s_nbits_m3),
            ">;
assert_eq!(Fix::TAU, Fix::from_num(consts::TAU));
assert!(4 <= Fix::TAU && Fix::TAU < 8);
```

The following example fails to compile, since the maximum
representable value with ",
            if_signed_unsigned!($Signedness, $s_nbits_m3, $s_nbits_m2),
            " fractional bits and ",
            if_signed_unsigned!($Signedness, "3", "2"),
            " integer bits is <&nbsp;4.

```rust,compile_fail
use fixed::{consts, ", $s_fixed, "};
type Fix = ", $s_fixed, "<",
            if_signed_unsigned!($Signedness, $s_nbits_m3, $s_nbits_m2),
            ">;
let _ = Fix::TAU;
```
";
            impl<const FRAC: i32> $Fixed<FRAC>
            where
                If<{ (0 <= FRAC) & (FRAC <= $nbits_c3) }>: True,
            {
                /// A turn, τ = 6.28318…
                pub const TAU: $Fixed<FRAC> = shift!(TAU, 125, $Fixed<FRAC>);
            }
        }
    };
}
