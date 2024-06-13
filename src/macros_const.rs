// Copyright © 2018–2024 Trevor Spiteri

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
        Self = $Self:ident,
        Signedness = $Signedness:ident,
        [nm4 ..= n] = [$nm4:literal, $nm3:literal, $nm2:literal, $nm1:literal, $n:literal],
        [ncm3 ..= nc3] = [
            $ncm3:literal, $ncm2:literal, $ncm1:literal,
            $nc0:literal, $nc1:literal, $nc2:literal, $nc3:literal
        ],
    ) => {
        impl<const FRAC: i32> $Self<FRAC> {
            const fn from_const<const SRC_FRAC: i32>(src: FixedU128<SRC_FRAC>) -> $Self<FRAC> {
                let shift_right = SRC_FRAC.saturating_sub(FRAC);
                if shift_right < if_signed_unsigned!($Signedness, 129, 128) - $n {
                    panic!("overflow");
                }
                let bits128 = if shift_right >= 128 {
                    0
                } else {
                    src.to_bits() >> shift_right
                };
                $Self::from_bits(bits128 as _)
            }

            const fn one() -> $Self<FRAC> {
                if FRAC >= $n - if_signed_unsigned!($Signedness, 1, 0) {
                    panic!("overflow");
                }
                $Self::from_bits(if FRAC < 0 { 0 } else { 1 << FRAC })
            }

            if_signed! {
                $Signedness;
                const fn neg_one() -> $Self<FRAC> {
                    if FRAC >= $n {
                        panic!("overflow");
                    }
                    $Self::from_bits(if FRAC < 0 { -1 } else { -1 << FRAC })
                }
            }
        }

        comment! {
            "This block contains constants in the range 0.125&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;0.25,
which are implemented for `FRAC`&nbsp;≤&nbsp;", stringify!($ncm2), ".

These constants are not representable in ",
            if_signed_unsigned!($Signedness, "signed", "unsigned"),
            " fixed-point numbers with less than ",
            if_signed_unsigned!($Signedness, "&minus;1", "&minus;2"),
            " [integer bits].

# Examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", stringify!($Self), "};
type Fix = ", stringify!($Self), "<", stringify!($ncm2), ">;
assert_eq!(Fix::FRAC_1_TAU, Fix::from_num(consts::FRAC_1_TAU));
```

If `FRAC` is very small, the constants can be rounded down to insignificance.

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::", stringify!($Self), ";
type Fix = ", stringify!($Self), "<-", $n, ">;
assert_eq!(Fix::FRAC_1_TAU, Fix::ZERO);
```

The following example fails to compile, since the maximum representable value
with ", stringify!($ncm3), " [fractional bits] and ",
            if_signed_unsigned!($Signedness, "&minus;2", "&minus;3"),
            " [integer bits] is <&nbsp;0.125.

```rust,compile_fail
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", stringify!($Self), "};
type Fix = ", stringify!($Self), "<", stringify!($ncm3), ">;
let _ = Fix::FRAC_1_TAU;
```

[fractional bits]: Self::FRAC_BITS
[integer bits]: Self::INT_BITS
";
            impl<const FRAC: i32> $Self<FRAC>
            where
                If<{ FRAC <= $ncm2 }>: True,
            {
                /// 1/τ = 0.159154…
                pub const FRAC_1_TAU: $Self<FRAC> = Self::from_const(consts::PREC_FRAC_1_TAU);
            }
        }

        comment! {
            "This block contains constants in the range 0.25&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;0.5,
which are implemented for `FRAC`&nbsp;≤&nbsp;", stringify!($ncm1), ".

These constants are not representable in ",
            if_signed_unsigned!($Signedness, "signed", "unsigned"),
            " fixed-point numbers with less than ",
            if_signed_unsigned!($Signedness, "0", "&minus;1"),
            " [integer bits].

# Examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", stringify!($Self), "};
type Fix = ", stringify!($Self), "<", stringify!($ncm1), ">;
assert_eq!(Fix::LOG10_2, Fix::from_num(consts::LOG10_2));
```

If `FRAC` is very small, the constants can be rounded down to insignificance.

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::", stringify!($Self), ";
type Fix = ", stringify!($Self), "<-", $n, ">;
assert_eq!(Fix::LOG10_2, Fix::ZERO);
```

The following example fails to compile, since the maximum representable value
with ", stringify!($ncm2), " [fractional bits] and ",
            if_signed_unsigned!($Signedness, "&minus;1", "&minus;2"),
            " [integer bits] is <&nbsp;0.25.

```rust,compile_fail
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", stringify!($Self), "};
type Fix = ", stringify!($Self), "<", stringify!($ncm2), ">;
let _ = Fix::LOG10_2;
```

[fractional bits]: Self::FRAC_BITS
[integer bits]: Self::INT_BITS
";
            impl<const FRAC: i32> $Self<FRAC>
            where
                If<{ FRAC <= $ncm1 }>: True,
            {
                /// 2/τ = 0.318309…
                pub const FRAC_2_TAU: $Self<FRAC> = Self::from_const(consts::PREC_FRAC_2_TAU);

                /// π/8 = 0.392699…
                pub const FRAC_PI_8: $Self<FRAC> = Self::from_const(consts::PREC_FRAC_PI_8);

                /// 1/π = 0.318309…
                pub const FRAC_1_PI: $Self<FRAC> = Self::from_const(consts::PREC_FRAC_1_PI);

                /// 1/√2π = 0.398942…
                pub const FRAC_1_SQRT_2PI: $Self<FRAC> =
                    Self::from_const(consts::PREC_FRAC_1_SQRT_2PI);

                /// log<sub>10</sub> 2 = 0.301029…
                pub const LOG10_2: $Self<FRAC> = Self::from_const(consts::PREC_LOG10_2);

                /// log<sub>10</sub> e = 0.434294…
                pub const LOG10_E: $Self<FRAC> = Self::from_const(consts::PREC_LOG10_E);
            }
        }

        comment! {
            "This block contains constants in the range 0.5&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;1",
            if_signed_else_empty_str!{ $Signedness; ", and &minus;1" },
            ", which are implemented for `FRAC`&nbsp;≤&nbsp;", stringify!($nc0), ".

These constants are not representable in ",
            if_signed_unsigned!($Signedness, "signed", "unsigned"),
            " fixed-point numbers with less than ",
            if_signed_unsigned!($Signedness, "1 [integer bit]", "0 [integer bits]"),
            ".

# Examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", stringify!($Self), "};
type Fix = ", stringify!($Self), "<", stringify!($nc0), ">;
assert_eq!(Fix::LN_2, Fix::from_num(consts::LN_2));
assert!(0.5 <= Fix::LN_2  && Fix::LN_2 < 1);
```

If `FRAC` is very small, the constants can be rounded down to insignificance.

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::", stringify!($Self), ";
type Fix = ", stringify!($Self), "<-", $n, ">;
",
            if_signed_else_empty_str! {
                $Signedness;
                "assert_eq!(Fix::NEG_ONE, -Fix::DELTA);
",
            },
            "assert_eq!(Fix::LN_2, Fix::ZERO);
```

The following example fails to compile, since the maximum representable value
with ", stringify!($ncm1), " [fractional bits] and ",
            if_signed_unsigned!($Signedness, "0", "&minus;1"),
            " [integer bits] is <&nbsp;0.5.

```rust,compile_fail
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", stringify!($Self), "};
type Fix = ", stringify!($Self), "<", stringify!($ncm1), ">;
let _ = Fix::LN_2;
```

[fractional bits]: Self::FRAC_BITS
[integer bit]: Self::INT_BITS
[integer bits]: Self::INT_BITS
";
            impl<const FRAC: i32> $Self<FRAC>
            where
                If<{ FRAC <= $nc0 }>: True,
            {
                if_signed! {
                    $Signedness;
                    comment! {
                        "Negative one.

If `FRAC`&nbsp;<&nbsp;0 and [`DELTA`]&nbsp;>&nbsp;1, `NEG_ONE` will be rounded down to
<code>-[DELTA][`DELTA`]</code>.

# Examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::", stringify!($Self), ";
type Fix = ", stringify!($Self), "<", $nm1, ">;
assert_eq!(Fix::NEG_ONE, Fix::from_num(-1));

type Imprecise = ", stringify!($Self), "<-1>;
assert!(Imprecise::DELTA > 1);
assert_eq!(Imprecise::NEG_ONE, -Imprecise::DELTA);
```

The following would fail as
<code>[", stringify!($Self), "]&lt;", $nm1, "></code>
cannot represent 1, so there is no
<code>[", stringify!($Self), "]::&lt;", $nm1, ">::[ONE]</code>.

```rust,compile_fail
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::", stringify!($Self), ";
const _ERROR: ", stringify!($Self), "<", $nm1, "> = ", stringify!($Self), "::ONE.unwrapped_neg();
```

[ONE]: ", stringify!($Self), "::ONE
[`DELTA`]: ", stringify!($Self), "::DELTA
";
                        pub const NEG_ONE: $Self<FRAC> = Self::neg_one();
                    }
                }

                /// τ/8 = 0.785398…
                pub const FRAC_TAU_8: $Self<FRAC> = Self::from_const(consts::FRAC_TAU_8);

                /// τ/12 = 0.523598…
                pub const FRAC_TAU_12: $Self<FRAC> = Self::from_const(consts::FRAC_TAU_12);

                /// 4/τ = 0.636619…
                pub const FRAC_4_TAU: $Self<FRAC> = Self::from_const(consts::FRAC_4_TAU);

                /// π/4 = 0.785398…
                pub const FRAC_PI_4: $Self<FRAC> = Self::from_const(consts::FRAC_PI_4);

                /// π/6 = 0.523598…
                pub const FRAC_PI_6: $Self<FRAC> = Self::from_const(consts::FRAC_PI_6);

                /// 2/π = 0.636619…
                pub const FRAC_2_PI: $Self<FRAC> = Self::from_const(consts::FRAC_2_PI);

                /// 1/√π = 0.564189…
                pub const FRAC_1_SQRT_PI: $Self<FRAC> = Self::from_const(consts::FRAC_1_SQRT_PI);

                /// 1/√2 = 0.707106…
                pub const FRAC_1_SQRT_2: $Self<FRAC> = Self::from_const(consts::FRAC_1_SQRT_2);

                /// 1/√3 = 0.577350…
                pub const FRAC_1_SQRT_3: $Self<FRAC> = Self::from_const(consts::FRAC_1_SQRT_3);

                /// ln 2 = 0.693147…
                pub const LN_2: $Self<FRAC> = Self::from_const(consts::LN_2);

                /// The golden ratio conjugate, Φ = 1/φ = 0.618033…
                pub const FRAC_1_PHI: $Self<FRAC> = Self::from_const(consts::FRAC_1_PHI);

                /// The Euler-Mascheroni constant, γ = 0.577215…
                pub const GAMMA: $Self<FRAC> = Self::from_const(consts::GAMMA);

                /// Catalan’s constant = 0.915965…
                pub const CATALAN: $Self<FRAC> = Self::from_const(consts::CATALAN);
            }
        }

        comment! {
            "This block contains constants in the range 1&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;2,
which are implemented for `FRAC`&nbsp;≤&nbsp;", stringify!($nc1), ".

These constants are not representable in ",
            if_signed_unsigned!($Signedness, "signed", "unsigned"),
            " fixed-point numbers with less than ",
            if_signed_unsigned!($Signedness, "2 [integer bits]", "1 [integer bit]"),
            ".

# Examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", stringify!($Self), "};
type Fix = ", stringify!($Self), "<", stringify!($nc1), ">;
assert_eq!(Fix::LOG2_E, Fix::from_num(consts::LOG2_E));
assert!(1 <= Fix::LOG2_E && Fix::LOG2_E < 2);
```

If `FRAC` is very small, the constants can be rounded down to insignificance.

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::", stringify!($Self), ";
type Fix = ", stringify!($Self), "<-", $n, ">;
assert_eq!(Fix::ONE, Fix::ZERO);
assert_eq!(Fix::LOG2_E, Fix::ZERO);
```

The following example fails to compile, since the maximum representable value
with ", stringify!($nc0), " [fractional bits] and ",
            if_signed_unsigned!($Signedness, "1 [integer bit]", "0 [integer bits]"),
            " is <&nbsp;1.

```rust,compile_fail
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", stringify!($Self), "};
type Fix = ", stringify!($Self), "<", stringify!($nc0), ">;
let _ = Fix::LOG2_E;
```

[fractional bits]: Self::FRAC_BITS
[integer bit]: Self::INT_BITS
[integer bits]: Self::INT_BITS
";
            impl<const FRAC: i32> $Self<FRAC>
            where
                If<{ FRAC <= $nc1 }>: True,
            {
                comment! {
                    "One.

If `FRAC`&nbsp;<&nbsp;0 and [`DELTA`]&nbsp;>&nbsp;1, `ONE` will be rounded down
to [`ZERO`].

# Examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::", stringify!($Self), ";
type Fix = ", stringify!($Self), "<4>;
assert_eq!(Fix::ONE, Fix::from_num(1));

type Imprecise = ", stringify!($Self), "<-1>;
assert!(Imprecise::DELTA > 1);
assert_eq!(Imprecise::ONE, Imprecise::ZERO);
```

[`DELTA`]: ", stringify!($Self), "::DELTA
[`ZERO`]: ", stringify!($Self), "::ZERO
";
                    pub const ONE: $Self<FRAC> = Self::one();
                }

                /// τ/4 = 1.57079…
                pub const FRAC_TAU_4: $Self<FRAC> = Self::from_const(consts::FRAC_TAU_4);

                /// τ/6 = 1.04719…
                pub const FRAC_TAU_6: $Self<FRAC> = Self::from_const(consts::FRAC_TAU_6);

                /// π/2 = 1.57079…
                pub const FRAC_PI_2: $Self<FRAC> = Self::from_const(consts::FRAC_PI_2);

                /// π/3 = 1.04719…
                pub const FRAC_PI_3: $Self<FRAC> = Self::from_const(consts::FRAC_PI_3);

                /// √π = 1.77245…
                pub const SQRT_PI: $Self<FRAC> = Self::from_const(consts::SQRT_PI);

                /// 2/√π = 1.12837…
                pub const FRAC_2_SQRT_PI: $Self<FRAC> = Self::from_const(consts::FRAC_2_SQRT_PI);

                /// √2 = 1.41421…
                pub const SQRT_2: $Self<FRAC> = Self::from_const(consts::SQRT_2);

                /// √3 = 1.73205…
                pub const SQRT_3: $Self<FRAC> = Self::from_const(consts::SQRT_3);

                /// √e = 1.64872…
                pub const SQRT_E: $Self<FRAC> = Self::from_const(consts::SQRT_E);

                /// log<sub>2</sub> e = 1.44269…
                pub const LOG2_E: $Self<FRAC> = Self::from_const(consts::LOG2_E);

                /// The golden ratio, φ = 1.61803…
                pub const PHI: $Self<FRAC> = Self::from_const(consts::PHI);

                /// √φ = 1.27201…
                pub const SQRT_PHI: $Self<FRAC> = Self::from_const(consts::SQRT_PHI);
            }
        }

        comment! {
            "This block contains constants in the range 2&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;4,
which are implemented for `FRAC`&nbsp;≤&nbsp;", stringify!($nc2), ".

These constants are not representable in ",
            if_signed_unsigned!($Signedness, "signed", "unsigned"),
            " fixed-point numbers with less than ",
            if_signed_unsigned!($Signedness, "3", "2"),
            " [integer bits].

# Examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", stringify!($Self), "};
type Fix = ", stringify!($Self), "<", stringify!($nc2), ">;
assert_eq!(Fix::E, Fix::from_num(consts::E));
assert!(2 <= Fix::E && Fix::E < 4);
```

If `FRAC` is very small, the constants can be rounded down to insignificance.

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::", stringify!($Self), ";
type Fix = ", stringify!($Self), "<-", $n, ">;
assert_eq!(Fix::E, Fix::ZERO);
```

The following example fails to compile, since the maximum representable value
with ", stringify!($nc1), " [fractional bits] and ",
            if_signed_unsigned!($Signedness, "2 [integer bits]", "1 [integer bit]"),
            " is <&nbsp;2.

```rust,compile_fail
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", stringify!($Self), "};
type Fix = ", stringify!($Self), "<", stringify!($nc1), ">;
let _ = Fix::E;
```

[fractional bits]: Self::FRAC_BITS
[integer bit]: Self::INT_BITS
[integer bits]: Self::INT_BITS
";
            impl<const FRAC: i32> $Self<FRAC>
            where
                If<{ FRAC <= $nc2 }>: True,
            {
                /// τ/2 = 3.14159…
                pub const FRAC_TAU_2: $Self<FRAC> = Self::from_const(consts::FRAC_TAU_2);

                /// τ/3 = 2.09439…
                pub const FRAC_TAU_3: $Self<FRAC> = Self::from_const(consts::FRAC_TAU_3);

                /// Archimedes’ constant, π = 3.14159…
                pub const PI: $Self<FRAC> = Self::from_const(consts::PI);

                /// √2π = 2.50662…
                pub const SQRT_2PI: $Self<FRAC> = Self::from_const(consts::SQRT_2PI);

                /// Euler’s number, e = 2.71828…
                pub const E: $Self<FRAC> = Self::from_const(consts::E);

                /// log<sub>2</sub> 10 = 3.32192…
                pub const LOG2_10: $Self<FRAC> = Self::from_const(consts::LOG2_10);

                /// ln 10 = 2.30258…
                pub const LN_10: $Self<FRAC> = Self::from_const(consts::LN_10);
            }
        }

        comment! {
            "This block contains constants in the range 4&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;8,
which are implemented for `FRAC`&nbsp;≤&nbsp;", stringify!($nc3), ".

These constants are not representable in ",
            if_signed_unsigned!($Signedness, "signed", "unsigned"),
            " fixed-point numbers with less than ",
            if_signed_unsigned!($Signedness, "4", "3"),
            " [integer bits].

# Examples

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", stringify!($Self), "};
type Fix = ", stringify!($Self), "<", stringify!($nc3), ">;
assert_eq!(Fix::TAU, Fix::from_num(consts::TAU));
assert!(4 <= Fix::TAU && Fix::TAU < 8);
```

If `FRAC` is very small, the constants can be rounded down to insignificance.

```rust
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::", stringify!($Self), ";
type Fix = ", stringify!($Self), "<-", $n, ">;
assert_eq!(Fix::TAU, Fix::ZERO);
```

The following example fails to compile, since the maximum representable value
with ", stringify!($nc2), " [fractional bits] and ",
            if_signed_unsigned!($Signedness, "3", "2"),
            " [integer bits] is <&nbsp;4.

```rust,compile_fail
#![feature(generic_const_exprs)]
# #![allow(incomplete_features)]

use fixed::{consts, ", stringify!($Self), "};
type Fix = ", stringify!($Self), "<", stringify!($nc2), ">;
let _ = Fix::TAU;
```

[fractional bits]: Self::FRAC_BITS
[integer bits]: Self::INT_BITS
";
            impl<const FRAC: i32> $Self<FRAC>
            where
                If<{ FRAC <= $nc3 }>: True,
            {
                /// A turn, τ = 6.28318…
                pub const TAU: $Self<FRAC> = Self::from_const(consts::TAU);
            }
        }
    };
}
