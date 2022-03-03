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

use core::{cmp::Ordering, num::FpCategory};

/// The bit representation of a *binary128* floating-point number (`f128`).
///
/// This type can be used to
///
///   * convert between fixed-point numbers and the bit representation of
///     128-bit floating-point numbers.
///   * compare fixed-point numbers and the bit representation of 128-bit
///     floating-point numbers.
///
/// # Examples
///
/// ```rust
/// #![feature(generic_const_exprs)]
/// # #![allow(incomplete_features)]
///
/// use fixed::{types::I16F16, F128Bits};
/// assert_eq!(I16F16::ONE.to_num::<F128Bits>(), F128Bits::ONE);
/// assert_eq!(I16F16::from_num(F128Bits::ONE), I16F16::ONE);
///
/// // fixed-point numbers can be compared directly to F128Bits values
/// assert!(I16F16::from_num(1.5) > F128Bits::ONE);
/// assert!(I16F16::from_num(0.5) < F128Bits::ONE);
/// ```
#[repr(transparent)]
#[derive(Clone, Copy, Default, Hash, Debug)]
pub struct F128Bits {
    pub(crate) bits: u128,
}

impl F128Bits {
    /// Zero.
    pub const ZERO: F128Bits = F128Bits::from_bits(0);
    /// Negative zero (&minus;0).
    pub const NEG_ZERO: F128Bits = F128Bits::from_bits(1u128 << 127);
    /// One.
    pub const ONE: F128Bits = F128Bits::from_bits(0x3FFF_u128 << 112);
    /// Negative one (&minus;1).
    pub const NEG_ONE: F128Bits = F128Bits::from_bits(0xBFFF_u128 << 112);
    /// Smallest positive subnormal number.
    pub const MIN_POSITIVE_SUB: F128Bits = F128Bits::from_bits(1u128);
    /// Smallest positive normal number.
    pub const MIN_POSITIVE: F128Bits = F128Bits::from_bits(1u128 << 112);
    /// Largest finite number.
    pub const MAX: F128Bits = F128Bits::from_bits((0x7FFF_u128 << 112) - 1);
    /// Smallest finite number; equal to &minus;[`MAX`][Self::MAX].
    pub const MIN: F128Bits = F128Bits::from_bits((0xFFFF_u128 << 112) - 1);
    /// Infinity (∞).
    pub const INFINITY: F128Bits = F128Bits::from_bits(0x7FFF_u128 << 112);
    /// Negative infinity (&minus;∞).
    pub const NEG_INFINITY: F128Bits = F128Bits::from_bits(0xFFFF_u128 << 112);
    /// NaN.
    pub const NAN: F128Bits = F128Bits::from_bits(0x7FFF_8000_u128 << 96);

    /// The radix or base of the internal representation.
    pub const RADIX: u32 = 2;
    /// Number of significant digits in base 2.
    pub const MANTISSA_DIGITS: u32 = 113;

    /// The difference between 1 and the next larger representable number.
    pub const EPSILON: F128Bits = F128Bits::from_bits((0x3FFF_u128 - 112) << 112);
    /// If <i>x</i>&nbsp;=&nbsp;`MIN_EXP`, then normal numbers
    /// ≥&nbsp;0.5&nbsp;×&nbsp;2<sup><i>x</i></sup>.
    pub const MIN_EXP: i32 = -16381;
    /// If <i>x</i>&nbsp;=&nbsp;`MAX_EXP`, then normal numbers
    /// <&nbsp;1&nbsp;×&nbsp;2<sup><i>x</i></sup>.
    pub const MAX_EXP: i32 = 16383;

    /// Raw transmutation to [`u128`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::F128Bits;
    /// assert_eq!(F128Bits::ONE.to_bits(), 0x3FFF_u128 << 112);
    /// assert_ne!(F128Bits::ONE.to_bits(), 1u128);
    /// ```
    #[inline]
    pub const fn to_bits(self) -> u128 {
        self.bits
    }

    /// Raw transmutation from [`u128`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::F128Bits;
    /// let infinity_bits = 0x7FFF_u128 << 112;
    /// assert!(F128Bits::from_bits(infinity_bits - 1).is_finite());
    /// assert!(!F128Bits::from_bits(infinity_bits).is_finite());
    /// ```
    #[inline]
    pub const fn from_bits(bits: u128) -> F128Bits {
        F128Bits { bits }
    }

    /// Returns [`true`] if the number is NaN.
    ///
    /// # Example
    ///
    /// ```rust
    /// use fixed::F128Bits;
    ///
    /// assert!(F128Bits::NAN.is_nan());
    ///
    /// assert!(!F128Bits::ONE.is_nan());
    /// assert!(!F128Bits::INFINITY.is_nan());
    /// assert!(!F128Bits::NEG_INFINITY.is_nan());
    /// ```
    #[inline]
    pub const fn is_nan(self) -> bool {
        const SIGN_MASK: u128 = F128Bits::NEG_ZERO.to_bits();
        const EXP_MASK: u128 = F128Bits::INFINITY.to_bits();
        (self.to_bits() & !SIGN_MASK) > EXP_MASK
    }

    /// Returns [`true`] if the number is infiniteN.
    ///
    /// # Example
    ///
    /// ```rust
    /// use fixed::F128Bits;
    ///
    /// assert!(F128Bits::INFINITY.is_infinite());
    /// assert!(F128Bits::NEG_INFINITY.is_infinite());
    ///
    /// assert!(!F128Bits::ONE.is_infinite());
    /// assert!(!F128Bits::NAN.is_infinite());
    /// ```
    #[inline]
    pub const fn is_infinite(self) -> bool {
        const SIGN_MASK: u128 = F128Bits::NEG_ZERO.to_bits();
        const EXP_MASK: u128 = F128Bits::INFINITY.to_bits();
        (self.to_bits() & !SIGN_MASK) == EXP_MASK
    }

    /// Returns [`true`] if the number is neither inifinte nor NaN.
    ///
    /// # Example
    ///
    /// ```rust
    /// use fixed::F128Bits;
    ///
    /// assert!(F128Bits::ONE.is_finite());
    /// assert!(F128Bits::MAX.is_finite());
    ///
    /// assert!(!F128Bits::INFINITY.is_finite());
    /// assert!(!F128Bits::NEG_INFINITY.is_finite());
    /// assert!(!F128Bits::NAN.is_finite());
    /// ```
    #[inline]
    pub const fn is_finite(self) -> bool {
        const EXP_MASK: u128 = F128Bits::INFINITY.to_bits();
        (self.to_bits() & EXP_MASK) != EXP_MASK
    }

    /// Returns [`true`] if the number is zero.
    ///
    /// # Example
    ///
    /// ```rust
    /// use fixed::F128Bits;
    ///
    /// assert!(F128Bits::ZERO.is_zero());
    /// assert!(F128Bits::NEG_ZERO.is_zero());
    ///
    /// assert!(!F128Bits::MIN_POSITIVE_SUB.is_zero());
    /// assert!(!F128Bits::NAN.is_zero());
    /// ```
    #[inline]
    pub const fn is_zero(self) -> bool {
        const SIGN_MASK: u128 = F128Bits::NEG_ZERO.to_bits();
        (self.to_bits() & !SIGN_MASK) == 0
    }

    /// Returns [`true`] if the number is subnormal.
    ///
    /// # Example
    ///
    /// ```rust
    /// use fixed::F128Bits;
    ///
    /// assert!(F128Bits::MIN_POSITIVE_SUB.is_subnormal());
    ///
    /// assert!(!F128Bits::ZERO.is_subnormal());
    /// assert!(!F128Bits::MIN_POSITIVE.is_subnormal());
    /// ```
    #[inline]
    pub const fn is_subnormal(self) -> bool {
        const SIGN_MASK: u128 = F128Bits::NEG_ZERO.to_bits();
        let abs = self.to_bits() & !SIGN_MASK;
        0 < abs && abs < F128Bits::MIN_POSITIVE.to_bits()
    }

    /// Returns [`true`] if the number is neither zero, infinite, subnormal, or NaN.
    ///
    /// # Example
    ///
    /// ```rust
    /// use fixed::F128Bits;
    ///
    /// assert!(F128Bits::MIN.is_normal());
    /// assert!(F128Bits::MIN_POSITIVE.is_normal());
    /// assert!(F128Bits::MAX.is_normal());
    ///
    /// assert!(!F128Bits::ZERO.is_normal());
    /// assert!(!F128Bits::MIN_POSITIVE_SUB.is_normal());
    /// assert!(!F128Bits::INFINITY.is_normal());
    /// assert!(!F128Bits::NAN.is_normal());
    /// ```
    #[inline]
    pub const fn is_normal(self) -> bool {
        const SIGN_MASK: u128 = F128Bits::NEG_ZERO.to_bits();
        let abs = self.to_bits() & !SIGN_MASK;
        F128Bits::MIN_POSITIVE.to_bits() <= abs && abs <= F128Bits::MAX.to_bits()
    }

    /// Returns the floating point category of the number.
    ///
    /// If only one property is going to be tested, it is generally faster to
    /// use the specific predicate instead.
    ///
    /// # Example
    ///
    /// ```rust
    /// use core::num::FpCategory;
    /// use fixed::F128Bits;
    ///
    /// assert_eq!(F128Bits::ZERO.classify(), FpCategory::Zero);
    /// assert_eq!(F128Bits::MIN_POSITIVE_SUB.classify(), FpCategory::Subnormal);
    /// assert_eq!(F128Bits::MIN_POSITIVE.classify(), FpCategory::Normal);
    /// assert_eq!(F128Bits::INFINITY.classify(), FpCategory::Infinite);
    /// assert_eq!(F128Bits::NAN.classify(), FpCategory::Nan);
    /// ```
    #[inline]
    pub const fn classify(self) -> FpCategory {
        const EXP_MASK: u128 = F128Bits::INFINITY.to_bits();
        const MANT_MASK: u128 = F128Bits::MIN_POSITIVE.to_bits() - 1;
        let exp = self.to_bits() & EXP_MASK;
        let mant = self.to_bits() & MANT_MASK;
        if exp == 0 {
            if mant == 0 {
                FpCategory::Zero
            } else {
                FpCategory::Subnormal
            }
        } else if exp == EXP_MASK {
            if mant == 0 {
                FpCategory::Infinite
            } else {
                FpCategory::Nan
            }
        } else {
            FpCategory::Normal
        }
    }

    /// Returns [`true`] if the number has a positive sign, including +0, +∞,
    /// and NaN without a negative sign bit.
    ///
    /// # Example
    ///
    /// ```rust
    /// use fixed::F128Bits;
    ///
    /// assert!(F128Bits::ZERO.is_sign_positive());
    /// assert!(F128Bits::MAX.is_sign_positive());
    /// assert!(F128Bits::INFINITY.is_sign_positive());
    ///
    /// assert!(!F128Bits::NEG_ZERO.is_sign_positive());
    /// assert!(!F128Bits::MIN.is_sign_positive());
    /// assert!(!F128Bits::NEG_INFINITY.is_sign_positive());
    /// ```
    #[inline]
    pub const fn is_sign_positive(self) -> bool {
        const SIGN_MASK: u128 = F128Bits::NEG_ZERO.to_bits();
        (self.to_bits() & SIGN_MASK) == 0
    }

    /// Returns [`true`] if the number has a negative sign, including &minus;0,
    /// &minus;∞, and NaN with a negative sign bit.
    ///
    /// # Example
    ///
    /// ```rust
    /// use fixed::F128Bits;
    ///
    /// assert!(F128Bits::NEG_ZERO.is_sign_negative());
    /// assert!(F128Bits::MIN.is_sign_negative());
    /// assert!(F128Bits::NEG_INFINITY.is_sign_negative());
    ///
    /// assert!(!F128Bits::ZERO.is_sign_negative());
    /// assert!(!F128Bits::MAX.is_sign_negative());
    /// assert!(!F128Bits::INFINITY.is_sign_negative());
    /// ```
    #[inline]
    pub const fn is_sign_negative(self) -> bool {
        const SIGN_MASK: u128 = F128Bits::NEG_ZERO.to_bits();
        (self.to_bits() & SIGN_MASK) != 0
    }
}

impl PartialEq for F128Bits {
    #[inline]
    fn eq(&self, other: &F128Bits) -> bool {
        const SIGN_MASK: u128 = F128Bits::NEG_ZERO.to_bits();
        if self.is_nan() || other.is_nan() {
            return false;
        }
        let a = self.to_bits();
        let b = other.to_bits();
        // handle zero
        if ((a | b) & !SIGN_MASK) == 0 {
            return true;
        }
        a == b
    }
}

impl PartialOrd for F128Bits {
    #[inline]
    fn partial_cmp(&self, other: &F128Bits) -> Option<Ordering> {
        const SIGN_MASK: u128 = F128Bits::NEG_ZERO.to_bits();
        if self.is_nan() || other.is_nan() {
            return None;
        }
        let a = self.to_bits();
        let b = other.to_bits();
        // handle zero
        if ((a | b) & !SIGN_MASK) == 0 {
            return Some(Ordering::Equal);
        }
        match (a & SIGN_MASK != 0, b & SIGN_MASK != 0) {
            (false, false) => a.partial_cmp(&b),
            (true, true) => b.partial_cmp(&a),
            (false, true) => Some(Ordering::Greater),
            (true, false) => Some(Ordering::Less),
        }
    }
}
