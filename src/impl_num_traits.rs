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

use crate::{
    consts,
    types::extra::{If, True},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8, ParseFixedError,
};
use core::fmt::{Display, Formatter, Result as FmtResult};
use num_traits::{
    bounds::Bounded,
    cast::{FromPrimitive, ToPrimitive},
    float::FloatConst,
    identities::{One, Zero},
    ops::{
        checked::{
            CheckedAdd, CheckedDiv, CheckedMul, CheckedNeg, CheckedRem, CheckedShl, CheckedShr,
            CheckedSub,
        },
        inv::Inv,
        mul_add::{MulAdd, MulAddAssign},
        overflowing::{OverflowingAdd, OverflowingMul, OverflowingSub},
        saturating::{SaturatingAdd, SaturatingMul, SaturatingSub},
        wrapping::{WrappingAdd, WrappingMul, WrappingNeg, WrappingShl, WrappingShr, WrappingSub},
    },
    sign::{Signed, Unsigned},
    Num,
};
#[cfg(feature = "std")]
use std::error::Error;

/// An error which can be returned when parsing a fixed-point number
/// with a given radix.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RadixParseFixedError {
    /// The radix is not 2, 8, 10 or 16.
    UnsupportedRadix,
    /// The string could not be parsed as a fixed-point number.
    ParseFixedError(ParseFixedError),
}

impl RadixParseFixedError {
    fn message(&self) -> &str {
        match self {
            RadixParseFixedError::UnsupportedRadix => "unsupported radix",
            RadixParseFixedError::ParseFixedError(e) => e.message(),
        }
    }
}

impl Display for RadixParseFixedError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Display::fmt(self.message(), f)
    }
}

#[cfg(feature = "std")]
impl Error for RadixParseFixedError {
    fn description(&self) -> &str {
        self.message()
    }
}

macro_rules! impl_traits {
    ($Fixed:ident, $nbits:expr, $one_max_frac:expr, $Signedness:tt) => {
        impl<const FRAC: u32> Bounded for $Fixed<FRAC> {
            #[inline]
            fn min_value() -> Self {
                Self::MIN
            }
            #[inline]
            fn max_value() -> Self {
                Self::MAX
            }
        }

        impl<const FRAC: u32> Zero for $Fixed<FRAC> {
            #[inline]
            fn zero() -> Self {
                Self::ZERO
            }
            #[inline]
            fn is_zero(&self) -> bool {
                (*self).is_zero()
            }
        }

        impl<const FRAC: u32> One for $Fixed<FRAC>
        where
            If<{ FRAC <= $nbits }>: True,
            If<{ FRAC <= $one_max_frac }>: True,
        {
            #[inline]
            fn one() -> Self {
                Self::ONE
            }
        }

        impl<const FRAC: u32> Num for $Fixed<FRAC>
        where
            If<{ FRAC <= $nbits }>: True,
            If<{ FRAC <= $one_max_frac }>: True,
        {
            type FromStrRadixErr = RadixParseFixedError;

            #[inline]
            fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
                match radix {
                    2 => Self::from_str_binary(str),
                    8 => Self::from_str_octal(str),
                    10 => str.parse(),
                    16 => Self::from_str_hex(str),
                    _ => return Err(RadixParseFixedError::UnsupportedRadix),
                }
                .map_err(RadixParseFixedError::ParseFixedError)
            }
        }

        impl<const FRAC: u32> Inv for $Fixed<FRAC>
        where
            If<{ FRAC <= $nbits }>: True,
        {
            type Output = Self;
            #[inline]
            fn inv(self) -> Self::Output {
                self.recip()
            }
        }

        if_signed! {
            $Signedness;
            impl<const FRAC: u32> Signed for $Fixed<FRAC>
            where
                If<{FRAC <= $nbits}>: True,
                If<{FRAC <= $one_max_frac}>: True,
            {
                #[inline]
                fn abs(&self) -> Self {
                    (*self).abs()
                }
                #[inline]
                fn abs_sub(&self, other: &Self) -> Self {
                    if *self < *other {
                        Self::ZERO
                    } else {
                        *self - *other
                    }
                }
                #[inline]
                fn signum(&self) -> Self {
                    (*self).signum()
                }
                #[inline]
                fn is_positive(&self) -> bool {
                    (*self).is_positive()
                }
                #[inline]
                fn is_negative(&self) -> bool {
                    (*self).is_negative()
                }
            }
        }

        if_unsigned! {
            $Signedness;
            impl<const FRAC: u32> Unsigned for $Fixed<FRAC>
            where
                If<{FRAC <= $nbits}>: True,
                If<{FRAC <= $one_max_frac}>: True,
            {
            }
        }

        impl<const FRAC: u32> CheckedAdd for $Fixed<FRAC> {
            #[inline]
            fn checked_add(&self, v: &Self) -> Option<Self> {
                (*self).checked_add(*v)
            }
        }

        impl<const FRAC: u32> CheckedSub for $Fixed<FRAC> {
            #[inline]
            fn checked_sub(&self, v: &Self) -> Option<Self> {
                (*self).checked_sub(*v)
            }
        }

        impl<const FRAC: u32> CheckedNeg for $Fixed<FRAC> {
            #[inline]
            fn checked_neg(&self) -> Option<Self> {
                (*self).checked_neg()
            }
        }

        impl<const FRAC: u32> CheckedMul for $Fixed<FRAC>
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn checked_mul(&self, v: &Self) -> Option<Self> {
                (*self).checked_mul(*v)
            }
        }

        impl<const FRAC: u32> CheckedDiv for $Fixed<FRAC>
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn checked_div(&self, v: &Self) -> Option<Self> {
                (*self).checked_div(*v)
            }
        }

        impl<const FRAC: u32> CheckedRem for $Fixed<FRAC> {
            #[inline]
            fn checked_rem(&self, v: &Self) -> Option<Self> {
                (*self).checked_rem(*v)
            }
        }

        impl<const FRAC: u32> CheckedShl for $Fixed<FRAC> {
            #[inline]
            fn checked_shl(&self, rhs: u32) -> Option<Self> {
                (*self).checked_shl(rhs)
            }
        }

        impl<const FRAC: u32> CheckedShr for $Fixed<FRAC> {
            #[inline]
            fn checked_shr(&self, rhs: u32) -> Option<Self> {
                (*self).checked_shr(rhs)
            }
        }

        impl<const FRAC: u32> SaturatingAdd for $Fixed<FRAC> {
            #[inline]
            fn saturating_add(&self, v: &Self) -> Self {
                (*self).saturating_add(*v)
            }
        }

        impl<const FRAC: u32> SaturatingSub for $Fixed<FRAC> {
            #[inline]
            fn saturating_sub(&self, v: &Self) -> Self {
                (*self).saturating_sub(*v)
            }
        }

        impl<const FRAC: u32> SaturatingMul for $Fixed<FRAC>
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn saturating_mul(&self, v: &Self) -> Self {
                (*self).saturating_mul(*v)
            }
        }

        impl<const FRAC: u32> WrappingAdd for $Fixed<FRAC> {
            #[inline]
            fn wrapping_add(&self, v: &Self) -> Self {
                (*self).wrapping_add(*v)
            }
        }

        impl<const FRAC: u32> WrappingSub for $Fixed<FRAC> {
            #[inline]
            fn wrapping_sub(&self, v: &Self) -> Self {
                (*self).wrapping_sub(*v)
            }
        }

        impl<const FRAC: u32> WrappingNeg for $Fixed<FRAC> {
            #[inline]
            fn wrapping_neg(&self) -> Self {
                (*self).wrapping_neg()
            }
        }

        impl<const FRAC: u32> WrappingMul for $Fixed<FRAC>
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn wrapping_mul(&self, v: &Self) -> Self {
                (*self).wrapping_mul(*v)
            }
        }

        impl<const FRAC: u32> WrappingShl for $Fixed<FRAC> {
            #[inline]
            fn wrapping_shl(&self, rhs: u32) -> Self {
                (*self).wrapping_shl(rhs)
            }
        }

        impl<const FRAC: u32> WrappingShr for $Fixed<FRAC> {
            #[inline]
            fn wrapping_shr(&self, rhs: u32) -> Self {
                (*self).wrapping_shr(rhs)
            }
        }

        impl<const FRAC: u32> OverflowingAdd for $Fixed<FRAC> {
            #[inline]
            fn overflowing_add(&self, v: &Self) -> (Self, bool) {
                (*self).overflowing_add(*v)
            }
        }

        impl<const FRAC: u32> OverflowingSub for $Fixed<FRAC> {
            #[inline]
            fn overflowing_sub(&self, v: &Self) -> (Self, bool) {
                (*self).overflowing_sub(*v)
            }
        }

        impl<const FRAC: u32> OverflowingMul for $Fixed<FRAC>
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn overflowing_mul(&self, v: &Self) -> (Self, bool) {
                (*self).overflowing_mul(*v)
            }
        }

        impl<const FRAC: u32, const MUL_FRAC: u32> MulAdd<$Fixed<MUL_FRAC>> for $Fixed<FRAC>
        where
            If<{ MUL_FRAC <= $nbits }>: True,
        {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn mul_add(self, a: $Fixed<MUL_FRAC>, b: $Fixed<FRAC>) -> $Fixed<FRAC> {
                self.mul_add(a, b)
            }
        }

        impl<const FRAC: u32, const MUL_FRAC: u32> MulAddAssign<$Fixed<MUL_FRAC>> for $Fixed<FRAC>
        where
            If<{ MUL_FRAC <= $nbits }>: True,
        {
            #[inline]
            fn mul_add_assign(&mut self, a: $Fixed<MUL_FRAC>, b: $Fixed<FRAC>) {
                *self = self.mul_add(a, b)
            }
        }

        impl<const FRAC: u32> FloatConst for $Fixed<FRAC>
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn E() -> Self {
                consts::E.to_num()
            }
            #[inline]
            fn FRAC_1_PI() -> Self {
                consts::FRAC_1_PI.to_num()
            }
            #[inline]
            fn FRAC_1_SQRT_2() -> Self {
                consts::FRAC_1_SQRT_2.to_num()
            }
            #[inline]
            fn FRAC_2_PI() -> Self {
                consts::FRAC_2_PI.to_num()
            }
            #[inline]
            fn FRAC_2_SQRT_PI() -> Self {
                consts::FRAC_2_SQRT_PI.to_num()
            }
            #[inline]
            fn FRAC_PI_2() -> Self {
                consts::FRAC_PI_2.to_num()
            }
            #[inline]
            fn FRAC_PI_3() -> Self {
                consts::FRAC_PI_3.to_num()
            }
            #[inline]
            fn FRAC_PI_4() -> Self {
                consts::FRAC_PI_4.to_num()
            }
            #[inline]
            fn FRAC_PI_6() -> Self {
                consts::FRAC_PI_6.to_num()
            }
            #[inline]
            fn FRAC_PI_8() -> Self {
                consts::FRAC_PI_8.to_num()
            }
            #[inline]
            fn LN_10() -> Self {
                consts::LN_10.to_num()
            }
            #[inline]
            fn LN_2() -> Self {
                consts::LN_2.to_num()
            }
            #[inline]
            fn LOG10_E() -> Self {
                consts::LOG10_E.to_num()
            }
            #[inline]
            fn LOG2_E() -> Self {
                consts::LOG2_E.to_num()
            }
            #[inline]
            fn PI() -> Self {
                consts::PI.to_num()
            }
            #[inline]
            fn SQRT_2() -> Self {
                consts::SQRT_2.to_num()
            }
            #[inline]
            fn TAU() -> Self {
                consts::TAU.to_num()
            }
            #[inline]
            fn LOG10_2() -> Self {
                consts::LOG10_2.to_num()
            }
            #[inline]
            fn LOG2_10() -> Self {
                consts::LOG2_10.to_num()
            }
        }

        impl<const FRAC: u32> ToPrimitive for $Fixed<FRAC>
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn to_i64(&self) -> Option<i64> {
                self.checked_to_num()
            }
            #[inline]
            fn to_u64(&self) -> Option<u64> {
                self.checked_to_num()
            }
            #[inline]
            fn to_isize(&self) -> Option<isize> {
                self.checked_to_num()
            }
            #[inline]
            fn to_i8(&self) -> Option<i8> {
                self.checked_to_num()
            }
            #[inline]
            fn to_i16(&self) -> Option<i16> {
                self.checked_to_num()
            }
            #[inline]
            fn to_i32(&self) -> Option<i32> {
                self.checked_to_num()
            }
            #[inline]
            fn to_i128(&self) -> Option<i128> {
                self.checked_to_num()
            }
            #[inline]
            fn to_usize(&self) -> Option<usize> {
                self.checked_to_num()
            }
            #[inline]
            fn to_u8(&self) -> Option<u8> {
                self.checked_to_num()
            }
            #[inline]
            fn to_u16(&self) -> Option<u16> {
                self.checked_to_num()
            }
            #[inline]
            fn to_u32(&self) -> Option<u32> {
                self.checked_to_num()
            }
            #[inline]
            fn to_u128(&self) -> Option<u128> {
                self.checked_to_num()
            }
            #[inline]
            fn to_f32(&self) -> Option<f32> {
                self.checked_to_num()
            }
            #[inline]
            fn to_f64(&self) -> Option<f64> {
                self.checked_to_num()
            }
        }

        impl<const FRAC: u32> FromPrimitive for $Fixed<FRAC>
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn from_i64(n: i64) -> Option<Self> {
                Self::checked_from_num(n)
            }
            #[inline]
            fn from_u64(n: u64) -> Option<Self> {
                Self::checked_from_num(n)
            }
            #[inline]
            fn from_isize(n: isize) -> Option<Self> {
                Self::checked_from_num(n)
            }
            #[inline]
            fn from_i8(n: i8) -> Option<Self> {
                Self::checked_from_num(n)
            }
            #[inline]
            fn from_i16(n: i16) -> Option<Self> {
                Self::checked_from_num(n)
            }
            #[inline]
            fn from_i32(n: i32) -> Option<Self> {
                Self::checked_from_num(n)
            }
            #[inline]
            fn from_i128(n: i128) -> Option<Self> {
                Self::checked_from_num(n)
            }
            #[inline]
            fn from_usize(n: usize) -> Option<Self> {
                Self::checked_from_num(n)
            }
            #[inline]
            fn from_u8(n: u8) -> Option<Self> {
                Self::checked_from_num(n)
            }
            #[inline]
            fn from_u16(n: u16) -> Option<Self> {
                Self::checked_from_num(n)
            }
            #[inline]
            fn from_u32(n: u32) -> Option<Self> {
                Self::checked_from_num(n)
            }
            #[inline]
            fn from_u128(n: u128) -> Option<Self> {
                Self::checked_from_num(n)
            }
            #[inline]
            fn from_f32(n: f32) -> Option<Self> {
                Self::checked_from_num(n)
            }
            #[inline]
            fn from_f64(n: f64) -> Option<Self> {
                Self::checked_from_num(n)
            }
        }
    };
}

impl_traits! { FixedI8, 8, 6, Signed }
impl_traits! { FixedI16, 16, 14, Signed }
impl_traits! { FixedI32, 32, 30, Signed }
impl_traits! { FixedI64, 64, 62, Signed }
impl_traits! { FixedI128, 128, 126, Signed }
impl_traits! { FixedU8, 8, 7, Unsigned }
impl_traits! { FixedU16, 16, 15, Unsigned }
impl_traits! { FixedU32, 32, 31, Unsigned }
impl_traits! { FixedU64, 64, 63, Unsigned }
impl_traits! { FixedU128, 128, 127, Unsigned }
