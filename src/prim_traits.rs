// Copyright © 2018–2024 Trevor Spiteri

// This library is free software: you can redistribute it and/or modify it under
// the terms of either
//
//   * the Apache License, Version 2.0 or
//   * the MIT License
//
// at your option.
//
// You should have recieved copies of the Apache License and the MIT License
// along with the library. If not, see
// <https://www.apache.org/licenses/LICENSE-2.0> and
// <https://opensource.org/licenses/MIT>.

use crate::{
    float_helper, int_helper,
    traits::{Fixed, FixedBits, FixedEquiv, FromFixed, ToFixed},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use az::{OverflowingAs, OverflowingCast, OverflowingCastFrom};
use bytemuck::TransparentWrapper;
use core::mem;
use half::{bf16 as half_bf16, f16 as half_f16};

impl ToFixed for bool {
    /// Converts a [`bool`] to a fixed-point number.
    ///
    /// # Panics
    ///
    /// When debug assertions are enabled, panics if the value does
    /// not fit. When debug assertions are not enabled, the wrapped
    /// value can be returned, but it is not considered a breaking
    /// change if in the future it panics; if wrapping is required use
    /// [`wrapping_to_fixed`] instead.
    ///
    /// [`wrapping_to_fixed`]: ToFixed::wrapping_to_fixed
    #[inline]
    #[track_caller]
    fn to_fixed<F: Fixed>(self) -> F {
        ToFixed::to_fixed(u8::from(self))
    }

    /// Converts a [`bool`] to a fixed-point number if it fits, otherwise returns [`None`].
    #[inline]
    fn checked_to_fixed<F: Fixed>(self) -> Option<F> {
        ToFixed::checked_to_fixed(u8::from(self))
    }

    /// Convert a [`bool`] to a fixed-point number, saturating if it does not fit.
    #[inline]
    fn saturating_to_fixed<F: Fixed>(self) -> F {
        ToFixed::saturating_to_fixed(u8::from(self))
    }

    /// Converts a [`bool`] to a fixed-point number, wrapping if it does not fit.
    #[inline]
    fn wrapping_to_fixed<F: Fixed>(self) -> F {
        ToFixed::wrapping_to_fixed(u8::from(self))
    }

    /// Converts a [`bool`] to a fixed-point number.
    ///
    /// Returns a [tuple] of the fixed-point number and a [`bool`]
    /// indicating whether an overflow has occurred. On overflow, the
    /// wrapped value is returned.
    #[inline]
    fn overflowing_to_fixed<F: Fixed>(self) -> (F, bool) {
        ToFixed::overflowing_to_fixed(u8::from(self))
    }

    /// Converts a [`bool`] to a fixed-point number, panicking if it
    /// does not fit.
    ///
    /// # Panics
    ///
    /// Panics if the value does not fit, even when debug assertions
    /// are not enabled.
    #[inline]
    #[track_caller]
    fn unwrapped_to_fixed<F: Fixed>(self) -> F {
        ToFixed::unwrapped_to_fixed(u8::from(self))
    }
}

macro_rules! impl_int {
    ($Int:ident as $IntAs:ident, $AsEquiv:ident) => {
        impl FromFixed for $Int {
            /// Converts a fixed-point number to an integer.
            ///
            /// Any fractional bits are discarded, which rounds towards &minus;∞.
            ///
            /// # Panics
            ///
            /// When debug assertions are enabled, panics if the value
            /// does not fit. When debug assertions are not enabled,
            /// the wrapped value can be returned, but it is not
            /// considered a breaking change if in the future it
            /// panics; if wrapping is required use
            /// [`wrapping_from_fixed`] instead.
            ///
            /// [`wrapping_from_fixed`]: FromFixed::wrapping_from_fixed
            #[inline]
            #[track_caller]
            fn from_fixed<F: Fixed>(src: F) -> Self {
                $AsEquiv::<0>::from_fixed(src).to_bits() as $Int
            }

            /// Converts a fixed-point number to an integer if it fits, otherwise returns [`None`].
            ///
            /// Any fractional bits are discarded, which rounds towards &minus;∞.
            #[inline]
            fn checked_from_fixed<F: Fixed>(src: F) -> Option<Self> {
                $AsEquiv::<0>::checked_from_fixed(src).map(|x| x.to_bits() as $Int)
            }

            /// Converts a fixed-point number to an integer, saturating if it does not fit.
            ///
            /// Any fractional bits are discarded, which rounds towards &minus;∞.
            #[inline]
            fn saturating_from_fixed<F: Fixed>(src: F) -> Self {
                $AsEquiv::<0>::saturating_from_fixed(src).to_bits() as $Int
            }

            /// Converts a fixed-point number to an integer, wrapping if it does not fit.
            ///
            /// Any fractional bits are discarded, which rounds towards &minus;∞.
            #[inline]
            fn wrapping_from_fixed<F: Fixed>(src: F) -> Self {
                $AsEquiv::<0>::wrapping_from_fixed(src).to_bits() as $Int
            }

            /// Converts a fixed-point number to an integer.
            ///
            /// Returns a [tuple] of the value and a [`bool`] indicating whether
            /// an overflow has occurred. On overflow, the wrapped value is
            /// returned.
            ///
            /// Any fractional bits are discarded, which rounds towards &minus;∞.
            #[inline]
            fn overflowing_from_fixed<F: Fixed>(src: F) -> (Self, bool) {
                let (fixed, overflow) = $AsEquiv::<0>::overflowing_from_fixed(src);
                (fixed.to_bits() as $Int, overflow)
            }

            /// Converts a fixed-point number to an integer, panicking if it does not fit.
            ///
            /// Any fractional bits are discarded, which rounds towards &minus;∞.
            ///
            /// # Panics
            ///
            /// Panics if the value
            /// does not fit, even when debug assertions are not enabled.
            #[inline]
            #[track_caller]
            fn unwrapped_from_fixed<F: Fixed>(src: F) -> Self {
                $AsEquiv::<0>::unwrapped_from_fixed(src).to_bits() as $Int
            }
        }

        impl ToFixed for $Int {
            /// Converts an integer to a fixed-point number.
            ///
            /// # Panics
            ///
            /// When debug assertions are enabled, panics if the value
            /// does not fit. When debug assertions are not enabled,
            /// the wrapped value can be returned, but it is not
            /// considered a breaking change if in the future it
            /// panics; if wrapping is required use
            /// [`wrapping_to_fixed`] instead.
            ///
            /// [`wrapping_to_fixed`]: ToFixed::wrapping_to_fixed
            #[inline]
            #[track_caller]
            fn to_fixed<F: Fixed>(self) -> F {
                $AsEquiv::<0>::from_bits(self as $IntAs).to_fixed()
            }

            /// Converts an integer to a fixed-point number if it fits, otherwise returns [`None`].
            #[inline]
            fn checked_to_fixed<F: Fixed>(self) -> Option<F> {
                $AsEquiv::<0>::from_bits(self as $IntAs).checked_to_fixed()
            }

            /// Converts an integer to a fixed-point number, saturating if it does not fit.
            #[inline]
            fn saturating_to_fixed<F: Fixed>(self) -> F {
                $AsEquiv::<0>::from_bits(self as $IntAs).saturating_to_fixed()
            }

            /// Converts an integer to a fixed-point number, wrapping if it does not fit.
            #[inline]
            fn wrapping_to_fixed<F: Fixed>(self) -> F {
                $AsEquiv::<0>::from_bits(self as $IntAs).wrapping_to_fixed()
            }

            /// Converts an integer to a fixed-point number.
            ///
            /// Returns a [tuple] of the fixed-point number and a [`bool`]
            /// indicating whether an overflow has occurred. On overflow, the
            /// wrapped value is returned.
            #[inline]
            fn overflowing_to_fixed<F: Fixed>(self) -> (F, bool) {
                $AsEquiv::<0>::from_bits(self as $IntAs).overflowing_to_fixed()
            }

            /// Converts an integer to a fixed-point number, panicking if it does not fit.
            ///
            /// # Panics
            ///
            /// Panics if the value does not fit, even when debug
            /// assertions are not enabled.
            #[inline]
            #[track_caller]
            fn unwrapped_to_fixed<F: Fixed>(self) -> F {
                $AsEquiv::<0>::from_bits(self as $IntAs).unwrapped_to_fixed()
            }
        }
    };
}

impl_int! { i8 as i8, FixedI8 }
impl_int! { i16 as i16, FixedI16 }
impl_int! { i32 as i32, FixedI32 }
impl_int! { i64 as i64, FixedI64 }
impl_int! { i128 as i128, FixedI128 }
#[cfg(target_pointer_width = "16")]
impl_int! { isize as i16, FixedI16 }
#[cfg(target_pointer_width = "32")]
impl_int! { isize as i32, FixedI32 }
#[cfg(target_pointer_width = "64")]
impl_int! { isize as i64, FixedI64 }
impl_int! { u8 as u8, FixedU8 }
impl_int! { u16 as u16, FixedU16 }
impl_int! { u32 as u32, FixedU32 }
impl_int! { u64 as u64, FixedU64 }
impl_int! { u128 as u128, FixedU128 }
#[cfg(target_pointer_width = "16")]
impl_int! { usize as u16, FixedU16 }
#[cfg(target_pointer_width = "32")]
impl_int! { usize as u32, FixedU32 }
#[cfg(target_pointer_width = "64")]
impl_int! { usize as u64, FixedU64 }

macro_rules! impl_int_equiv {
    ($Int:ident, $Equiv:ident) => {
        impl FixedEquiv for $Int {
            type Equiv = $Equiv<0>;

            #[inline]
            fn to_fixed_equiv(self) -> $Equiv<0> {
                $Equiv::from_bits(self)
            }

            #[inline]
            fn as_fixed_equiv(&self) -> &$Equiv<0> {
                $Equiv::wrap_ref(self)
            }

            #[inline]
            fn as_fixed_equiv_mut(&mut self) -> &mut $Equiv<0> {
                $Equiv::wrap_mut(self)
            }

            #[inline]
            fn from_fixed_equiv(f: $Equiv<0>) -> $Int {
                f.to_bits()
            }

            #[inline]
            fn ref_from_fixed_equiv(f: &$Equiv<0>) -> &$Int {
                &f.bits
            }

            #[inline]
            fn mut_from_fixed_equiv(f: &mut $Equiv<0>) -> &mut $Int {
                &mut f.bits
            }
        }
    };
}

impl_int_equiv! { i8, FixedI8 }
impl_int_equiv! { i16, FixedI16 }
impl_int_equiv! { i32, FixedI32 }
impl_int_equiv! { i64, FixedI64 }
impl_int_equiv! { i128, FixedI128 }
impl_int_equiv! { u8, FixedU8 }
impl_int_equiv! { u16, FixedU16 }
impl_int_equiv! { u32, FixedU32 }
impl_int_equiv! { u64, FixedU64 }
impl_int_equiv! { u128, FixedU128 }

#[inline]
fn leading_ones<Bits: FixedBits>(bits: Bits) -> u32 {
    let neg_overflows = Bits::overflowing_cast_from(-1i8).1;
    let is_signed = !neg_overflows;
    match (is_signed, mem::size_of::<Bits>()) {
        (false, 1) => bits.overflowing_as::<u8>().0.leading_ones(),
        (false, 2) => bits.overflowing_as::<u16>().0.leading_ones(),
        (false, 4) => bits.overflowing_as::<u32>().0.leading_ones(),
        (false, 8) => bits.overflowing_as::<u64>().0.leading_ones(),
        (false, 16) => bits.overflowing_as::<u128>().0.leading_ones(),
        (true, 1) => bits.overflowing_as::<i8>().0.leading_ones(),
        (true, 2) => bits.overflowing_as::<i16>().0.leading_ones(),
        (true, 4) => bits.overflowing_as::<i32>().0.leading_ones(),
        (true, 8) => bits.overflowing_as::<i64>().0.leading_ones(),
        (true, 16) => bits.overflowing_as::<i128>().0.leading_ones(),
        _ => unreachable!(),
    }
}

#[inline]
fn leading_zeros<Bits: FixedBits>(bits: Bits) -> u32 {
    let neg_overflows = Bits::overflowing_cast_from(-1i8).1;
    let is_signed = !neg_overflows;
    match (is_signed, mem::size_of::<Bits>()) {
        (false, 1) => bits.overflowing_as::<u8>().0.leading_zeros(),
        (false, 2) => bits.overflowing_as::<u16>().0.leading_zeros(),
        (false, 4) => bits.overflowing_as::<u32>().0.leading_zeros(),
        (false, 8) => bits.overflowing_as::<u64>().0.leading_zeros(),
        (false, 16) => bits.overflowing_as::<u128>().0.leading_zeros(),
        (true, 1) => bits.overflowing_as::<i8>().0.leading_zeros(),
        (true, 2) => bits.overflowing_as::<i16>().0.leading_zeros(),
        (true, 4) => bits.overflowing_as::<i32>().0.leading_zeros(),
        (true, 8) => bits.overflowing_as::<i64>().0.leading_zeros(),
        (true, 16) => bits.overflowing_as::<i128>().0.leading_zeros(),
        _ => unreachable!(),
    }
}

macro_rules! impl_float {
    ($Float:ident, $FloatI:ident, $FloatU:ident) => {
        impl FromFixed for $Float {
            /// Converts a fixed-point number to a floating-point number.
            ///
            /// Rounding is to the nearest, with ties rounded to even.
            ///
            /// # Panics
            ///
            /// When debug assertions are enabled, panics if the value
            /// does not fit. When debug assertions are not enabled,
            /// the wrapped value can be returned, but it is not
            /// considered a breaking change if in the future it
            /// panics; if wrapping is required use
            /// [`wrapping_from_fixed`] instead.
            ///
            /// [`wrapping_from_fixed`]: FromFixed::wrapping_from_fixed
            #[inline]
            #[track_caller]
            fn from_fixed<F: Fixed>(src: F) -> Self {
                let zero = F::Bits::overflowing_cast_from(0u8).0;
                let src = src.to_bits();
                // handle zero early so that we can assume bits != 0
                if src == zero {
                    return Self::from_bits(0);
                }

                let src_neg_overflows = F::Bits::overflowing_cast_from(-1i8).1;
                let src_is_signed = !src_neg_overflows;
                let src_bits = mem::size_of::<F>() as u32 * 8;
                let (neg, abs, excess_shift) = if $FloatU::BITS >= src_bits {
                    if src_is_signed {
                        let (widened, overflow): ($FloatI, bool) = src.overflowing_cast();
                        debug_assert!(!overflow);
                        let (neg, abs) = int_helper::$FloatI::neg_abs(widened);
                        let shift = abs.leading_zeros();
                        (neg, abs << shift, shift as i32)
                    } else {
                        let (widened, overflow): ($FloatU, bool) = src.overflowing_cast();
                        debug_assert!(!overflow);
                        let shift = widened.leading_zeros();
                        (false, widened << shift, shift as i32)
                    }
                } else {
                    // We need to narrow the source. First we push the bits to
                    // the left so that we don't crop off bits we'd need.
                    let lossless_shift = if !src_is_signed {
                        leading_zeros(src)
                    } else if src < zero {
                        leading_ones(src) - 1
                    } else {
                        leading_zeros(src) - 1
                    };
                    let src = src << lossless_shift;
                    let narrow_by = src_bits - $FloatU::BITS;
                    let narrowed = src >> narrow_by;
                    let sig_lower_bits = narrowed << narrow_by != src;
                    if src_is_signed {
                        let (narrowed, overflow) = narrowed.overflowing_as::<$FloatI>();
                        debug_assert!(!overflow);
                        let (neg, mut abs) = int_helper::$FloatI::neg_abs(narrowed);
                        let shift = abs.leading_zeros();
                        abs <<= shift;
                        if sig_lower_bits {
                            abs |= 1;
                        }
                        (neg, abs, (shift + lossless_shift) as i32 - narrow_by as i32)
                    } else {
                        let (mut narrowed, overflow) = narrowed.overflowing_as::<$FloatU>();
                        debug_assert!(!overflow);
                        debug_assert!(narrowed.leading_zeros() == 0);
                        if sig_lower_bits {
                            narrowed |= 1;
                        }
                        (false, narrowed, lossless_shift as i32 - narrow_by as i32)
                    }
                };
                // excess_shift is how much we have shifted the bits to the left.
                // So eventually we need to divide if excess_shift is positive.
                // Similarly we need to divide if F::FRAC_BITS is positive.
                // That means that we can add excess_shift and F::FRAC_BITS.
                let frac = F::FRAC_BITS.saturating_add(excess_shift);
                float_helper::$Float::from_neg_abs(neg, abs, frac)
            }

            /// Converts a fixed-point number to a floating-point
            /// number if it fits, otherwise returns [`None`].
            ///
            /// Rounding is to the nearest, with ties rounded to even.
            #[inline]
            fn checked_from_fixed<F: Fixed>(src: F) -> Option<Self> {
                Some(FromFixed::from_fixed(src))
            }

            /// Converts a fixed-point number to a floating-point
            /// number, saturating if it does not fit.
            ///
            /// Rounding is to the nearest, with ties rounded to even.
            #[inline]
            fn saturating_from_fixed<F: Fixed>(src: F) -> Self {
                FromFixed::from_fixed(src)
            }

            /// Converts a fixed-point number to a floating-point
            /// number, wrapping if it does not fit.
            ///
            /// Rounding is to the nearest, with ties rounded to even.
            #[inline]
            fn wrapping_from_fixed<F: Fixed>(src: F) -> Self {
                FromFixed::from_fixed(src)
            }

            /// Converts a fixed-point number to a floating-point number.
            ///
            /// Returns a [tuple] of the value and a [`bool`]
            /// indicating whether an overflow has occurred. On
            /// overflow, the wrapped value is returned.
            ///
            /// Rounding is to the nearest, with ties rounded to even.
            #[inline]
            fn overflowing_from_fixed<F: Fixed>(src: F) -> (Self, bool) {
                (FromFixed::from_fixed(src), false)
            }

            /// Converts a fixed-point number to a floating-point
            /// number, panicking if it does not fit.
            ///
            /// Rounding is to the nearest, with ties rounded to even.
            ///
            /// # Panics
            ///
            /// Panics if the value does not fit, even when debug
            /// assertions are not enabled.
            #[inline]
            #[track_caller]
            fn unwrapped_from_fixed<F: Fixed>(src: F) -> Self {
                FromFixed::from_fixed(src)
            }
        }

        impl ToFixed for $Float {
            comment! {
                "Converts a floating-point number to a fixed-point number.

Rounding is to the nearest, with ties rounded to even.

# Panics

Panics if `self` is not [finite].

When debug assertions are enabled, also panics if the value does not
fit. When debug assertions are not enabled, the wrapped value can be
returned, but it is not considered a breaking change if in the future
it panics; if wrapping is required use [`wrapping_to_fixed`] instead.

[`wrapping_to_fixed`]: ToFixed::wrapping_to_fixed
[finite]: ", stringify!($Float), "::is_finite
";
                #[inline]
                #[track_caller]
                fn to_fixed<F: Fixed>(self) -> F {
                    let (wrapped, overflow) = ToFixed::overflowing_to_fixed(self);
                    debug_assert!(!overflow, "overflow");
                    wrapped
                }
            }

            /// Converts a floating-point number to a fixed-point
            /// number if it fits, otherwise returns [`None`].
            ///
            /// Rounding is to the nearest, with ties rounded to even.
            #[inline]
            fn checked_to_fixed<F: Fixed>(self) -> Option<F> {
                if !self.is_finite() {
                    return None;
                }
                match ToFixed::overflowing_to_fixed(self) {
                    (wrapped, false) => Some(wrapped),
                    (_, true) => None,
                }
            }

            comment! {
                "Converts a floating-point number to a fixed-point
number, saturating if it does not fit.

Rounding is to the nearest, with ties rounded to even.

# Panics

Panics if `self` is [NaN].

[NaN]: ", stringify!($Float), "::is_nan
";
                #[inline]
                #[track_caller]
                fn saturating_to_fixed<F: Fixed>(self) -> F {
                    if self.is_nan() {
                        panic!("NaN");
                    }
                    if self.is_finite() {
                        let (wrapped, overflow) = ToFixed::overflowing_to_fixed(self);
                        if !overflow {
                            return wrapped;
                        }
                    }
                    // either self is infinite, or overflow flag returned is true
                    if self.is_sign_negative() {
                        F::MIN
                    } else {
                        F::MAX
                    }
                }
            }

            comment! {
                "Converts a floating-point number to a fixed-point
number, wrapping if it does not fit.

Rounding is to the nearest, with ties rounded to even.

# Panics

Panics if `self` is not [finite].

[finite]: ", stringify!($Float), "::is_finite
";
                #[inline]
                #[track_caller]
                fn wrapping_to_fixed<F: Fixed>(self) -> F {
                    let (wrapped, _) = ToFixed::overflowing_to_fixed(self);
                    wrapped
                }
            }

            comment! {
            "Converts a floating-point number to a fixed-point number.

Returns a [tuple] of the fixed-point number and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

Rounding is to the nearest, with ties rounded to even.

# Panics

Panics if `self` is not [finite].

[finite]: ", stringify!($Float), "::is_finite
";
                #[inline]
                #[track_caller]
                fn overflowing_to_fixed<F: Fixed>(self) -> (F, bool) {
                    float_helper::$Float::overflowing_to_fixed(self)
                }
            }

            comment! {
                "Converts a floating-point number to a fixed-point
number, panicking if it does not fit.

Rounding is to the nearest, with ties rounded to even.

# Panics

Panics if `self` is not [finite] or if the value does not fit, even
when debug assertions are not enabled.

[finite]: ", stringify!($Float), "::is_finite
";
                #[inline]
                #[track_caller]
                fn unwrapped_to_fixed<F: Fixed>(self) -> F {
                    match ToFixed::overflowing_to_fixed(self) {
                        (val, false) => val,
                        (_, true) => panic!("overflow"),
                    }
                }
            }
        }
    };
}

impl_float! { half_f16, i16, u16 }
impl_float! { half_bf16, i16, u16 }
impl_float! { f16, i16, u16 }
impl_float! { f32, i32, u32 }
impl_float! { f64, i64, u64 }
impl_float! { f128, i128, u128 }
