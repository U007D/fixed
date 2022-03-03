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
    traits::FixedBits, FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16,
    FixedU32, FixedU64, FixedU8,
};
use core::mem;

pub(crate) enum Shift {
    Right(u32),
    Left(u32),
    RightAll,
    LeftAll,
}

#[inline]
pub(crate) fn src_shift(dst_frac: i32, src_frac: i32, src_bits: u32) -> Shift {
    if dst_frac <= src_frac {
        let shift = src_frac.wrapping_sub(dst_frac) as u32;
        if shift >= src_bits {
            Shift::RightAll
        } else {
            Shift::Right(shift)
        }
    } else {
        let shift = dst_frac.wrapping_sub(src_frac) as u32;
        if shift >= src_bits {
            Shift::LeftAll
        } else {
            Shift::Left(shift)
        }
    }
}

macro_rules! impl_fixed_from_bits {
    ($Fixed:ident($Inner:ident, $nbits:expr), $InnerI:ident, $InnerU:ident) => {
        impl<const FRAC: i32> $Fixed<FRAC> {
            pub(crate) fn fixed_from_bits<Src>(src: Src, src_frac: i32) -> ($Fixed<FRAC>, bool)
            where
                Src: FixedBits,
            {
                let src_is_signed = Src::try_from(-1i8).is_ok();
                let src_bits = mem::size_of::<Src>() as u32 * 8;
                // If src is narrower and we need to shift left, we widen src.
                if $nbits > src_bits && FRAC > src_frac {
                    if src_is_signed {
                        let (widened, overflow): ($InnerI, bool) = src.overflowing_cast();
                        debug_assert!(!overflow);
                        return $Fixed::fixed_from_bits(widened, src_frac);
                    } else {
                        let (widened, overflow): ($InnerU, bool) = src.overflowing_cast();
                        debug_assert!(!overflow);
                        return $Fixed::fixed_from_bits(widened, src_frac);
                    }
                }

                match src_shift(FRAC, src_frac, src_bits) {
                    Shift::Right(shift) => {
                        let shifted = src >> shift;
                        let (bits, overflow) = shifted.overflowing_cast();
                        ($Fixed::from_bits(bits), overflow)
                    }
                    Shift::Left(shift) => {
                        // src is at least as wide as dst.
                        // Cast before shifting, in case we are converting a signed positive
                        // to an unsigned, for example 01.00 signed into 1.000 unsigned.
                        // Shifting first would produce signed 1.000 which is negative and
                        // the cast would then overflow.
                        // Casting first would produce unsigned 01.00 which can then be shifted.
                        let (cast, overflow1): ($Inner, bool) = src.overflowing_cast();
                        let shifted = cast << shift;
                        let overflow2 = (shifted >> shift) != cast;
                        ($Fixed::from_bits(shifted), overflow1 || overflow2)
                    }
                    Shift::RightAll => {
                        if src_is_signed {
                            // preserve sign bit
                            let shifted = src >> src_bits - 1;
                            let (bits, overflow) = shifted.overflowing_cast();
                            ($Fixed::from_bits(bits), overflow)
                        } else {
                            ($Fixed::ZERO, false)
                        }
                    }
                    Shift::LeftAll => {
                        let src_zero = match Src::try_from(0i8) {
                            Ok(zero) => zero,
                            Err(_) => unreachable!(),
                        };
                        ($Fixed::ZERO, src != src_zero)
                    }
                }
            }
        }
    };
}

impl_fixed_from_bits! { FixedI8(i8, 8), i8, u8 }
impl_fixed_from_bits! { FixedI16(i16, 16), i16, u16 }
impl_fixed_from_bits! { FixedI32(i32, 32), i32, u32 }
impl_fixed_from_bits! { FixedI64(i64, 64), i64, u64 }
impl_fixed_from_bits! { FixedI128(i128, 128), i128, u128 }
impl_fixed_from_bits! { FixedU8(u8, 8), i8, u8 }
impl_fixed_from_bits! { FixedU16(u16, 16), i16, u16 }
impl_fixed_from_bits! { FixedU32(u32, 32), i32, u32 }
impl_fixed_from_bits! { FixedU64(u64, 64), i64, u64 }
impl_fixed_from_bits! { FixedU128(u128, 128), i128, u128 }
