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
    float_helper, int_helper, FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128,
    FixedU16, FixedU32, FixedU64, FixedU8, F128,
};
use core::{
    cmp::Ordering,
    ops::{Shl, Shr},
};
use half::{bf16, f16};

macro_rules! fixed_cmp_fixed_instance {
    ($Lhs:ident($LhsInner:ident), $Rhs:ident($RhsInner:ident), $nbits:expr, $rhs_shl:ident) => {
        impl<const LHS_FRAC: i32, const RHS_FRAC: i32> PartialEq<$Rhs<RHS_FRAC>>
            for $Lhs<LHS_FRAC>
        {
            #[inline]
            fn eq(&self, rhs: &$Rhs<RHS_FRAC>) -> bool {
                if LHS_FRAC < RHS_FRAC {
                    return rhs.eq(self);
                }

                let (lhs_neg, lhs_abs) = int_helper::$LhsInner::neg_abs(self.to_bits());
                let (rhs_neg, rhs_abs) = int_helper::$RhsInner::neg_abs(rhs.to_bits());
                if lhs_neg != rhs_neg {
                    return false;
                }

                // LHS_FRAC >= RHS_FRAC
                match $rhs_shl(rhs_abs, LHS_FRAC, RHS_FRAC) {
                    None => false,
                    Some(shifted_rhs_abs) => lhs_abs == shifted_rhs_abs,
                }
            }
        }

        impl<const LHS_FRAC: i32, const RHS_FRAC: i32> PartialOrd<$Rhs<RHS_FRAC>>
            for $Lhs<LHS_FRAC>
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$Rhs<RHS_FRAC>) -> Option<Ordering> {
                if LHS_FRAC < RHS_FRAC {
                    return rhs.partial_cmp(self).map(Ordering::reverse);
                }

                let (lhs_neg, lhs_abs) = int_helper::$LhsInner::neg_abs(self.to_bits());
                let (rhs_neg, rhs_abs) = int_helper::$RhsInner::neg_abs(rhs.to_bits());
                if !lhs_neg && rhs_neg {
                    return Some(Ordering::Greater);
                }
                if lhs_neg && !rhs_neg {
                    return Some(Ordering::Less);
                }

                // LHS_FRAC >= RHS_FRAC
                match $rhs_shl(rhs_abs, LHS_FRAC, RHS_FRAC) {
                    None => {
                        // rhs is so large it doesn't fit
                        if lhs_neg {
                            // both lhs and rhs are negative, and rhs is even more negative
                            Some(Ordering::Greater)
                        } else {
                            Some(Ordering::Less)
                        }
                    }
                    Some(shifted_rhs_abs) => {
                        if lhs_neg {
                            // both lhs are negative, so reverse order
                            shifted_rhs_abs.partial_cmp(&lhs_abs)
                        } else {
                            lhs_abs.partial_cmp(&shifted_rhs_abs)
                        }
                    }
                }
            }

            #[inline]
            fn lt(&self, rhs: &$Rhs<RHS_FRAC>) -> bool {
                if LHS_FRAC < RHS_FRAC {
                    return rhs.gt(self);
                }

                let (lhs_neg, lhs_abs) = int_helper::$LhsInner::neg_abs(self.to_bits());
                let (rhs_neg, rhs_abs) = int_helper::$RhsInner::neg_abs(rhs.to_bits());
                if lhs_neg != rhs_neg {
                    return lhs_neg;
                }

                // LHS_FRAC >= RHS_FRAC
                match $rhs_shl(rhs_abs, LHS_FRAC, RHS_FRAC) {
                    None => !lhs_neg,
                    Some(shifted_rhs_abs) => {
                        if lhs_neg {
                            // both lhs are negative, so reverse order
                            lhs_abs > shifted_rhs_abs
                        } else {
                            lhs_abs < shifted_rhs_abs
                        }
                    }
                }
            }

            #[inline]
            fn le(&self, rhs: &$Rhs<RHS_FRAC>) -> bool {
                !self.gt(rhs)
            }

            #[inline]
            fn gt(&self, rhs: &$Rhs<RHS_FRAC>) -> bool {
                if LHS_FRAC < RHS_FRAC {
                    return rhs.lt(self);
                }

                let (lhs_neg, lhs_abs) = int_helper::$LhsInner::neg_abs(self.to_bits());
                let (rhs_neg, rhs_abs) = int_helper::$RhsInner::neg_abs(rhs.to_bits());
                if lhs_neg != rhs_neg {
                    return rhs_neg;
                }

                // LHS_FRAC >= RHS_FRAC
                match $rhs_shl(rhs_abs, LHS_FRAC, RHS_FRAC) {
                    None => lhs_neg,
                    Some(shifted_rhs_abs) => {
                        if lhs_neg {
                            // both lhs are negative, so reverse order
                            lhs_abs < shifted_rhs_abs
                        } else {
                            lhs_abs > shifted_rhs_abs
                        }
                    }
                }
            }

            #[inline]
            fn ge(&self, rhs: &$Rhs<RHS_FRAC>) -> bool {
                !self.lt(rhs)
            }
        }
    };
}

macro_rules! fixed_cmp_fixed_cross {
    ($FixedI:ident($InnerI:ident), $FixedU:ident($InnerU:ident), $nbits:expr, $rhs_shl:ident) => {
        fixed_cmp_fixed_instance! { $FixedI($InnerI), $FixedI($InnerI), $nbits, $rhs_shl }
        fixed_cmp_fixed_instance! { $FixedI($InnerI), $FixedU($InnerU), $nbits, $rhs_shl }
        fixed_cmp_fixed_instance! { $FixedU($InnerU), $FixedI($InnerI), $nbits, $rhs_shl }
        fixed_cmp_fixed_instance! { $FixedU($InnerU), $FixedU($InnerU), $nbits, $rhs_shl }

        #[inline]
        // lhs_frac >= rhs_frac
        const fn $rhs_shl(rhs_abs: $InnerU, lhs_frac: i32, rhs_frac: i32) -> Option<$InnerU> {
            debug_assert!(lhs_frac >= rhs_frac);
            let rhs_shl = lhs_frac.wrapping_sub(rhs_frac) as u32;
            if rhs_abs == 0 {
                Some(0)
            } else if rhs_shl >= $InnerU::BITS {
                None
            } else {
                let shifted = rhs_abs << rhs_shl;
                if (shifted >> rhs_shl) == rhs_abs {
                    Some(shifted)
                } else {
                    None
                }
            }
        }
    };
}

macro_rules! fixed_cmp_wider_instance {
    ($Wide:ident; $Narrow:ident, $Widened:ident) => {
        impl<const LHS_FRAC: i32, const RHS_FRAC: i32> PartialEq<$Wide<RHS_FRAC>>
            for $Narrow<LHS_FRAC>
        {
            #[inline]
            fn eq(&self, rhs: &$Wide<RHS_FRAC>) -> bool {
                let lhs = $Widened::<LHS_FRAC>::from_bits(self.to_bits().into());
                lhs.eq(rhs)
            }
        }

        impl<const LHS_FRAC: i32, const RHS_FRAC: i32> PartialOrd<$Wide<RHS_FRAC>>
            for $Narrow<LHS_FRAC>
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$Wide<RHS_FRAC>) -> Option<Ordering> {
                let lhs = $Widened::<LHS_FRAC>::from_bits(self.to_bits().into());
                lhs.partial_cmp(rhs)
            }

            #[inline]
            fn lt(&self, rhs: &$Wide<RHS_FRAC>) -> bool {
                let lhs = $Widened::<LHS_FRAC>::from_bits(self.to_bits().into());
                lhs.lt(rhs)
            }

            #[inline]
            fn le(&self, rhs: &$Wide<RHS_FRAC>) -> bool {
                let lhs = $Widened::<LHS_FRAC>::from_bits(self.to_bits().into());
                lhs.le(rhs)
            }

            #[inline]
            fn gt(&self, rhs: &$Wide<RHS_FRAC>) -> bool {
                let lhs = $Widened::<LHS_FRAC>::from_bits(self.to_bits().into());
                lhs.gt(rhs)
            }

            #[inline]
            fn ge(&self, rhs: &$Wide<RHS_FRAC>) -> bool {
                let lhs = $Widened::<LHS_FRAC>::from_bits(self.to_bits().into());
                lhs.ge(rhs)
            }
        }

        impl<const LHS_FRAC: i32, const RHS_FRAC: i32> PartialEq<$Narrow<RHS_FRAC>>
            for $Wide<LHS_FRAC>
        {
            #[inline]
            fn eq(&self, rhs: &$Narrow<RHS_FRAC>) -> bool {
                let rhs = $Widened::<RHS_FRAC>::from_bits(rhs.to_bits().into());
                self.eq(&rhs)
            }
        }

        impl<const LHS_FRAC: i32, const RHS_FRAC: i32> PartialOrd<$Narrow<RHS_FRAC>>
            for $Wide<LHS_FRAC>
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$Narrow<RHS_FRAC>) -> Option<Ordering> {
                let rhs = $Widened::<RHS_FRAC>::from_bits(rhs.to_bits().into());
                self.partial_cmp(&rhs)
            }

            #[inline]
            fn lt(&self, rhs: &$Narrow<RHS_FRAC>) -> bool {
                let rhs = $Widened::<RHS_FRAC>::from_bits(rhs.to_bits().into());
                self.lt(&rhs)
            }

            #[inline]
            fn le(&self, rhs: &$Narrow<RHS_FRAC>) -> bool {
                let rhs = $Widened::<RHS_FRAC>::from_bits(rhs.to_bits().into());
                self.le(&rhs)
            }

            #[inline]
            fn gt(&self, rhs: &$Narrow<RHS_FRAC>) -> bool {
                let rhs = $Widened::<RHS_FRAC>::from_bits(rhs.to_bits().into());
                self.gt(&rhs)
            }

            #[inline]
            fn ge(&self, rhs: &$Narrow<RHS_FRAC>) -> bool {
                let rhs = $Widened::<RHS_FRAC>::from_bits(rhs.to_bits().into());
                self.ge(&rhs)
            }
        }
    };
}

macro_rules! fixed_cmp_wider_cross {
    (
        $WideI:ident, $WideU:ident; $NarrowI:ident, $NarrowU:ident
    ) => {
        fixed_cmp_wider_instance! { $WideI; $NarrowI, $WideI }
        fixed_cmp_wider_instance! { $WideI; $NarrowU, $WideU }
        fixed_cmp_wider_instance! { $WideU; $NarrowI, $WideI }
        fixed_cmp_wider_instance! { $WideU; $NarrowU, $WideU }
    };
}

fixed_cmp_fixed_cross! { FixedI8(i8), FixedU8(u8), 8, rhs_shl_8 }
fixed_cmp_fixed_cross! { FixedI16(i16), FixedU16(u16), 16, rhs_shl_16 }
fixed_cmp_fixed_cross! { FixedI32(i32), FixedU32(u32), 32, rhs_shl_32 }
fixed_cmp_fixed_cross! { FixedI64(i64), FixedU64(u64), 64, rhs_shl_64 }
fixed_cmp_fixed_cross! { FixedI128(i128), FixedU128(u128), 128, rhs_shl_128 }

fixed_cmp_wider_cross! { FixedI16, FixedU16; FixedI8, FixedU8 }
fixed_cmp_wider_cross! { FixedI32, FixedU32; FixedI8, FixedU8 }
fixed_cmp_wider_cross! { FixedI32, FixedU32; FixedI16, FixedU16 }
fixed_cmp_wider_cross! { FixedI64, FixedU64; FixedI8, FixedU8 }
fixed_cmp_wider_cross! { FixedI64, FixedU64; FixedI16, FixedU16 }
fixed_cmp_wider_cross! { FixedI64, FixedU64; FixedI32, FixedU32 }
fixed_cmp_wider_cross! { FixedI128, FixedU128; FixedI8, FixedU8 }
fixed_cmp_wider_cross! { FixedI128, FixedU128; FixedI16, FixedU16 }
fixed_cmp_wider_cross! { FixedI128, FixedU128; FixedI32, FixedU32 }
fixed_cmp_wider_cross! { FixedI128, FixedU128; FixedI64, FixedU64 }

macro_rules! fixed_cmp_int {
    ($Fix:ident($nbits:expr), $Int:ident, $IntAs:ident, $IntFixed:ident) => {
        impl<const FRAC: i32> PartialEq<$Int> for $Fix<FRAC> {
            #[inline]
            fn eq(&self, rhs: &$Int) -> bool {
                let rhs = $IntFixed::<0>::from_bits(*rhs as $IntAs);
                self.eq(&rhs)
            }
        }

        impl<const FRAC: i32> PartialEq<$Fix<FRAC>> for $Int {
            #[inline]
            fn eq(&self, rhs: &$Fix<FRAC>) -> bool {
                let slf = $IntFixed::<0>::from_bits(*self as $IntAs);
                slf.eq(rhs)
            }
        }

        impl<const FRAC: i32> PartialOrd<$Int> for $Fix<FRAC> {
            #[inline]
            fn partial_cmp(&self, rhs: &$Int) -> Option<Ordering> {
                let rhs = $IntFixed::<0>::from_bits(*rhs as $IntAs);
                self.partial_cmp(&rhs)
            }

            #[inline]
            fn lt(&self, rhs: &$Int) -> bool {
                let rhs = $IntFixed::<0>::from_bits(*rhs as $IntAs);
                self.lt(&rhs)
            }

            #[inline]
            fn le(&self, rhs: &$Int) -> bool {
                let rhs = $IntFixed::<0>::from_bits(*rhs as $IntAs);
                self.le(&rhs)
            }

            #[inline]
            fn gt(&self, rhs: &$Int) -> bool {
                let rhs = $IntFixed::<0>::from_bits(*rhs as $IntAs);
                self.gt(&rhs)
            }

            #[inline]
            fn ge(&self, rhs: &$Int) -> bool {
                let rhs = $IntFixed::<0>::from_bits(*rhs as $IntAs);
                self.ge(&rhs)
            }
        }

        impl<const FRAC: i32> PartialOrd<$Fix<FRAC>> for $Int {
            #[inline]
            fn partial_cmp(&self, rhs: &$Fix<FRAC>) -> Option<Ordering> {
                let slf = $IntFixed::<0>::from_bits(*self as $IntAs);
                slf.partial_cmp(rhs)
            }

            #[inline]
            fn lt(&self, rhs: &$Fix<FRAC>) -> bool {
                let slf = $IntFixed::<0>::from_bits(*self as $IntAs);
                slf.lt(rhs)
            }

            #[inline]
            fn le(&self, rhs: &$Fix<FRAC>) -> bool {
                let slf = $IntFixed::<0>::from_bits(*self as $IntAs);
                slf.le(rhs)
            }

            #[inline]
            fn gt(&self, rhs: &$Fix<FRAC>) -> bool {
                let slf = $IntFixed::<0>::from_bits(*self as $IntAs);
                slf.gt(rhs)
            }

            #[inline]
            fn ge(&self, rhs: &$Fix<FRAC>) -> bool {
                let slf = $IntFixed::<0>::from_bits(*self as $IntAs);
                slf.ge(rhs)
            }
        }
    };
}

// Zero must NOT be neg
struct Value<U> {
    neg: bool,
    abs: U,
    bits: u32,
    frac_bits: i32,
}

#[inline]
// lhs_frac >= rhs_frac
fn float_rhs_shl<U>(rhs_abs: U, bits: u32, lhs_frac: i32, rhs_frac: i32) -> Option<U>
where
    U: Copy + Eq + TryFrom<u32> + Shl<u32, Output = U> + Shr<u32, Output = U>,
{
    debug_assert!(lhs_frac >= rhs_frac);
    let rhs_shl = lhs_frac.wrapping_sub(rhs_frac) as u32;
    let rhs_zero = match U::try_from(0u32) {
        Ok(zero) => zero,
        Err(_) => unreachable!(),
    };
    if rhs_abs == rhs_zero {
        Some(rhs_zero)
    } else if rhs_shl >= bits {
        None
    } else {
        let shifted = rhs_abs << rhs_shl;
        if (shifted >> rhs_shl) == rhs_abs {
            Some(shifted)
        } else {
            None
        }
    }
}

#[inline]
fn float_eq_even<U>(lhs: Value<U>, rhs: Value<U>) -> bool
where
    U: Copy + Eq + TryFrom<u32> + Shl<u32, Output = U> + Shr<u32, Output = U>,
{
    if lhs.frac_bits < rhs.frac_bits {
        return float_eq_even(rhs, lhs);
    }

    if lhs.neg != rhs.neg {
        return false;
    }

    // lhs.frac_bits >= rhs.frac_bits
    match float_rhs_shl(rhs.abs, rhs.bits, lhs.frac_bits, rhs.frac_bits) {
        None => false,
        Some(shifted_rhs_abs) => lhs.abs == shifted_rhs_abs,
    }
}

#[inline]
fn float_eq<Lhs, Rhs>(lhs: Value<Lhs>, rhs: Value<Rhs>) -> bool
where
    Lhs: Copy + Eq + TryFrom<u32> + TryFrom<Rhs> + Shl<u32, Output = Lhs> + Shr<u32, Output = Lhs>,
    Rhs: Copy + Eq + TryFrom<u32> + TryFrom<Lhs> + Shl<u32, Output = Rhs> + Shr<u32, Output = Rhs>,
{
    if lhs.bits >= rhs.bits {
        let rhs_abs = match Lhs::try_from(rhs.abs) {
            Ok(abs) => abs,
            Err(_) => unreachable!(),
        };
        let rhs = Value {
            neg: rhs.neg,
            abs: rhs_abs,
            bits: lhs.bits,
            frac_bits: rhs.frac_bits,
        };
        float_eq_even(lhs, rhs)
    } else {
        let lhs_abs = match Rhs::try_from(lhs.abs) {
            Ok(abs) => abs,
            Err(_) => unreachable!(),
        };
        let lhs = Value {
            neg: lhs.neg,
            abs: lhs_abs,
            bits: rhs.bits,
            frac_bits: lhs.frac_bits,
        };
        float_eq_even(lhs, rhs)
    }
}

#[inline]
fn float_cmp_even<U>(lhs: Value<U>, rhs: Value<U>) -> Ordering
where
    U: Copy + Ord + TryFrom<u32> + Shl<u32, Output = U> + Shr<u32, Output = U>,
{
    if lhs.frac_bits < rhs.frac_bits {
        return float_cmp_even(rhs, lhs).reverse();
    }

    if !lhs.neg && rhs.neg {
        return Ordering::Greater;
    }
    if lhs.neg && !rhs.neg {
        return Ordering::Less;
    }

    match float_rhs_shl(rhs.abs, rhs.bits, lhs.frac_bits, rhs.frac_bits) {
        None => {
            // rhs is so large it doesn't fit
            if lhs.neg {
                // both lhs and rhs are negative, and rhs is even more negative
                Ordering::Greater
            } else {
                Ordering::Less
            }
        }
        Some(shifted_rhs_abs) => {
            if lhs.neg {
                // both lhs are negative, so reverse order
                shifted_rhs_abs.cmp(&lhs.abs)
            } else {
                lhs.abs.cmp(&shifted_rhs_abs)
            }
        }
    }
}

#[inline]
fn float_cmp<Lhs, Rhs>(lhs: Value<Lhs>, rhs: Value<Rhs>) -> Ordering
where
    Lhs: Copy + Ord + TryFrom<u32> + TryFrom<Rhs> + Shl<u32, Output = Lhs> + Shr<u32, Output = Lhs>,
    Rhs: Copy + Ord + TryFrom<u32> + TryFrom<Lhs> + Shl<u32, Output = Rhs> + Shr<u32, Output = Rhs>,
{
    if lhs.bits >= rhs.bits {
        let rhs_abs = match Lhs::try_from(rhs.abs) {
            Ok(abs) => abs,
            Err(_) => unreachable!(),
        };
        let rhs = Value {
            neg: rhs.neg,
            abs: rhs_abs,
            bits: lhs.bits,
            frac_bits: rhs.frac_bits,
        };
        float_cmp_even(lhs, rhs)
    } else {
        let lhs_abs = match Rhs::try_from(lhs.abs) {
            Ok(abs) => abs,
            Err(_) => unreachable!(),
        };
        let lhs = Value {
            neg: lhs.neg,
            abs: lhs_abs,
            bits: rhs.bits,
            frac_bits: lhs.frac_bits,
        };
        float_cmp_even(lhs, rhs)
    }
}

macro_rules! fixed_cmp_float {
    ($Fix:ident($nbits:expr, $Inner:ident), $Float:ident, $FloatBits:ident) => {
        impl<const FRAC: i32> PartialEq<$Float> for $Fix<FRAC> {
            #[inline]
            fn eq(&self, rhs: &$Float) -> bool {
                use float_helper::$Float::Kind;
                let (lhs_neg, lhs_abs) = int_helper::$Inner::neg_abs(self.to_bits());
                let lhs = Value {
                    neg: lhs_neg,
                    abs: lhs_abs,
                    bits: $Inner::BITS,
                    frac_bits: FRAC,
                };
                let (rhs_neg, rhs_abs, rhs_frac) = match float_helper::$Float::kind(*rhs) {
                    Kind::Finite {
                        neg,
                        abs,
                        frac_bits,
                    } => (neg, abs, frac_bits),
                    _ => return false,
                };
                let rhs = Value {
                    neg: rhs_neg,
                    abs: rhs_abs,
                    bits: $FloatBits::BITS,
                    frac_bits: rhs_frac,
                };

                float_eq(lhs, rhs)
            }
        }

        impl<const FRAC: i32> PartialEq<$Fix<FRAC>> for $Float {
            #[inline]
            fn eq(&self, rhs: &$Fix<FRAC>) -> bool {
                rhs.eq(self)
            }
        }

        impl<const FRAC: i32> PartialOrd<$Float> for $Fix<FRAC> {
            #[inline]
            fn partial_cmp(&self, rhs: &$Float) -> Option<Ordering> {
                use float_helper::$Float::Kind;
                let (lhs_neg, lhs_abs) = int_helper::$Inner::neg_abs(self.to_bits());
                let lhs = Value {
                    neg: lhs_neg,
                    abs: lhs_abs,
                    bits: $Inner::BITS,
                    frac_bits: FRAC,
                };
                let (rhs_neg, rhs_abs, rhs_frac) = match float_helper::$Float::kind(*rhs) {
                    Kind::Finite {
                        neg,
                        abs,
                        frac_bits,
                    } => (neg, abs, frac_bits),
                    Kind::Infinite { neg } => {
                        return if neg {
                            Some(Ordering::Greater)
                        } else {
                            Some(Ordering::Less)
                        };
                    }
                    Kind::NaN => return None,
                };
                let rhs = Value {
                    neg: rhs_neg,
                    abs: rhs_abs,
                    bits: $FloatBits::BITS,
                    frac_bits: rhs_frac,
                };

                Some(float_cmp(lhs, rhs))
            }
        }

        impl<const FRAC: i32> PartialOrd<$Fix<FRAC>> for $Float {
            #[inline]
            fn partial_cmp(&self, rhs: &$Fix<FRAC>) -> Option<Ordering> {
                rhs.partial_cmp(self).map(Ordering::reverse)
            }
        }
    };
}

macro_rules! fixed_cmp_prim {
    ($Fix:ident($nbits:expr, $Inner:ident)) => {
        impl<const FRAC: i32> Eq for $Fix<FRAC> {}

        impl<const FRAC: i32> Ord for $Fix<FRAC> {
            #[inline]
            fn cmp(&self, rhs: &$Fix<FRAC>) -> Ordering {
                self.to_bits().cmp(&rhs.to_bits())
            }
        }

        fixed_cmp_int! { $Fix($nbits), i8, i8, FixedI8 }
        fixed_cmp_int! { $Fix($nbits), i16, i16, FixedI16 }
        fixed_cmp_int! { $Fix($nbits), i32, i32, FixedI32 }
        fixed_cmp_int! { $Fix($nbits), i64, i64, FixedI64 }
        fixed_cmp_int! { $Fix($nbits), i128, i128, FixedI128 }
        #[cfg(target_pointer_width = "16")]
        fixed_cmp_int! { $Fix($nbits), isize, i16, FixedI16 }
        #[cfg(target_pointer_width = "32")]
        fixed_cmp_int! { $Fix($nbits), isize, i32, FixedI32 }
        #[cfg(target_pointer_width = "64")]
        fixed_cmp_int! { $Fix($nbits), isize, i64, FixedI64 }
        fixed_cmp_int! { $Fix($nbits), u8, u8, FixedU8 }
        fixed_cmp_int! { $Fix($nbits), u16, u16, FixedU16 }
        fixed_cmp_int! { $Fix($nbits), u32, u32, FixedU32 }
        fixed_cmp_int! { $Fix($nbits), u64, u64, FixedU64 }
        fixed_cmp_int! { $Fix($nbits), u128, u128, FixedU128 }
        #[cfg(target_pointer_width = "16")]
        fixed_cmp_int! { $Fix($nbits), usize, u16, FixedU16 }
        #[cfg(target_pointer_width = "32")]
        fixed_cmp_int! { $Fix($nbits), usize, u32, FixedU32 }
        #[cfg(target_pointer_width = "64")]
        fixed_cmp_int! { $Fix($nbits), usize, u64, FixedU64 }
        fixed_cmp_float! { $Fix($nbits, $Inner), f16, u16 }
        fixed_cmp_float! { $Fix($nbits, $Inner), bf16, u16 }
        fixed_cmp_float! { $Fix($nbits, $Inner), f32, u32 }
        fixed_cmp_float! { $Fix($nbits, $Inner), f64, u64 }
        fixed_cmp_float! { $Fix($nbits, $Inner), F128, u128 }
    };
}

fixed_cmp_prim! { FixedI8(8, i8) }
fixed_cmp_prim! { FixedI16(16, i16) }
fixed_cmp_prim! { FixedI32(32, i32) }
fixed_cmp_prim! { FixedI64(64, i64) }
fixed_cmp_prim! { FixedI128(128, i128) }
fixed_cmp_prim! { FixedU8(8, u8) }
fixed_cmp_prim! { FixedU16(16, u16) }
fixed_cmp_prim! { FixedU32(32, u32) }
fixed_cmp_prim! { FixedU64(64, u64) }
fixed_cmp_prim! { FixedU128(128, u128) }

#[cfg(test)]
mod tests {
    use crate::*;
    use core::cmp::Ordering;

    #[test]
    fn cmp_signed() {
        use core::cmp::Ordering::*;
        let neg1_16 = FixedI32::<16>::NEG_ONE;
        let neg1_20 = FixedI32::<20>::NEG_ONE;
        let mut a = neg1_16;
        let mut b = neg1_20;
        // a = ffff.0000 = -1, b = fff.00000 = -1
        assert!(a.eq(&b) && b.eq(&a));
        assert_eq!(a.partial_cmp(&b), Some(Equal));
        assert_eq!(b.partial_cmp(&a), Some(Equal));
        assert_eq!(a, -1i8);
        assert_eq!(b, -1i128);
        a >>= 16;
        b >>= 16;
        // a = ffff.ffff = -2^-16, b = fff.ffff0 = -2^-16
        assert!(a.eq(&b) && b.eq(&a));
        assert_eq!(a.partial_cmp(&b), Some(Equal));
        assert_eq!(b.partial_cmp(&a), Some(Equal));
        assert!(a < 0.0);
        assert_eq!(a.partial_cmp(&f32::INFINITY), Some(Less));
        assert!(a < f32::INFINITY);
        assert!(a != f32::INFINITY);
        assert_eq!(a.partial_cmp(&f32::NEG_INFINITY), Some(Greater));
        assert!(a > f32::NEG_INFINITY);
        assert_eq!(a, -(-16f32).exp2());
        assert!(a <= -(-16f32).exp2());
        assert!(a >= -(-16f32).exp2());
        assert!(a < (-16f32).exp2());
        assert_ne!(a, -0.75 * (-16f32).exp2());
        assert!(a < -0.75 * (-16f32).exp2());
        assert!(a <= -0.75 * (-16f32).exp2());
        assert!(a > -1.25 * (-16f32).exp2());
        assert!(a >= -1.25 * (-16f32).exp2());
        a >>= 1;
        b >>= 1;
        // a = ffff.ffff = -2^-16, b = fff.ffff8 = -2^-17
        assert!(a.ne(&b) && b.ne(&a));
        assert_eq!(a.partial_cmp(&b), Some(Less));
        assert_eq!(b.partial_cmp(&a), Some(Greater));
        a = neg1_16 << 11;
        b = neg1_20 << 11;
        // a = f800.0000 = -2^11, b = 800.00000 = -2^11
        assert!(a.eq(&b) && b.eq(&a));
        assert_eq!(a.partial_cmp(&b), Some(Equal));
        assert_eq!(b.partial_cmp(&a), Some(Equal));
        assert_eq!(a, -1i16 << 11);
        assert_eq!(b, -1i64 << 11);
        a <<= 1;
        b <<= 1;
        // a = f000.0000 = -2^-12, b = 000.00000 = 0
        assert!(a.ne(&b) && b.ne(&a));
        assert_eq!(a.partial_cmp(&b), Some(Less));
        assert_eq!(b.partial_cmp(&a), Some(Greater));
        assert!(a < 1u8);
        assert_eq!(b, 0);
    }

    #[test]
    fn cmp_unsigned() {
        use core::cmp::Ordering::*;
        let one_16 = FixedU32::<16>::ONE;
        let one_20 = FixedU32::<20>::ONE;
        let mut a = one_16;
        let mut b = one_20;
        // a = 0001.0000 = 1, b = 001.00000 = 1
        assert!(a.eq(&b) && b.eq(&a));
        assert_eq!(a.partial_cmp(&b), Some(Equal));
        assert_eq!(b.partial_cmp(&a), Some(Equal));
        assert_eq!(a, 1u8);
        assert_eq!(b, 1i128);
        a >>= 16;
        b >>= 16;
        // a = 0000.0001 = 2^-16, b = 000.00010 = 2^-16
        assert!(a.eq(&b) && b.eq(&a));
        assert_eq!(a.partial_cmp(&b), Some(Equal));
        assert_eq!(b.partial_cmp(&a), Some(Equal));
        assert!(a > 0.0);
        assert_eq!(a.partial_cmp(&f32::INFINITY), Some(Less));
        assert!(a < f32::INFINITY);
        assert!(a != f32::INFINITY);
        assert_eq!(a.partial_cmp(&f32::NEG_INFINITY), Some(Greater));
        assert!(a > f32::NEG_INFINITY);
        assert_eq!(a, (-16f64).exp2());
        assert!(a <= (-16f64).exp2());
        assert!(a >= (-16f64).exp2());
        assert!(a > -(-16f64).exp2());
        assert_ne!(a, 0.75 * (-16f64).exp2());
        assert!(a > 0.75 * (-16f64).exp2());
        assert!(a >= 0.75 * (-16f64).exp2());
        assert!(a < 1.25 * (-16f64).exp2());
        assert!(a <= 1.25 * (-16f64).exp2());
        a >>= 1;
        b >>= 1;
        // a = 0000.0000 = 0, b = 000.00008 = 2^-17
        assert!(a.ne(&b) && b.ne(&a));
        assert_eq!(a.partial_cmp(&b), Some(Less));
        assert_eq!(b.partial_cmp(&a), Some(Greater));
        a = one_16 << 11;
        b = one_20 << 11;
        // a = 0800.0000 = 2^11, b = 800.00000 = 2^11
        assert!(a.eq(&b) && b.eq(&a));
        assert_eq!(a.partial_cmp(&b), Some(Equal));
        assert_eq!(b.partial_cmp(&a), Some(Equal));
        assert_eq!(a, 1i16 << 11);
        assert_eq!(b, 1u64 << 11);
        a <<= 1;
        b <<= 1;
        // a = 1000.0000 = 2^12, b = 000.00000 = 0
        assert!(a.ne(&b) && b.ne(&a));
        assert_eq!(a.partial_cmp(&b), Some(Greater));
        assert_eq!(b.partial_cmp(&a), Some(Less));
        assert!(a > -1i8);
        assert_eq!(a, 1i32 << 12);
        assert_eq!(b, 0);
    }

    #[test]
    fn cmp_i0() {
        use crate::types::*;
        assert_eq!(I0F32::checked_from_num(0.5), None);
        for &float in &[-0.5, -0.25, 0., 0.25, 0.49] {
            let fixed = I0F32::from_num(float);
            let half = U0F32::from_num(0.5);
            assert_eq!(fixed < half, float < 0.5, "{} < {}", fixed, half);
            assert_eq!(fixed == half, float == 0.5, "{} == {}", fixed, half);
            assert_eq!(fixed > half, float > 0.5, "{} > {}", fixed, half);
            assert_eq!(
                fixed.partial_cmp(&half),
                float.partial_cmp(&0.5),
                "{}.partial_cmp(&{})",
                fixed,
                half
            );
            assert_eq!(half < fixed, fixed > half);
            assert_eq!(half == fixed, fixed == half);
            assert_eq!(half > fixed, fixed < half);
            assert_eq!(
                half.partial_cmp(&fixed),
                fixed.partial_cmp(&half).map(Ordering::reverse)
            );

            let half = I1F31::from_num(0.5);
            assert_eq!(fixed < half, float < 0.5, "{} < {}", fixed, half);
            assert_eq!(fixed == half, float == 0.5, "{} == {}", fixed, half);
            assert_eq!(fixed > half, float > 0.5, "{} > {}", fixed, half);
            assert_eq!(
                fixed.partial_cmp(&half),
                float.partial_cmp(&0.5),
                "{}.partial_cmp(&{})",
                fixed,
                half
            );
            assert_eq!(half < fixed, fixed > half);
            assert_eq!(half == fixed, fixed == half);
            assert_eq!(half > fixed, fixed < half);
            assert_eq!(
                half.partial_cmp(&fixed),
                fixed.partial_cmp(&half).map(Ordering::reverse)
            );

            let half = 0.5f32;
            assert_eq!(fixed < half, float < 0.5, "{} < {}", fixed, half);
            assert_eq!(fixed == half, float == 0.5, "{} == {}", fixed, half);
            assert_eq!(fixed > half, float > 0.5, "{} > {}", fixed, half);
            assert_eq!(
                fixed.partial_cmp(&half),
                float.partial_cmp(&0.5),
                "{}.partial_cmp(&{})",
                fixed,
                half
            );
            assert_eq!(half < fixed, fixed > half);
            assert_eq!(half == fixed, fixed == half);
            assert_eq!(half > fixed, fixed < half);
            assert_eq!(
                half.partial_cmp(&fixed),
                fixed.partial_cmp(&half).map(Ordering::reverse)
            );

            let m1 = I1F31::from_num(-1.0);
            assert_eq!(fixed < m1, float < -1.0, "{} < {}", fixed, m1);
            assert_eq!(fixed == m1, float == -1.0, "{} == {}", fixed, m1);
            assert_eq!(fixed > m1, float > -1.0, "{} > {}", fixed, m1);
            assert_eq!(
                fixed.partial_cmp(&m1),
                float.partial_cmp(&-1.0),
                "{}.partial_cmp(&{})",
                fixed,
                m1
            );
            assert_eq!(m1 < fixed, fixed > m1);
            assert_eq!(m1 == fixed, fixed == m1);
            assert_eq!(m1 > fixed, fixed < m1);
            assert_eq!(
                m1.partial_cmp(&fixed),
                fixed.partial_cmp(&m1).map(Ordering::reverse)
            );

            let m1 = -1.0f32;
            assert_eq!(fixed < m1, float < -1.0, "{} < {}", fixed, m1);
            assert_eq!(fixed == m1, float == -1.0, "{} == {}", fixed, m1);
            assert_eq!(fixed > m1, float > -1.0, "{} > {}", fixed, m1);
            assert_eq!(
                fixed.partial_cmp(&m1),
                float.partial_cmp(&-1.0),
                "{}.partial_cmp(&{})",
                fixed,
                m1
            );
            assert_eq!(m1 < fixed, fixed > m1);
            assert_eq!(m1 == fixed, fixed == m1);
            assert_eq!(m1 > fixed, fixed < m1);
            assert_eq!(
                m1.partial_cmp(&fixed),
                fixed.partial_cmp(&m1).map(Ordering::reverse)
            );

            let mhalf = I1F31::from_num(-0.5);
            assert_eq!(fixed < mhalf, float < -0.5, "{} < {}", fixed, mhalf);
            assert_eq!(fixed == mhalf, float == -0.5, "{} == {}", fixed, mhalf);
            assert_eq!(fixed > mhalf, float > -0.5, "{} > {}", fixed, mhalf);
            assert_eq!(
                fixed.partial_cmp(&mhalf),
                float.partial_cmp(&-0.5),
                "{}.partial_cmp(&{})",
                fixed,
                mhalf
            );
            assert_eq!(mhalf < fixed, fixed > mhalf);
            assert_eq!(mhalf == fixed, fixed == mhalf);
            assert_eq!(mhalf > fixed, fixed < mhalf);
            assert_eq!(
                mhalf.partial_cmp(&fixed),
                fixed.partial_cmp(&mhalf).map(Ordering::reverse)
            );

            let mhalf = -0.5f32;
            assert_eq!(fixed < mhalf, float < -0.5, "{} < {}", fixed, mhalf);
            assert_eq!(fixed == mhalf, float == -0.5, "{} == {}", fixed, mhalf);
            assert_eq!(fixed > mhalf, float > -0.5, "{} > {}", fixed, mhalf);
            assert_eq!(
                fixed.partial_cmp(&mhalf),
                float.partial_cmp(&-0.5),
                "{}.partial_cmp(&{})",
                fixed,
                mhalf
            );
            assert_eq!(mhalf < fixed, fixed > mhalf);
            assert_eq!(mhalf == fixed, fixed == mhalf);
            assert_eq!(mhalf > fixed, fixed < mhalf);
            assert_eq!(
                mhalf.partial_cmp(&fixed),
                fixed.partial_cmp(&mhalf).map(Ordering::reverse)
            );
        }
    }
}
