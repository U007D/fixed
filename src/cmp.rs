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
    float_helper,
    helpers::{FloatKind, Widest},
    int_helper,
    types::extra::{If, True},
    F128Bits, FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32,
    FixedU64, FixedU8,
};
use core::cmp::Ordering;
use half::{bf16, f16};

macro_rules! fixed_cmp_fixed {
    (
        $Lhs:ident($nbits_lhs:expr, $LhsInner:ident),
        $Rhs:ident($nbits_rhs:expr, $RhsInner:ident)
    ) => {
        impl<const LHS_FRAC: i32, const RHS_FRAC: i32> PartialEq<$Rhs<RHS_FRAC>> for $Lhs<LHS_FRAC>
        where
            If<{ (0 <= LHS_FRAC) & (LHS_FRAC <= $nbits_lhs) }>: True,
            If<{ (0 <= RHS_FRAC) & (RHS_FRAC <= $nbits_rhs) }>: True,
        {
            #[inline]
            fn eq(&self, rhs: &$Rhs<RHS_FRAC>) -> bool {
                let conv = int_helper::$RhsInner::to_fixed_helper(
                    rhs.to_bits(),
                    <$Rhs<RHS_FRAC>>::FRAC_NBITS as i32,
                    Self::FRAC_NBITS,
                    Self::INT_NBITS,
                );
                let (rhs_is_neg, rhs_bits) = match conv.bits {
                    Widest::Unsigned(bits) => (false, bits as $LhsInner),
                    Widest::Negative(bits) => (true, bits as $LhsInner),
                };
                conv.dir == Ordering::Equal
                    && !conv.overflow
                    && rhs_is_neg == int_helper::$LhsInner::is_negative(rhs_bits)
                    && rhs_bits == self.to_bits()
            }
        }

        impl<const LHS_FRAC: i32, const RHS_FRAC: i32> PartialOrd<$Rhs<RHS_FRAC>> for $Lhs<LHS_FRAC>
        where
            If<{ (0 <= LHS_FRAC) & (LHS_FRAC <= $nbits_lhs) }>: True,
            If<{ (0 <= RHS_FRAC) & (RHS_FRAC <= $nbits_rhs) }>: True,
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$Rhs<RHS_FRAC>) -> Option<Ordering> {
                let lhs_is_neg = int_helper::$LhsInner::is_negative(self.to_bits());
                let rhs_is_neg = int_helper::$RhsInner::is_negative(rhs.to_bits());
                match (lhs_is_neg, rhs_is_neg) {
                    (false, true) => return Some(Ordering::Greater),
                    (true, false) => return Some(Ordering::Less),
                    _ => {}
                }
                let conv = int_helper::$RhsInner::to_fixed_helper(
                    rhs.to_bits(),
                    <$Rhs<RHS_FRAC>>::FRAC_NBITS as i32,
                    Self::FRAC_NBITS,
                    Self::INT_NBITS,
                );
                let rhs_bits = match conv.bits {
                    Widest::Unsigned(bits) => bits as $LhsInner,
                    Widest::Negative(bits) => bits as $LhsInner,
                };
                if conv.overflow || int_helper::$LhsInner::is_negative(rhs_bits) != rhs_is_neg {
                    return if rhs_is_neg {
                        Some(Ordering::Greater)
                    } else {
                        Some(Ordering::Less)
                    };
                }
                Some(self.to_bits().cmp(&rhs_bits).then(conv.dir))
            }

            #[inline]
            fn lt(&self, rhs: &$Rhs<RHS_FRAC>) -> bool {
                let lhs_is_neg = int_helper::$LhsInner::is_negative(self.to_bits());
                let rhs_is_neg = int_helper::$RhsInner::is_negative(rhs.to_bits());
                match (lhs_is_neg, rhs_is_neg) {
                    (false, true) => return false,
                    (true, false) => return true,
                    _ => {}
                }
                let conv = int_helper::$RhsInner::to_fixed_helper(
                    rhs.to_bits(),
                    <$Rhs<RHS_FRAC>>::FRAC_NBITS as i32,
                    Self::FRAC_NBITS,
                    Self::INT_NBITS,
                );
                let rhs_bits = match conv.bits {
                    Widest::Unsigned(bits) => bits as $LhsInner,
                    Widest::Negative(bits) => bits as $LhsInner,
                };
                if conv.overflow || int_helper::$LhsInner::is_negative(rhs_bits) != rhs_is_neg {
                    return !rhs_is_neg;
                }
                let lhs_bits = self.to_bits();
                lhs_bits < rhs_bits || (lhs_bits == rhs_bits && conv.dir == Ordering::Less)
            }

            #[inline]
            fn le(&self, rhs: &$Rhs<RHS_FRAC>) -> bool {
                !rhs.lt(self)
            }

            #[inline]
            fn gt(&self, rhs: &$Rhs<RHS_FRAC>) -> bool {
                rhs.lt(self)
            }

            #[inline]
            fn ge(&self, rhs: &$Rhs<RHS_FRAC>) -> bool {
                !self.lt(rhs)
            }
        }
    };
}

macro_rules! fixed_cmp_int {
    ($Fix:ident($nbits:expr), $Int:ident, $IntAs:ident, $IntFixed:ident) => {
        impl<const FRAC: i32> PartialEq<$Int> for $Fix<FRAC>
        where
            If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True,
        {
            #[inline]
            fn eq(&self, rhs: &$Int) -> bool {
                let rhs = $IntFixed::<0>::from_bits(*rhs as $IntAs);
                self.eq(&rhs)
            }
        }

        // TODO: blocked on https://github.com/rust-lang/rust/issues/94282
        // impl<const FRAC: i32> PartialEq<$Fix<FRAC>> for $Int
        // where
        //     If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True,
        // {
        //     #[inline]
        //     fn eq(&self, rhs: &$Fix<FRAC>) -> bool {
        //         let slf = $IntFixed::<0>::from_bits(*self as $IntAs);
        //         slf.eq(rhs)
        //     }
        // }

        impl<const FRAC: i32> PartialOrd<$Int> for $Fix<FRAC>
        where
            If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True,
        {
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

        // TODO: blocked on https://github.com/rust-lang/rust/issues/94282
        // impl<const FRAC: i32> PartialOrd<$Fix<FRAC>> for $Int
        // where
        //     If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True,
        // {
        //     #[inline]
        //     fn partial_cmp(&self, rhs: &$Fix<FRAC>) -> Option<Ordering> {
        //         let slf = $IntFixed::<0>::from_bits(*self as $IntAs);
        //         slf.partial_cmp(rhs)
        //     }

        //     #[inline]
        //     fn lt(&self, rhs: &$Fix<FRAC>) -> bool {
        //         let slf = $IntFixed::<0>::from_bits(*self as $IntAs);
        //         slf.lt(rhs)
        //     }

        //     #[inline]
        //     fn le(&self, rhs: &$Fix<FRAC>) -> bool {
        //         let slf = $IntFixed::<0>::from_bits(*self as $IntAs);
        //         slf.le(rhs)
        //     }

        //     #[inline]
        //     fn gt(&self, rhs: &$Fix<FRAC>) -> bool {
        //         let slf = $IntFixed::<0>::from_bits(*self as $IntAs);
        //         slf.gt(rhs)
        //     }

        //     #[inline]
        //     fn ge(&self, rhs: &$Fix<FRAC>) -> bool {
        //         let slf = $IntFixed::<0>::from_bits(*self as $IntAs);
        //         slf.ge(rhs)
        //     }
        // }
    };
}

macro_rules! fixed_cmp_float {
    ($Fix:ident($nbits:expr, $Inner:ident), $Float:ident) => {
        impl<const FRAC: i32> PartialEq<$Float> for $Fix<FRAC>
        where
            If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True,
        {
            #[inline]
            fn eq(&self, rhs: &$Float) -> bool {
                let kind =
                    float_helper::$Float::to_float_kind(*rhs, Self::FRAC_NBITS, Self::INT_NBITS);
                let conv = match kind {
                    FloatKind::Finite { conv, .. } => conv,
                    _ => return false,
                };
                let (rhs_is_neg, rhs_bits) = match conv.bits {
                    Widest::Unsigned(bits) => (false, bits as $Inner),
                    Widest::Negative(bits) => (true, bits as $Inner),
                };
                conv.dir == Ordering::Equal
                    && !conv.overflow
                    && rhs_is_neg == int_helper::$Inner::is_negative(rhs_bits)
                    && rhs_bits == self.to_bits()
            }
        }

        impl<const FRAC: i32> PartialEq<$Fix<FRAC>> for $Float
        where
            If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True,
        {
            #[inline]
            fn eq(&self, rhs: &$Fix<FRAC>) -> bool {
                rhs.eq(self)
            }
        }

        impl<const FRAC: i32> PartialOrd<$Float> for $Fix<FRAC>
        where
            If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True,
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$Float) -> Option<Ordering> {
                let lhs_is_neg = int_helper::$Inner::is_negative(self.to_bits());
                let kind =
                    float_helper::$Float::to_float_kind(*rhs, Self::FRAC_NBITS, Self::INT_NBITS);
                let (rhs_is_neg, conv) = match kind {
                    FloatKind::NaN => return None,
                    FloatKind::Infinite { neg } => {
                        return if neg {
                            Some(Ordering::Greater)
                        } else {
                            Some(Ordering::Less)
                        };
                    }
                    FloatKind::Finite { neg, conv } => (neg, conv),
                };
                match (lhs_is_neg, rhs_is_neg) {
                    (false, true) => return Some(Ordering::Greater),
                    (true, false) => return Some(Ordering::Less),
                    _ => {}
                }
                let rhs_bits = match conv.bits {
                    Widest::Unsigned(bits) => bits as $Inner,
                    Widest::Negative(bits) => bits as $Inner,
                };
                if conv.overflow || int_helper::$Inner::is_negative(rhs_bits) != rhs_is_neg {
                    return if rhs_is_neg {
                        Some(Ordering::Greater)
                    } else {
                        Some(Ordering::Less)
                    };
                }
                Some(self.to_bits().cmp(&rhs_bits).then(conv.dir))
            }

            #[inline]
            fn lt(&self, rhs: &$Float) -> bool {
                let lhs_is_neg = int_helper::$Inner::is_negative(self.to_bits());
                let kind =
                    float_helper::$Float::to_float_kind(*rhs, Self::FRAC_NBITS, Self::INT_NBITS);
                let (rhs_is_neg, conv) = match kind {
                    FloatKind::NaN => return false,
                    FloatKind::Infinite { neg } => return !neg,
                    FloatKind::Finite { neg, conv } => (neg, conv),
                };

                match (lhs_is_neg, rhs_is_neg) {
                    (false, true) => return false,
                    (true, false) => return true,
                    _ => {}
                }
                let rhs_bits = match conv.bits {
                    Widest::Unsigned(bits) => bits as $Inner,
                    Widest::Negative(bits) => bits as $Inner,
                };
                if conv.overflow || int_helper::$Inner::is_negative(rhs_bits) != rhs_is_neg {
                    return !rhs_is_neg;
                }
                let lhs_bits = self.to_bits();
                lhs_bits < rhs_bits || (lhs_bits == rhs_bits && conv.dir == Ordering::Less)
            }

            #[inline]
            fn le(&self, rhs: &$Float) -> bool {
                !rhs.is_nan() && !rhs.lt(self)
            }

            #[inline]
            fn gt(&self, rhs: &$Float) -> bool {
                rhs.lt(self)
            }

            #[inline]
            fn ge(&self, rhs: &$Float) -> bool {
                !rhs.is_nan() && !self.lt(rhs)
            }
        }

        impl<const FRAC: i32> PartialOrd<$Fix<FRAC>> for $Float
        where
            If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True,
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$Fix<FRAC>) -> Option<Ordering> {
                rhs.partial_cmp(self).map(Ordering::reverse)
            }

            #[inline]
            fn lt(&self, rhs: &$Fix<FRAC>) -> bool {
                let kind = float_helper::$Float::to_float_kind(
                    *self,
                    <$Fix<FRAC>>::FRAC_NBITS,
                    <$Fix<FRAC>>::INT_NBITS,
                );
                let (lhs_is_neg, conv) = match kind {
                    FloatKind::NaN => return false,
                    FloatKind::Infinite { neg } => return neg,
                    FloatKind::Finite { neg, conv } => (neg, conv),
                };
                let rhs_is_neg = int_helper::$Inner::is_negative(rhs.to_bits());
                match (lhs_is_neg, rhs_is_neg) {
                    (false, true) => return false,
                    (true, false) => return true,
                    _ => {}
                }
                let lhs_bits = match conv.bits {
                    Widest::Unsigned(bits) => bits as $Inner,
                    Widest::Negative(bits) => bits as $Inner,
                };
                if conv.overflow || int_helper::$Inner::is_negative(lhs_bits) != lhs_is_neg {
                    return lhs_is_neg;
                }
                let rhs_bits = rhs.to_bits();
                lhs_bits < rhs_bits || (lhs_bits == rhs_bits && conv.dir == Ordering::Greater)
            }

            #[inline]
            fn le(&self, rhs: &$Fix<FRAC>) -> bool {
                !self.is_nan() && !rhs.lt(self)
            }

            #[inline]
            fn gt(&self, rhs: &$Fix<FRAC>) -> bool {
                rhs.lt(self)
            }

            #[inline]
            fn ge(&self, rhs: &$Fix<FRAC>) -> bool {
                !self.is_nan() && !self.lt(rhs)
            }
        }
    };
}

macro_rules! fixed_cmp_all {
    ($Fix:ident($nbits:expr, $Inner:ident)) => {
        impl<const FRAC: i32> Eq for $Fix<FRAC> where If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True {}

        impl<const FRAC: i32> Ord for $Fix<FRAC>
        where
            If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True,
        {
            #[inline]
            fn cmp(&self, rhs: &$Fix<FRAC>) -> Ordering {
                self.to_bits().cmp(&rhs.to_bits())
            }
        }

        fixed_cmp_fixed! { $Fix($nbits, $Inner), FixedI8(8, i8) }
        fixed_cmp_fixed! { $Fix($nbits, $Inner), FixedI16(16, i16) }
        fixed_cmp_fixed! { $Fix($nbits, $Inner), FixedI32(32, i32) }
        fixed_cmp_fixed! { $Fix($nbits, $Inner), FixedI64(64, i64) }
        fixed_cmp_fixed! { $Fix($nbits, $Inner), FixedI128(128, i128) }
        fixed_cmp_fixed! { $Fix($nbits, $Inner), FixedU8(8, u8) }
        fixed_cmp_fixed! { $Fix($nbits, $Inner), FixedU16(16, u16) }
        fixed_cmp_fixed! { $Fix($nbits, $Inner), FixedU32(32, u32) }
        fixed_cmp_fixed! { $Fix($nbits, $Inner), FixedU64(64, u64) }
        fixed_cmp_fixed! { $Fix($nbits, $Inner), FixedU128(128, u128) }
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
        fixed_cmp_float! { $Fix($nbits, $Inner), f16 }
        fixed_cmp_float! { $Fix($nbits, $Inner), bf16 }
        fixed_cmp_float! { $Fix($nbits, $Inner), f32 }
        fixed_cmp_float! { $Fix($nbits, $Inner), f64 }
        fixed_cmp_float! { $Fix($nbits, $Inner), F128Bits }
    };
}

fixed_cmp_all! { FixedI8(8, i8) }
fixed_cmp_all! { FixedI16(16, i16) }
fixed_cmp_all! { FixedI32(32, i32) }
fixed_cmp_all! { FixedI64(64, i64) }
fixed_cmp_all! { FixedI128(128, i128) }
fixed_cmp_all! { FixedU8(8, u8) }
fixed_cmp_all! { FixedU16(16, u16) }
fixed_cmp_all! { FixedU32(32, u32) }
fixed_cmp_all! { FixedU64(64, u64) }
fixed_cmp_all! { FixedU128(128, u128) }

#[cfg(test)]
mod tests {
    use crate::*;
    use core::f32;

    #[test]
    fn cmp_signed() {
        use core::cmp::Ordering::*;
        let neg1_16 = FixedI32::<16>::from_num(-1);
        let neg1_20 = FixedI32::<20>::from_num(-1);
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
