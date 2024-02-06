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

use crate::{
    types::extra::{If, True},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
#[cfg(not(debug_assertions))]
use core::hint;
use core::{
    iter::{Product, Sum},
    num::{
        NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroU128, NonZeroU16,
        NonZeroU32, NonZeroU64, NonZeroU8,
    },
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div,
        DivAssign, Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
};

macro_rules! refs {
    (impl $Imp:ident for $Fixed:ident$(($nbits:expr))? { $method:ident }) => {
        impl<const FRAC: i32> $Imp<$Fixed<FRAC>> for &$Fixed<FRAC>
            $(where If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True)?
        {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn $method(self, rhs: $Fixed<FRAC>) -> $Fixed<FRAC> {
                (*self).$method(rhs)
            }
        }

        impl<const FRAC: i32> $Imp<&$Fixed<FRAC>> for $Fixed<FRAC>
            $(where If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True)?
        {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn $method(self, rhs: &$Fixed<FRAC>) -> $Fixed<FRAC> {
                self.$method(*rhs)
            }
        }

        impl<const FRAC: i32> $Imp<&$Fixed<FRAC>> for &$Fixed<FRAC>
            $(where If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True)?
        {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn $method(self, rhs: &$Fixed<FRAC>) -> $Fixed<FRAC> {
                (*self).$method(*rhs)
            }
        }
    };

    (impl $Imp:ident<$Inner:ty> for $Fixed:ident$(($nbits:expr))? { $method:ident }) => {
        impl<const FRAC: i32> $Imp<$Inner> for &$Fixed<FRAC>
            $(where If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True)?
        {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn $method(self, rhs: $Inner) -> $Fixed<FRAC> {
                (*self).$method(rhs)
            }
        }

        impl<const FRAC: i32> $Imp<&$Inner> for $Fixed<FRAC>
            $(where If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True)?
        {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn $method(self, rhs: &$Inner) -> $Fixed<FRAC> {
                self.$method(*rhs)
            }
        }

        impl<const FRAC: i32> $Imp<&$Inner> for &$Fixed<FRAC>
            $(where If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True)?
        {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn $method(self, rhs: &$Inner) -> $Fixed<FRAC> {
                (*self).$method(*rhs)
            }
        }
    };
}

macro_rules! refs_assign {
    (impl $Imp:ident for $Fixed:ident$(($nbits:expr))? { $method:ident }) => {
        impl<const FRAC: i32> $Imp<&$Fixed<FRAC>> for $Fixed<FRAC>
            $(where If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True)?
        {
            #[inline]
            fn $method(&mut self, rhs: &$Fixed<FRAC>) {
                self.$method(*rhs);
            }
        }
    };

    (impl $Imp:ident<$Inner:ty> for $Fixed:ident$(($nbits:expr))? { $method:ident }) => {
        impl<const FRAC: i32> $Imp<&$Inner> for $Fixed<FRAC>
            $(where If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True)?
        {
            #[inline]
            fn $method(&mut self, rhs: &$Inner) {
                self.$method(*rhs);
            }
        }
    };
}

macro_rules! pass {
    (impl $Imp:ident for $Fixed:ident { $method:ident }) => {
        impl<const FRAC: i32> $Imp<$Fixed<FRAC>> for $Fixed<FRAC> {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn $method(self, rhs: $Fixed<FRAC>) -> $Fixed<FRAC> {
                Self::from_bits(self.to_bits().$method(rhs.to_bits()))
            }
        }

        refs! { impl $Imp for $Fixed { $method } }
    };
}

macro_rules! pass_assign {
    (impl $Imp:ident for $Fixed:ident { $method:ident }) => {
        impl<const FRAC: i32> $Imp<$Fixed<FRAC>> for $Fixed<FRAC> {
            #[inline]
            fn $method(&mut self, rhs: $Fixed<FRAC>) {
                self.bits.$method(rhs.to_bits())
            }
        }

        refs_assign! { impl $Imp for $Fixed { $method } }
    };
}

macro_rules! pass_one {
    (impl $Imp:ident for $Fixed:ident { $method:ident }) => {
        impl<const FRAC: i32> $Imp for $Fixed<FRAC> {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn $method(self) -> $Fixed<FRAC> {
                Self::from_bits(self.to_bits().$method())
            }
        }

        impl<const FRAC: i32> $Imp for &$Fixed<FRAC> {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn $method(self) -> $Fixed<FRAC> {
                (*self).$method()
            }
        }
    };
}

macro_rules! shift {
    (impl $Imp:ident < $Rhs:ty > for $Fixed:ident { $method:ident }) => {
        impl<const FRAC: i32> $Imp<$Rhs> for $Fixed<FRAC> {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn $method(self, rhs: $Rhs) -> $Fixed<FRAC> {
                $Fixed::from_bits(self.to_bits().$method(rhs))
            }
        }

        impl<const FRAC: i32> $Imp<$Rhs> for &$Fixed<FRAC> {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn $method(self, rhs: $Rhs) -> $Fixed<FRAC> {
                (*self).$method(rhs)
            }
        }

        impl<const FRAC: i32> $Imp<&$Rhs> for $Fixed<FRAC> {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn $method(self, rhs: &$Rhs) -> $Fixed<FRAC> {
                self.$method(*rhs)
            }
        }

        impl<const FRAC: i32> $Imp<&$Rhs> for &$Fixed<FRAC> {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn $method(self, rhs: &$Rhs) -> $Fixed<FRAC> {
                (*self).$method(*rhs)
            }
        }
    };
}

macro_rules! shift_assign {
    (impl $Imp:ident < $Rhs:ty > for $Fixed:ident { $method:ident }) => {
        impl<const FRAC: i32> $Imp<$Rhs> for $Fixed<FRAC> {
            #[inline]
            fn $method(&mut self, rhs: $Rhs) {
                self.bits.$method(rhs)
            }
        }

        impl<const FRAC: i32> $Imp<&$Rhs> for $Fixed<FRAC> {
            #[inline]
            fn $method(&mut self, rhs: &$Rhs) {
                self.$method(*rhs)
            }
        }
    };
}

macro_rules! shift_all {
    (
        impl {$Imp:ident, $ImpAssign:ident}<{ $($Rhs:ty),* }> for $Fixed:ident
        { $method:ident, $method_assign:ident }
    ) => { $(
        shift! { impl $Imp<$Rhs> for $Fixed { $method } }
        shift_assign! { impl $ImpAssign<$Rhs> for $Fixed { $method_assign } }
    )* };
}

macro_rules! fixed_arith {
    (
        $Fixed:ident($Inner:ident, $nbits:expr, $NonZeroInner:ident),
        $Signedness:tt
    ) => {
        if_signed! {
            $Signedness;
            pass_one! { impl Neg for $Fixed { neg } }
        }

        pass! { impl Add for $Fixed { add } }
        pass_assign! { impl AddAssign for $Fixed { add_assign } }
        pass! { impl Sub for $Fixed { sub } }
        pass_assign! { impl SubAssign for $Fixed { sub_assign } }

        impl<const FRAC: i32> Mul<$Fixed<FRAC>> for $Fixed<FRAC> {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn mul(self, rhs: $Fixed<FRAC>) -> $Fixed<FRAC> {
                let (ans, overflow) = $Inner::overflowing_mul(self.to_bits(), rhs.to_bits(), FRAC);
                debug_assert!(!overflow, "overflow");
                Self::from_bits(ans)
            }
        }

        refs! { impl Mul for $Fixed { mul } }

        impl<const FRAC: i32, const RHS_FRAC: i32> MulAssign<$Fixed<RHS_FRAC>> for $Fixed<FRAC> {
            #[inline]
            fn mul_assign(&mut self, rhs: $Fixed<RHS_FRAC>) {
                let (ans, overflow) =
                    $Inner::overflowing_mul(self.to_bits(), rhs.to_bits(), RHS_FRAC);
                debug_assert!(!overflow, "overflow");
                *self = Self::from_bits(ans);
            }
        }

        impl<const FRAC: i32, const RHS_FRAC: i32> MulAssign<&$Fixed<RHS_FRAC>> for $Fixed<FRAC> {
            #[inline]
            fn mul_assign(&mut self, rhs: &$Fixed<RHS_FRAC>) {
                let (ans, overflow) =
                    $Inner::overflowing_mul(self.to_bits(), rhs.to_bits(), RHS_FRAC);
                debug_assert!(!overflow, "overflow");
                *self = Self::from_bits(ans);
            }
        }

        impl<const FRAC: i32> Div<$Fixed<FRAC>> for $Fixed<FRAC>
        where
            If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True,
        {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn div(self, rhs: $Fixed<FRAC>) -> $Fixed<FRAC> {
                let (ans, overflow) =
                    $Inner::overflowing_div(self.to_bits(), rhs.to_bits(), FRAC as u32);
                debug_assert!(!overflow, "overflow");
                Self::from_bits(ans)
            }
        }

        refs! { impl Div for $Fixed($nbits) { div } }

        impl<const FRAC: i32> DivAssign<$Fixed<FRAC>> for $Fixed<FRAC>
        where
            If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True,
        {
            #[inline]
            fn div_assign(&mut self, rhs: $Fixed<FRAC>) {
                *self = (*self).div(rhs)
            }
        }

        refs_assign! { impl DivAssign for $Fixed($nbits) { div_assign } }

        // do not pass! { Rem }, as I::MIN % I::from(-1) should return 0, not panic
        impl<const FRAC: i32> Rem<$Fixed<FRAC>> for $Fixed<FRAC> {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn rem(self, rhs: $Fixed<FRAC>) -> $Fixed<FRAC> {
                self.checked_rem(rhs).expect("division by zero")
            }
        }

        refs! { impl Rem for $Fixed { rem } }

        impl<const FRAC: i32> RemAssign<$Fixed<FRAC>> for $Fixed<FRAC> {
            #[inline]
            fn rem_assign(&mut self, rhs: $Fixed<FRAC>) {
                *self = (*self).rem(rhs)
            }
        }

        refs_assign! { impl RemAssign for $Fixed { rem_assign } }

        pass_one! { impl Not for $Fixed { not } }
        pass! { impl BitAnd for $Fixed { bitand } }
        pass_assign! { impl BitAndAssign for $Fixed { bitand_assign } }
        pass! { impl BitOr for $Fixed { bitor } }
        pass_assign! { impl BitOrAssign for $Fixed { bitor_assign } }
        pass! { impl BitXor for $Fixed { bitxor } }
        pass_assign! { impl BitXorAssign for $Fixed { bitxor_assign } }

        impl<const FRAC: i32> Mul<$Inner> for $Fixed<FRAC> {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn mul(self, rhs: $Inner) -> $Fixed<FRAC> {
                Self::from_bits(self.to_bits().mul(rhs))
            }
        }

        refs! { impl Mul<$Inner> for $Fixed { mul } }

        impl<const FRAC: i32> MulAssign<$Inner> for $Fixed<FRAC> {
            #[inline]
            fn mul_assign(&mut self, rhs: $Inner) {
                *self = (*self).mul(rhs);
            }
        }

        refs_assign! { impl MulAssign<$Inner> for $Fixed { mul_assign } }

        impl<const FRAC: i32> Mul<$Fixed<FRAC>> for $Inner {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn mul(self, rhs: $Fixed<FRAC>) -> $Fixed<FRAC> {
                rhs.mul(self)
            }
        }

        impl<const FRAC: i32> Mul<&$Fixed<FRAC>> for $Inner {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn mul(self, rhs: &$Fixed<FRAC>) -> $Fixed<FRAC> {
                (*rhs).mul(self)
            }
        }

        impl<const FRAC: i32> Mul<$Fixed<FRAC>> for &$Inner {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn mul(self, rhs: $Fixed<FRAC>) -> $Fixed<FRAC> {
                rhs.mul(*self)
            }
        }

        impl<const FRAC: i32> Mul<&$Fixed<FRAC>> for &$Inner {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn mul(self, rhs: &$Fixed<FRAC>) -> $Fixed<FRAC> {
                (*rhs).mul(*self)
            }
        }

        impl<const FRAC: i32> Div<$Inner> for $Fixed<FRAC> {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn div(self, rhs: $Inner) -> $Fixed<FRAC> {
                Self::from_bits(self.to_bits().div(rhs))
            }
        }

        refs! { impl Div<$Inner> for $Fixed { div } }

        impl<const FRAC: i32> DivAssign<$Inner> for $Fixed<FRAC> {
            #[inline]
            fn div_assign(&mut self, rhs: $Inner) {
                *self = (*self).div(rhs);
            }
        }

        refs_assign! { impl DivAssign<$Inner> for $Fixed { div_assign } }

        impl<const FRAC: i32> Rem<$Inner> for $Fixed<FRAC>
        where
            If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True,
        {
            type Output = $Fixed<FRAC>;
            #[inline]
            fn rem(self, rhs: $Inner) -> $Fixed<FRAC> {
                self.checked_rem_int(rhs).expect("division by zero")
            }
        }

        refs! { impl Rem<$Inner> for $Fixed($nbits) { rem } }

        impl<const FRAC: i32> RemAssign<$Inner> for $Fixed<FRAC>
        where
            If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True,
        {
            #[inline]
            fn rem_assign(&mut self, rhs: $Inner) {
                *self = (*self).rem(rhs);
            }
        }

        refs_assign! { impl RemAssign<$Inner> for $Fixed($nbits) { rem_assign } }

        shift_all! {
            impl {Shl, ShlAssign}<{
                i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
            }> for $Fixed {
                shl, shl_assign
            }
        }
        shift_all! {
            impl {Shr, ShrAssign}<{
                i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
            }> for $Fixed {
                shr, shr_assign
            }
        }

        impl<const FRAC: i32> Sum<$Fixed<FRAC>> for $Fixed<FRAC> {
            fn sum<I>(iter: I) -> $Fixed<FRAC>
            where
                I: Iterator<Item = $Fixed<FRAC>>,
            {
                iter.fold(Self::ZERO, Add::add)
            }
        }

        impl<'a, const FRAC: i32> Sum<&'a $Fixed<FRAC>> for $Fixed<FRAC> {
            fn sum<I>(iter: I) -> $Fixed<FRAC>
            where
                I: Iterator<Item = &'a $Fixed<FRAC>>,
            {
                iter.fold(Self::ZERO, Add::add)
            }
        }

        impl<const FRAC: i32> Product<$Fixed<FRAC>> for $Fixed<FRAC> {
            fn product<I>(mut iter: I) -> $Fixed<FRAC>
            where
                I: Iterator<Item = $Fixed<FRAC>>,
            {
                match iter.next() {
                    None => {
                        if FRAC >= $nbits || FRAC < 0 {
                            if cfg!(debug_assertions) {
                                panic!("overflow");
                            }
                            $Fixed::ZERO
                        } else {
                            $Fixed::from_bits(1 << FRAC)
                        }
                    }
                    Some(first) => iter.fold(first, Mul::mul),
                }
            }
        }

        impl<'a, const FRAC: i32> Product<&'a $Fixed<FRAC>> for $Fixed<FRAC> {
            fn product<I>(mut iter: I) -> $Fixed<FRAC>
            where
                I: Iterator<Item = &'a $Fixed<FRAC>>,
            {
                match iter.next() {
                    None => {
                        if FRAC >= $nbits || FRAC < 0 {
                            if cfg!(debug_assertions) {
                                panic!("overflow");
                            }
                            $Fixed::ZERO
                        } else {
                            $Fixed::from_bits(1 << FRAC)
                        }
                    }
                    Some(first) => iter.fold(*first, Mul::mul),
                }
            }
        }

        if_unsigned! {
            $Signedness;

            impl<const FRAC: i32> Div<$NonZeroInner> for $Fixed<FRAC> {
                type Output = $Fixed<FRAC>;
                #[inline]
                fn div(self, rhs: $NonZeroInner) -> $Fixed<FRAC> {
                    Self::from_bits(self.to_bits() / rhs)
                }
            }

            refs! { impl Div<$NonZeroInner> for $Fixed { div } }

            impl<const FRAC: i32> DivAssign<$NonZeroInner> for $Fixed<FRAC> {
                #[inline]
                fn div_assign(&mut self, rhs: $NonZeroInner) {
                    *self = (*self).div(rhs)
                }
            }

            refs_assign! { impl DivAssign<$NonZeroInner> for $Fixed { div_assign } }

            impl<const FRAC: i32> Rem<$NonZeroInner> for $Fixed<FRAC>
            where
                If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True,
            {
                type Output = $Fixed<FRAC>;
                #[inline]
                fn rem(self, rhs: $NonZeroInner) -> $Fixed<FRAC> {
                    // Hack to silence overflow operation error if we shift
                    // by FRAC directly.
                    let frac_nbits = FRAC as u32;
                    let rhs = rhs.get();
                    if frac_nbits == <$Inner>::BITS {
                        // rhs > self, so the remainder is self
                        return self;
                    }
                    let rhs_fixed_bits = rhs << frac_nbits;
                    if (rhs_fixed_bits >> frac_nbits) != rhs {
                        // rhs > self, so the remainder is self
                        return self;
                    }
                    // SAFETY: rhs_fixed_bits must have some significant bits since
                    // rhs_fixed_bits >> frac_nbits is equal to a non-zero value.
                    debug_assert_ne!(rhs_fixed_bits, 0);
                    let n = unsafe { $NonZeroInner::new_unchecked(rhs_fixed_bits) };
                    Self::from_bits(self.to_bits() % n)
                }
            }
        }

        if_signed! {
            $Signedness;

            impl<const FRAC: i32> Rem<$NonZeroInner> for $Fixed<FRAC>
            where
                If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True,
            {
                type Output = $Fixed<FRAC>;
                #[inline]
                fn rem(self, rhs: $NonZeroInner) -> $Fixed<FRAC> {
                    // Hack to silence overflow operation error if we shift
                    // by FRAC directly.
                    let frac_nbits = FRAC as u32;
                    let rhs = rhs.get();
                    let mut overflow = false;
                    let rhs_fixed_bits = if frac_nbits == <$Inner>::BITS {
                        overflow = true;
                        0
                    } else {
                        rhs << frac_nbits
                    };
                    if overflow || (rhs_fixed_bits >> frac_nbits) != rhs {
                        // Either
                        //   * |rhs| > |self|, and so remainder is self, or
                        //   * self is signed min with at least one integer bit,
                        //     and the value of rhs is -self, so remainder is 0.
                        return if self == Self::MIN
                            && (Self::INT_BITS > 0 && rhs == 1 << (Self::INT_BITS - 1))
                        {
                            Self::ZERO
                        } else {
                            self
                        };
                    }
                    if rhs_fixed_bits == -1 {
                        return Self::ZERO;
                    }
                    // SAFETY: rhs_fixed_bits cannot be -1, and cannot be zero because
                    // rhs_fixed_bits >> frac_nbits is equal to a non-zero value,
                    // so the remainder operation cannot fail.
                    match self.to_bits().checked_rem(rhs_fixed_bits) {
                        Some(rem) => Self::from_bits(rem),
                        None => {
                            #[cfg(debug_assertions)]
                            {
                                unreachable!();
                            }
                            #[cfg(not(debug_assertions))]
                            unsafe {
                                hint::unreachable_unchecked();
                            }
                        }
                    }
                }
            }
        }

        refs! { impl Rem<$NonZeroInner> for $Fixed($nbits) { rem } }

        impl<const FRAC: i32> RemAssign<$NonZeroInner> for $Fixed<FRAC>
        where
            If<{ (0 <= FRAC) & (FRAC <= $nbits) }>: True,
        {
            #[inline]
            fn rem_assign(&mut self, rhs: $NonZeroInner) {
                *self = (*self).rem(rhs)
            }
        }

        refs_assign! { impl RemAssign<$NonZeroInner> for $Fixed($nbits) { rem_assign } }
    };
}

fixed_arith! { FixedU8(u8, 8, NonZeroU8), Unsigned }
fixed_arith! { FixedU16(u16, 16, NonZeroU16), Unsigned }
fixed_arith! { FixedU32(u32, 32, NonZeroU32), Unsigned }
fixed_arith! { FixedU64(u64, 64, NonZeroU64), Unsigned }
fixed_arith! { FixedU128(u128, 128, NonZeroU128), Unsigned }
fixed_arith! { FixedI8(i8, 8, NonZeroI8), Signed }
fixed_arith! { FixedI16(i16, 16, NonZeroI16), Signed }
fixed_arith! { FixedI32(i32, 32, NonZeroI32), Signed }
fixed_arith! { FixedI64(i64, 64, NonZeroI64), Signed }
fixed_arith! { FixedI128(i128, 128, NonZeroI128), Signed }

macro_rules! mul_div_widen {
    ($Single:ident, $Double:ty, $Signedness:tt, $Unsigned:ty) => {
        pub mod $Single {
            #[inline]
            pub const fn overflowing_mul(
                lhs: $Single,
                rhs: $Single,
                frac_nbits: i32,
            ) -> ($Single, bool) {
                const BITS: i32 = <$Single>::BITS as i32;
                const BITS2: i32 = <$Double>::BITS as i32;

                if frac_nbits <= 0 {
                    let (prod, overflow1) = lhs.overflowing_mul(rhs);
                    if frac_nbits <= -BITS {
                        (0, overflow1 || prod != 0)
                    } else {
                        let shifted = prod << -frac_nbits;
                        let overflow2 = (shifted >> -frac_nbits) != prod;
                        (shifted, overflow1 || overflow2)
                    }
                } else if frac_nbits >= BITS2 {
                    let val = if_signed_unsigned!(
                        $Signedness,
                        if (lhs < 0) != (rhs < 0) { -1 } else { 0 },
                        0,
                    );
                    (val, false)
                } else {
                    let lhs2 = lhs as $Double;
                    let rhs2 = rhs as $Double;
                    let prod2 = lhs2 * rhs2;
                    let shifted2 = prod2 >> frac_nbits;
                    let shifted = shifted2 as $Single;
                    let overflow = (shifted as $Double) != shifted2;
                    (shifted, overflow)
                }
            }

            #[inline]
            pub const fn overflowing_mul_add(
                m1: $Single,
                m2: $Single,
                add: $Single,
                mut frac_nbits: i32,
            ) -> ($Single, bool) {
                const NBITS: i32 = <$Single>::BITS as i32;
                const NBITS2: i32 = <$Double>::BITS as i32;

                // If frac_nbits <= -NBITS, any non-zero product will overflow
                // becuase using an 8-bit analogy,
                //   * for signed, the shifted product would be at least -0x100
                //     or 0x100. -0x100 + 0x7f = -0x81, and 0x100 + -0x80 =
                //     0x80, and -0x81 and 0x80 are both still overflowing.
                //   * for unsigned, the shifted product would be at least
                //     0x100.
                if frac_nbits <= -128 {
                    return (add, m1 != 0 && m2 != 0);
                }

                if_signed! {
                    $Signedness;
                    // If frac_nbits >= NBITS2 - 1, the only shifted products possible are -1 and 0.
                    if frac_nbits >= NBITS2 - 1 {
                        return if m1 != 0 && m2 != 0 && (m1.is_negative() != m2.is_negative()) {
                            add.overflowing_sub(1)
                        } else {
                            (add, false)
                        };
                    }
                }
                if_unsigned! {
                    $Signedness;
                    // If frac_nbits >= NBITS2, the only shifted product possible is 0.
                    if frac_nbits >= NBITS2 {
                        return (add, false);
                    }
                }

                let m1_2 = m1 as $Double;
                let m2_2 = m2 as $Double;
                let prod2 = m1_2 * m2_2;
                let (prod2, overflow2) = if frac_nbits < 0 {
                    frac_nbits += NBITS;
                    prod2.overflowing_mul((<$Unsigned>::MAX as $Double) + 1)
                } else if frac_nbits > NBITS {
                    frac_nbits -= NBITS;
                    (prod2 >> NBITS, false)
                } else {
                    (prod2, false)
                };
                let lo = (prod2 >> frac_nbits) as $Unsigned;
                let hi = (prod2 >> frac_nbits >> NBITS) as $Single;
                if_signed_unsigned!(
                    $Signedness,
                    {
                        let (uns, carry) = lo.overflowing_add(add as $Unsigned);
                        let ans = uns as $Single;
                        let expected_hi = if (ans.is_negative() != add.is_negative()) == carry {
                            0
                        } else {
                            -1
                        };
                        (ans, overflow2 || hi != expected_hi)
                    },
                    {
                        let (ans, overflow) = lo.overflowing_add(add);
                        (ans, overflow2 || overflow || hi != 0)
                    },
                )
            }

            // 0 <= frac_nbits <= NBITS
            #[inline]
            pub const fn overflowing_div(
                lhs: $Single,
                rhs: $Single,
                frac_nbits: u32,
            ) -> ($Single, bool) {
                const NBITS: u32 = <$Single>::BITS;
                let lhs2 = (lhs as $Double) << frac_nbits;
                let rhs2 = (rhs as $Double);
                // Overflow at this stage can only occur for signed when
                // frac_nbits == NBITS, lhs == MIN, and rhs == -1.
                // In that case, wrapped answer is $Double::MIN as $Single == 0
                let (quot2, false) = lhs2.overflowing_div(rhs2) else {
                    return (0, true);
                };
                let quot = quot2 as $Single;
                let overflow = if_signed_unsigned!(
                    $Signedness,
                    quot2 >> NBITS != if quot < 0 { -1 } else { 0 },
                    quot2 >> NBITS != 0
                );
                (quot, overflow)
            }
        }
    };
}

mul_div_widen! { u8, u16, Unsigned, u8 }
mul_div_widen! { u16, u32, Unsigned, u16 }
mul_div_widen! { u32, u64, Unsigned, u32 }
mul_div_widen! { u64, u128, Unsigned, u64 }
mul_div_widen! { i8, i16, Signed, u8 }
mul_div_widen! { i16, i32, Signed, u16 }
mul_div_widen! { i32, i64, Signed, u32 }
mul_div_widen! { i64, i128, Signed, u64 }

pub mod u128 {
    use crate::int256::{self, U256};
    use core::num::NonZeroU128;

    #[inline]
    pub const fn overflowing_mul(lhs: u128, rhs: u128, frac_nbits: i32) -> (u128, bool) {
        if frac_nbits <= 0 {
            let (prod, overflow1) = lhs.overflowing_mul(rhs);
            if frac_nbits <= -128 {
                (0, overflow1 || prod != 0)
            } else {
                let shifted = prod << -frac_nbits;
                let overflow2 = (shifted >> -frac_nbits) != prod;
                (shifted, overflow1 || overflow2)
            }
        } else if frac_nbits >= 256 {
            (0, false)
        } else {
            let prod = int256::wide_mul_u128(lhs, rhs);
            if frac_nbits >= 128 {
                (prod.hi >> (frac_nbits - 128), false)
            } else if frac_nbits == 0 {
                (prod.lo, prod.hi != 0)
            } else {
                let lo = prod.lo >> frac_nbits;
                let hi = prod.hi << (128 - frac_nbits);
                (lo | hi, hi >> (128 - frac_nbits) != prod.hi)
            }
        }
    }

    #[inline]
    pub const fn overflowing_mul_add(
        m1: u128,
        m2: u128,
        add: u128,
        mut frac_nbits: i32,
    ) -> (u128, bool) {
        // If frac_nbits <= -128, any non-zero product will overflow becuase
        // using an 8-bit analogy, the shifted product would be at least 0x100.
        if frac_nbits <= -128 {
            return (add, m1 != 0 && m2 != 0);
        }

        // If frac_nbits >= 256, the only shifted product possible is 0.
        if frac_nbits >= 256 {
            return (add, false);
        }

        let mut prod = int256::wide_mul_u128(m1, m2);

        let mut overflow1 = false;
        if frac_nbits < 0 {
            frac_nbits += 128;
            debug_assert!(frac_nbits >= 0);
            overflow1 = prod.hi != 0;
            prod.hi = prod.lo;
            prod.lo = 0;
        } else if frac_nbits > 128 {
            frac_nbits -= 128;
            debug_assert!(frac_nbits <= 128);
            prod.lo = prod.hi;
            prod.hi = 0;
        }

        let (shifted, overflow2) = int256::overflowing_shl_u256_into_u128(prod, frac_nbits as u32);
        let (ans, overflow3) = shifted.overflowing_add(add);
        (ans, overflow1 | overflow2 | overflow3)
    }

    // 0 <= frac_nbits <= NBITS
    #[inline]
    pub const fn overflowing_div(lhs: u128, rhs: u128, frac_nbits: u32) -> (u128, bool) {
        if frac_nbits == 0 {
            return lhs.overflowing_div(rhs);
        }
        let Some(rhs) = NonZeroU128::new(rhs) else {
            panic!("division by zero");
        };
        overflowing_div_nz(lhs, rhs, frac_nbits)
    }

    // Neither rhs nor frac_nbits is zero.
    const fn overflowing_div_nz(lhs: u128, rhs: NonZeroU128, frac_nbits: u32) -> (u128, bool) {
        let lhs2 = if frac_nbits == 128 {
            U256 { lo: 0, hi: lhs }
        } else {
            U256 {
                lo: lhs << frac_nbits,
                hi: lhs >> (128 - frac_nbits),
            }
        };
        let (quot2, _) = int256::div_rem_u256_u128(lhs2, rhs);
        let quot = quot2.lo;
        let overflow = quot2.hi != 0;
        (quot, overflow)
    }
}

pub mod i128 {
    use crate::int256::{self, I256};
    use core::num::NonZeroI128;

    #[inline]
    pub const fn overflowing_mul(lhs: i128, rhs: i128, frac_nbits: i32) -> (i128, bool) {
        if frac_nbits <= 0 {
            let (prod, overflow1) = lhs.overflowing_mul(rhs);
            if frac_nbits <= -128 {
                (0, overflow1 || prod != 0)
            } else {
                let shifted = prod << -frac_nbits;
                let overflow2 = (shifted >> -frac_nbits) != prod;
                (shifted, overflow1 || overflow2)
            }
        } else if frac_nbits >= 256 {
            let val = if (lhs < 0) == (rhs < 0) { 0 } else { -1 };
            (val, false)
        } else {
            let prod = int256::wide_mul_i128(lhs, rhs);
            if frac_nbits >= 128 {
                (prod.hi >> (frac_nbits - 128), false)
            } else if frac_nbits == 0 {
                let val = prod.lo as i128;
                (val, prod.hi != val)
            } else {
                let lo = (prod.lo >> frac_nbits) as i128;
                let hi = prod.hi << (128 - frac_nbits);
                (lo | hi, hi >> (128 - frac_nbits) != prod.hi)
            }
        }
    }

    #[inline]
    pub const fn overflowing_mul_add(
        m1: i128,
        m2: i128,
        add: i128,
        mut frac_nbits: i32,
    ) -> (i128, bool) {
        // If frac_nbits <= -128, any non-zero product will overflow becuase
        // using an 8-bit analogy, the shifted product would be at least -0x100
        // or 0x100. -0x100 + 0x7f = -0x81, and 0x100 + -0x80 = 0x80, and -0x81
        // and 0x80 are both still overflowing.
        if frac_nbits <= -128 {
            return (add, m1 != 0 && m2 != 0);
        }

        // If frac_nbits >= 255, the only shifted products possible are -1 and 0.
        if frac_nbits >= 255 {
            return if m1 != 0 && m2 != 0 && (m1.is_negative() != m2.is_negative()) {
                add.overflowing_sub(1)
            } else {
                (add, false)
            };
        }

        let mut prod = int256::wide_mul_i128(m1, m2);

        let mut overflow1 = false;
        if frac_nbits < 0 {
            frac_nbits += 128;
            overflow1 = prod.hi != (prod.lo as i128) >> 127;
            prod.hi = prod.lo as i128;
            prod.lo = 0;
        } else if frac_nbits > 128 {
            frac_nbits -= 128;
            prod.lo = prod.hi as u128;
            prod.hi >>= 127;
        }

        let shifted = int256::shl_i256_max_128(prod, frac_nbits as u32);
        let (uns, carry) = shifted.lo.overflowing_add(add as u128);
        let ans = uns as i128;
        let mut expected_hi = ans >> 127;
        if add < 0 {
            expected_hi += 1;
        }
        if carry {
            expected_hi -= 1;
        }
        (ans, overflow1 | (shifted.hi != expected_hi))
    }

    // 0 <= frac_nbits <= NBITS
    #[inline]
    pub const fn overflowing_div(lhs: i128, rhs: i128, frac_nbits: u32) -> (i128, bool) {
        if frac_nbits == 0 {
            return lhs.overflowing_div(rhs);
        }
        let Some(rhs) = NonZeroI128::new(rhs) else {
            panic!("division by zero");
        };
        overflowing_div_nz(lhs, rhs, frac_nbits)
    }

    // Neither rhs nor frac_nbits is zero.
    const fn overflowing_div_nz(lhs: i128, rhs: NonZeroI128, frac_nbits: u32) -> (i128, bool) {
        let lhs2 = if frac_nbits == 128 {
            // In this case, overflow is possible in the wide division.
            // Then, the wrapped answer is I256::MIN as i128 == 0
            if lhs == i128::MIN && rhs.get() == -1 {
                return (0, true);
            }
            I256 { lo: 0, hi: lhs }
        } else {
            I256 {
                lo: (lhs << frac_nbits) as u128,
                hi: lhs >> (128 - frac_nbits),
            }
        };
        let (quot2, _) = int256::div_rem_i256_i128_no_overflow(lhs2, rhs);
        let quot = quot2.lo as i128;
        let overflow = quot2.hi != quot >> 127;
        (quot, overflow)
    }
}

pub const fn saturating_add_sub_i32(a: i32, b: i32, c: i32) -> i32 {
    let sum = a as i64 + b as i64 - c as i64;
    if sum < i32::MIN as i64 {
        i32::MIN
    } else if sum > i32::MAX as i64 {
        i32::MAX
    } else {
        sum as i32
    }
}

#[cfg(test)]
mod tests {
    use crate::{arith, *};

    #[test]
    fn fixed_u16() {
        const FRAC: i32 = 7;
        let frac = FRAC;
        let a = 12;
        let b = 5;
        for &(a, b) in &[(a, b), (b, a)] {
            let af = FixedU16::<FRAC>::from_num(a);
            let bf = FixedU16::<FRAC>::from_num(b);
            assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
            if a > b {
                assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
            }
            assert_eq!((af * bf).to_bits(), (a << frac) * b);
            assert_eq!((af / bf).to_bits(), (a << frac) / b);
            assert_eq!((af % bf).to_bits(), (a << frac) % (b << frac));
            assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
            assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
            assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
            assert_eq!((!af).to_bits(), !(a << frac));
            assert_eq!((af << 4u8).to_bits(), (a << frac) << 4);
            assert_eq!((af >> 4i128).to_bits(), (a << frac) >> 4);
            assert_eq!((af * b).to_bits(), (a << frac) * b);
            assert_eq!((b * af).to_bits(), (a << frac) * b);
            assert_eq!((af / b).to_bits(), (a << frac) / b);
            assert_eq!((af % b).to_bits(), (a << frac) % (b << frac));
        }
    }

    #[test]
    fn fixed_i16() {
        const FRAC: i32 = 7;
        let frac = FRAC;
        let a = 12;
        let b = 5;
        for &(a, b) in &[
            (a, b),
            (a, -b),
            (-a, b),
            (-a, -b),
            (b, a),
            (b, -a),
            (-b, a),
            (-b, -a),
        ] {
            let af = FixedI16::<FRAC>::from_num(a);
            let bf = FixedI16::<FRAC>::from_num(b);
            assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
            assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
            assert_eq!((af * bf).to_bits(), (a << frac) * b);
            assert_eq!((af / bf).to_bits(), (a << frac) / b);
            assert_eq!((af % bf).to_bits(), (a << frac) % (b << frac));
            assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
            assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
            assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
            assert_eq!((-af).to_bits(), -(a << frac));
            assert_eq!((!af).to_bits(), !(a << frac));
            assert_eq!((af << 4u8).to_bits(), (a << frac) << 4);
            assert_eq!((af >> 4i128).to_bits(), (a << frac) >> 4);
            assert_eq!((af * b).to_bits(), (a << frac) * b);
            assert_eq!((b * af).to_bits(), (a << frac) * b);
            assert_eq!((af / b).to_bits(), (a << frac) / b);
            assert_eq!((af % b).to_bits(), (a << frac) % (b << frac));
        }
    }

    #[test]
    fn fixed_u128() {
        use crate::types::{U0F128, U121F7, U128F0};

        let frac = U121F7::FRAC_BITS;
        let a = 0x0003_4567_89ab_cdef_0123_4567_89ab_cdef_u128;
        let b = 5;
        for &(a, b) in &[(a, b), (b, a)] {
            let af = U121F7::from_num(a);
            let bf = U121F7::from_num(b);
            assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
            if a > b {
                assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
            }
            assert_eq!((af * bf).to_bits(), (a << frac) * b);
            assert_eq!((af / bf).to_bits(), (a << frac) / b);
            assert_eq!((af % bf).to_bits(), (a << frac) % (b << frac));
            assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
            assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
            assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
            assert_eq!((!af).to_bits(), !(a << frac));
            assert_eq!((af << 4u8).to_bits(), (a << frac) << 4);
            assert_eq!((af >> 4i128).to_bits(), (a << frac) >> 4);
            assert_eq!((af * b).to_bits(), (a << frac) * b);
            assert_eq!((b * af).to_bits(), (a << frac) * b);
            assert_eq!((af / b).to_bits(), (a << frac) / b);
            assert_eq!((af % b).to_bits(), (a << frac) % (b << frac));

            let af = U0F128::from_bits(a);
            let bf = U0F128::from_bits(b);
            assert_eq!(af * bf, 0);
            assert_eq!(af * b, U0F128::from_bits(a * b));
            assert_eq!(a * bf, U0F128::from_bits(a * b));
            assert_eq!(bf * af, 0);

            let af = U128F0::from_num(a);
            let bf = U128F0::from_num(b);
            assert_eq!(af * bf, a * b);
            assert_eq!(af * b, a * b);
            assert_eq!(a * bf, a * b);
            assert_eq!(bf * af, a * b);
            assert_eq!(af / bf, a / b);
            assert_eq!(af / b, a / b);
            assert_eq!(af % bf, a % b);
            assert_eq!(af % b, a % b);
        }
    }

    #[test]
    fn fixed_i128() {
        use crate::types::{I0F128, I121F7, I128F0};

        let frac = I121F7::FRAC_BITS;
        let a = 0x0003_4567_89ab_cdef_0123_4567_89ab_cdef_i128;
        let b = 5;
        for &(a, b) in &[
            (a, b),
            (a, -b),
            (-a, b),
            (-a, -b),
            (b, a),
            (b, -a),
            (-b, a),
            (-b, -a),
        ] {
            let af = I121F7::from_num(a);
            let bf = I121F7::from_num(b);
            assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
            assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
            assert_eq!((af * bf).to_bits(), (a << frac) * b);
            assert_eq!((af / bf).to_bits(), (a << frac) / b);
            assert_eq!((af % bf).to_bits(), (a << frac) % (b << frac));
            assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
            assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
            assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
            assert_eq!((-af).to_bits(), -(a << frac));
            assert_eq!((!af).to_bits(), !(a << frac));
            assert_eq!((af << 4u8).to_bits(), (a << frac) << 4);
            assert_eq!((af >> 4i128).to_bits(), (a << frac) >> 4);
            assert_eq!((af * b).to_bits(), (a << frac) * b);
            assert_eq!((b * af).to_bits(), (a << frac) * b);
            assert_eq!((af / b).to_bits(), (a << frac) / b);
            assert_eq!((af % b).to_bits(), (a << frac) % (b << frac));

            let af = I0F128::from_bits(a);
            let bf = I0F128::from_bits(b);
            let prod = if a.is_negative() == b.is_negative() {
                I0F128::ZERO
            } else {
                -I0F128::DELTA
            };
            assert_eq!(af * bf, prod);
            assert_eq!(af * b, I0F128::from_bits(a * b));
            assert_eq!(a * bf, I0F128::from_bits(a * b));
            assert_eq!(bf * af, prod);

            let af = I128F0::from_num(a);
            let bf = I128F0::from_num(b);
            assert_eq!(af * bf, a * b);
            assert_eq!(af * b, a * b);
            assert_eq!(a * bf, a * b);
            assert_eq!(bf * af, a * b);
            assert_eq!(af / bf, a / b);
            assert_eq!(af / b, a / b);
            assert_eq!(af % bf, a % b);
            assert_eq!(af % b, a % b);
        }
    }

    fn check_rem_int(a: i32, b: i32) {
        use crate::types::I16F16;
        assert_eq!(I16F16::from_num(a) % b, a % b);
        assert_eq!(I16F16::from_num(a).rem_euclid_int(b), a.rem_euclid(b));
        match (I16F16::from_num(a).checked_rem_int(b), a.checked_rem(b)) {
            (Some(a), Some(b)) => assert_eq!(a, b),
            (None, None) => {}
            (a, b) => panic!("mismatch {a:?}, {b:?}"),
        }
        match (
            I16F16::from_num(a).checked_rem_euclid_int(b),
            a.checked_rem_euclid(b),
        ) {
            (Some(a), Some(b)) => assert_eq!(a, b),
            (None, None) => {}
            (a, b) => panic!("mismatch {a:?}, {b:?}"),
        }
    }

    #[test]
    #[allow(clippy::modulo_one)]
    fn rem_int() {
        use crate::types::{I0F32, I16F16, I1F31};
        check_rem_int(-0x8000, -0x8000);
        check_rem_int(-0x8000, -0x7fff);
        check_rem_int(-0x8000, 0x7fff);
        check_rem_int(-0x8000, 0x8000);
        check_rem_int(-0x7fff, -0x8000);
        check_rem_int(-0x7fff, -0x7fff);
        check_rem_int(-0x7fff, 0x7fff);
        check_rem_int(-0x7fff, 0x8000);
        check_rem_int(0x7fff, -0x8000);
        check_rem_int(0x7fff, -0x7fff);
        check_rem_int(0x7fff, 0x7fff);
        check_rem_int(0x7fff, 0x8000);

        fn i1(f: f32) -> I1F31 {
            I1F31::from_num(f)
        }
        fn i0(f: f32) -> I0F32 {
            I0F32::from_num(f)
        }

        assert_eq!(I16F16::MIN % -1, 0);
        assert_eq!(I16F16::MIN.checked_rem_int(-1).unwrap(), 0);
        assert_eq!(I16F16::MIN.rem_euclid_int(-1), 0);
        assert_eq!(I16F16::MIN.checked_rem_euclid_int(-1).unwrap(), 0);

        assert_eq!(i1(-1.0) % 1, i1(0.0));
        assert_eq!(i1(-1.0).rem_euclid_int(1), i1(0.0));

        assert_eq!(i1(-0.75) % 1, i1(-0.75));
        assert_eq!(i1(-0.75).rem_euclid_int(1), i1(0.25));

        assert_eq!(i1(-0.5) % 1, i1(-0.5));
        assert_eq!(i1(-0.5).rem_euclid_int(1), i1(0.5));

        assert_eq!(i1(-0.5) % 3, i1(-0.5));
        assert_eq!(i1(-0.5).checked_rem_euclid_int(3), None);
        assert_eq!(i1(-0.5).wrapping_rem_euclid_int(3), i1(0.5));
        assert_eq!(i1(-0.5).overflowing_rem_euclid_int(3), (i1(0.5), true));

        assert_eq!(i1(-0.25) % 1, i1(-0.25));
        assert_eq!(i1(-0.25).rem_euclid_int(1), i1(0.75));

        assert_eq!(i1(-0.25) % 3, i1(-0.25));
        assert_eq!(i1(-0.25).checked_rem_euclid_int(3), None);
        assert_eq!(i1(-0.25).wrapping_rem_euclid_int(3), i1(0.75));
        assert_eq!(i1(-0.25).overflowing_rem_euclid_int(3), (i1(0.75), true));

        assert_eq!(i1(0.0) % 1, i1(0.0));
        assert_eq!(i1(0.0).rem_euclid_int(1), i1(0.0));

        assert_eq!(i1(0.25) % 1, i1(0.25));
        assert_eq!(i1(0.25).rem_euclid_int(1), i1(0.25));

        assert_eq!(i1(0.5) % 1, i1(0.5));
        assert_eq!(i1(0.5).rem_euclid_int(1), i1(0.5));

        assert_eq!(i1(0.75) % 1, i1(0.75));
        assert_eq!(i1(0.75).rem_euclid_int(1), i1(0.75));

        assert_eq!(i0(-0.5) % 1, i0(-0.5));
        assert_eq!(i0(-0.5).checked_rem_euclid_int(1), None);
        assert_eq!(i0(-0.5).wrapping_rem_euclid_int(1), i0(-0.5));
        assert_eq!(i0(-0.5).overflowing_rem_euclid_int(1), (i0(-0.5), true));

        assert_eq!(i0(-0.375) % 1, i0(-0.375));
        assert_eq!(i0(-0.375).checked_rem_euclid_int(1), None);
        assert_eq!(i0(-0.375).wrapping_rem_euclid_int(1), i0(-0.375));
        assert_eq!(i0(-0.375).overflowing_rem_euclid_int(1), (i0(-0.375), true));

        assert_eq!(i0(-0.25) % 1, i0(-0.25));
        assert_eq!(i0(-0.25).checked_rem_euclid_int(1), None);
        assert_eq!(i0(-0.25).wrapping_rem_euclid_int(1), i0(-0.25));
        assert_eq!(i0(-0.25).overflowing_rem_euclid_int(1), (i0(-0.25), true));

        assert_eq!(i0(0.0) % 1, i0(0.0));
        assert_eq!(i0(0.0).rem_euclid_int(1), i0(0.0));

        assert_eq!(i0(0.25) % 1, i0(0.25));
        assert_eq!(i0(0.25).rem_euclid_int(1), i0(0.25));
    }

    #[test]
    fn div_rem_nonzerou() {
        use crate::types::{U0F32, U16F16, U1F31, U31F1, U32F0};
        use core::num::NonZeroU32;
        let half_bits = u32::from(u16::MAX);
        let vals = &[
            0,
            1,
            100,
            5555,
            half_bits - 1,
            half_bits,
            half_bits + 1,
            u32::MAX - 1,
            u32::MAX,
        ];
        for &a in vals {
            for &b in vals {
                let a0 = U0F32::from_bits(a);
                let a1 = U1F31::from_bits(a);
                let a16 = U16F16::from_bits(a);
                let a31 = U31F1::from_bits(a);
                let a32 = U32F0::from_bits(a);
                let Some(nz) = NonZeroU32::new(b) else {
                    continue;
                };
                assert_eq!(a0 / nz, a0 / b);
                assert_eq!(a0 % nz, a0 % b);
                assert_eq!(a1 / nz, a1 / b);
                assert_eq!(a1 % nz, a1 % b);
                assert_eq!(a16 / nz, a16 / b);
                assert_eq!(a16 % nz, a16 % b);
                assert_eq!(a31 / nz, a31 / b);
                assert_eq!(a31 % nz, a31 % b);
                assert_eq!(a32 / nz, a32 / b);
                assert_eq!(a32 % nz, a32 % b);
            }
        }
    }

    #[test]
    fn rem_nonzeroi() {
        use crate::types::{I0F32, I16F16, I1F31, I31F1, I32F0};
        use core::num::NonZeroI32;
        let vals = &[
            i32::MIN,
            i32::MIN + 1,
            -5555,
            -80,
            -1,
            0,
            1,
            100,
            5555,
            i32::MAX - 1,
            i32::MAX,
        ];
        for &a in vals {
            for &b in vals {
                let a0 = I0F32::from_bits(a);
                let a1 = I1F31::from_bits(a);
                let a16 = I16F16::from_bits(a);
                let a31 = I31F1::from_bits(a);
                let a32 = I32F0::from_bits(a);
                let Some(nz) = NonZeroI32::new(b) else {
                    continue;
                };
                assert_eq!(a0 % nz, a0 % b);
                assert_eq!(a1 % nz, a1 % b);
                assert_eq!(a16 % nz, a16 % b);
                assert_eq!(a31 % nz, a31 % b);
                assert_eq!(a32 % nz, a32 % b);
            }
        }
    }

    macro_rules! check_mul_add {
        ($($F:ty)*) => { $(
            let min = <$F>::MIN;
            let max = <$F>::MAX;
            let hmax = max / 2;
            let delta = <$F>::DELTA;
            let zero = <$F>::ZERO;
            let one = <$F>::ONE;
            let three = one * 3;
            let m_hmax = zero.wrapping_sub(hmax);
            let m_delta = zero.wrapping_sub(delta);
            let max_m_delta = max - delta;
            assert_eq!(max.overflowing_mul_add(one, zero), (max, false));
            assert_eq!(max.overflowing_mul_add(one, delta), (min, true));
            assert_eq!(max.overflowing_mul_add(one, m_delta), (max_m_delta, m_delta > 0));
            assert_eq!(max.overflowing_mul_add(three, max), (<$F>::from_bits(!0 << 2), true));
            assert_eq!(hmax.overflowing_mul_add(three, m_hmax), (hmax * 2, m_hmax > 0));
        )* };
    }

    macro_rules! check_mul_add_no_int {
        ($($F:ty)*) => { $(
            let min = <$F>::MIN;
            let max = <$F>::MAX;
            let hmax = max / 2;
            let delta = <$F>::DELTA;
            let zero = <$F>::ZERO;
            let quarter = delta << (<$F>::FRAC_BITS - 2);
            assert_eq!(max.overflowing_mul_add(quarter, zero), (max >> 2, false));
            if <$F>::IS_SIGNED {
                assert_eq!(max.overflowing_mul_add(max, zero), (hmax, false));
                assert_eq!(max.overflowing_mul_add(max, max), (min + hmax - delta, true));
            } else {
                assert_eq!(max.overflowing_mul_add(max, zero), (max - delta, false));
                assert_eq!(max.overflowing_mul_add(max, max), (max - 2 * delta, true));
            }
        )* };
    }

    #[test]
    fn mul_add() {
        use crate::types::*;
        check_mul_add! { I3F5 I3F13 I3F29 I3F61 I3F125 }
        check_mul_add! { I4F4 I8F8 I16F16 I32F32 I64F64 }
        check_mul_add! { I8F0 I16F0 I32F0 I64F0 I128F0 }
        check_mul_add! { U2F6 U2F14 U2F30 U2F62 U2F126 }
        check_mul_add! { U4F4 U8F8 U16F16 U32F32 U64F64 }
        check_mul_add! { U8F0 U16F0 U32F0 U64F0 U128F0 }

        check_mul_add_no_int! { I0F8 I0F16 I0F32 I0F64 I0F128 }
        check_mul_add_no_int! { U0F8 U0F16 U0F32 U0F64 U0F128 }
    }

    #[test]
    fn overflowing_mul_add_large_frac_nbits() {
        let nbits_2 = 128;

        let max = u64::MAX;

        assert_eq!(
            arith::u64::overflowing_mul_add(max, max, max, nbits_2),
            (max, false)
        );
        assert_eq!(
            arith::u64::overflowing_mul_add(max, max, max, nbits_2 - 1),
            (0, true)
        );
        assert_eq!(
            arith::u64::overflowing_mul_add(max, max, max - 1, nbits_2 - 1),
            (max, false)
        );

        let (min, max) = (i64::MIN, i64::MAX);

        assert_eq!(
            arith::i64::overflowing_mul_add(max, max, max, nbits_2 - 2),
            (max, false)
        );
        assert_eq!(
            arith::i64::overflowing_mul_add(max, max, max, nbits_2 - 3),
            (min, true)
        );
        assert_eq!(
            arith::i64::overflowing_mul_add(max, max, max - 1, nbits_2 - 3),
            (max, false)
        );

        assert_eq!(
            arith::i64::overflowing_mul_add(min, min, max, nbits_2 - 1),
            (max, false)
        );
        assert_eq!(
            arith::i64::overflowing_mul_add(min, min, max, nbits_2 - 2),
            (min, true)
        );
        assert_eq!(
            arith::i64::overflowing_mul_add(min, min, max - 1, nbits_2 - 2),
            (max, false)
        );

        assert_eq!(
            arith::i64::overflowing_mul_add(max, min, -max, nbits_2 - 2),
            (min, false)
        );
        assert_eq!(
            arith::i64::overflowing_mul_add(max, min, -max, nbits_2 - 3),
            (max, true)
        );
        assert_eq!(
            arith::i64::overflowing_mul_add(max, min, -max + 1, nbits_2 - 3),
            (min, false)
        );

        let nbits_2 = 256;

        let max = u128::MAX;

        assert_eq!(
            arith::u128::overflowing_mul_add(max, max, max, nbits_2),
            (max, false)
        );
        assert_eq!(
            arith::u128::overflowing_mul_add(max, max, max, nbits_2 - 1),
            (0, true)
        );
        assert_eq!(
            arith::u128::overflowing_mul_add(max, max, max - 1, nbits_2 - 1),
            (max, false)
        );

        let (min, max) = (i128::MIN, i128::MAX);

        assert_eq!(
            arith::i128::overflowing_mul_add(max, max, max, nbits_2 - 2),
            (max, false)
        );
        assert_eq!(
            arith::i128::overflowing_mul_add(max, max, max, nbits_2 - 3),
            (min, true)
        );
        assert_eq!(
            arith::i128::overflowing_mul_add(max, max, max - 1, nbits_2 - 3),
            (max, false)
        );

        assert_eq!(
            arith::i128::overflowing_mul_add(min, min, max, nbits_2 - 1),
            (max, false)
        );
        assert_eq!(
            arith::i128::overflowing_mul_add(min, min, max, nbits_2 - 2),
            (min, true)
        );
        assert_eq!(
            arith::i128::overflowing_mul_add(min, min, max - 1, nbits_2 - 2),
            (max, false)
        );

        assert_eq!(
            arith::i128::overflowing_mul_add(max, min, -max, nbits_2 - 2),
            (min, false)
        );
        assert_eq!(
            arith::i128::overflowing_mul_add(max, min, -max, nbits_2 - 3),
            (max, true)
        );
        assert_eq!(
            arith::i128::overflowing_mul_add(max, min, -max + 1, nbits_2 - 3),
            (min, false)
        );
    }

    #[test]
    fn overflowing_mul_add_neg_frac_nbits() {
        let nbits = 64;

        let (zero, one, max) = (0u64, 1u64, u64::MAX);

        assert_eq!(
            arith::u64::overflowing_mul_add(zero, zero, max, -nbits),
            (max, false)
        );
        assert_eq!(
            arith::u64::overflowing_mul_add(one, one, max, -nbits),
            (max, true)
        );
        assert_eq!(
            arith::u64::overflowing_mul_add(one, one, zero, 1 - nbits),
            (max - max / 2, false)
        );
        assert_eq!(
            arith::u64::overflowing_mul_add(one, one, max, 1 - nbits),
            (max / 2, true)
        );

        let (zero, one, min, max) = (0i64, 1i64, i64::MIN, i64::MAX);

        assert_eq!(
            arith::i64::overflowing_mul_add(zero, zero, max, -nbits),
            (max, false)
        );
        assert_eq!(
            arith::i64::overflowing_mul_add(one, one, max, -nbits),
            (max, true)
        );
        assert_eq!(
            arith::i64::overflowing_mul_add(one, one, -one, 1 - nbits),
            (max, false)
        );
        assert_eq!(
            arith::i64::overflowing_mul_add(one, one, zero, 1 - nbits),
            (min, true)
        );

        assert_eq!(
            arith::i64::overflowing_mul_add(-one, -one, max, -nbits),
            (max, true)
        );
        assert_eq!(
            arith::i64::overflowing_mul_add(-one, -one, -one, 1 - nbits),
            (max, false)
        );
        assert_eq!(
            arith::i64::overflowing_mul_add(-one, -one, zero, 1 - nbits),
            (min, true)
        );

        assert_eq!(
            arith::i64::overflowing_mul_add(one, -one, max, -nbits),
            (max, true)
        );
        assert_eq!(
            arith::i64::overflowing_mul_add(one, -one, min, -nbits),
            (min, true)
        );
        assert_eq!(
            arith::i64::overflowing_mul_add(one, -one, zero, 1 - nbits),
            (min, false)
        );
        assert_eq!(
            arith::i64::overflowing_mul_add(one, -one, max, 1 - nbits),
            (-one, false)
        );

        let nbits = 128;

        let (zero, one, max) = (0u128, 1u128, u128::MAX);

        assert_eq!(
            arith::u128::overflowing_mul_add(zero, zero, max, -nbits),
            (max, false)
        );
        assert_eq!(
            arith::u128::overflowing_mul_add(one, one, max, -nbits),
            (max, true)
        );
        assert_eq!(
            arith::u128::overflowing_mul_add(one, one, zero, 1 - nbits),
            (max - max / 2, false)
        );
        assert_eq!(
            arith::u128::overflowing_mul_add(one, one, max, 1 - nbits),
            (max / 2, true)
        );

        let (zero, one, min, max) = (0i128, 1i128, i128::MIN, i128::MAX);

        assert_eq!(
            arith::i128::overflowing_mul_add(zero, zero, max, -nbits),
            (max, false)
        );
        assert_eq!(
            arith::i128::overflowing_mul_add(one, one, max, -nbits),
            (max, true)
        );
        assert_eq!(
            arith::i128::overflowing_mul_add(one, one, -one, 1 - nbits),
            (max, false)
        );
        assert_eq!(
            arith::i128::overflowing_mul_add(one, one, zero, 1 - nbits),
            (min, true)
        );

        assert_eq!(
            arith::i128::overflowing_mul_add(-one, -one, max, -nbits),
            (max, true)
        );
        assert_eq!(
            arith::i128::overflowing_mul_add(-one, -one, -one, 1 - nbits),
            (max, false)
        );
        assert_eq!(
            arith::i128::overflowing_mul_add(-one, -one, zero, 1 - nbits),
            (min, true)
        );

        assert_eq!(
            arith::i128::overflowing_mul_add(one, -one, max, -nbits),
            (max, true)
        );
        assert_eq!(
            arith::i128::overflowing_mul_add(one, -one, min, -nbits),
            (min, true)
        );
        assert_eq!(
            arith::i128::overflowing_mul_add(one, -one, zero, 1 - nbits),
            (min, false)
        );
        assert_eq!(
            arith::i128::overflowing_mul_add(one, -one, max, 1 - nbits),
            (-one, false)
        );
    }

    #[test]
    fn issue_26() {
        use crate::{FixedI128, FixedU128};

        // issue 26 is about FixedI128<123>, the others are just some extra tests

        let x: FixedI128<120> = "-9.079999999999999999999".parse().unwrap();
        let squared = x.checked_mul(x).unwrap();
        assert!(82.44639 < squared && squared < 82.44641);
        let msquared = (-x).checked_mul(x).unwrap();
        assert!(-82.44641 < msquared && msquared < -82.44639);
        assert_eq!(x.checked_mul(-x), Some(msquared));
        assert_eq!((-x).checked_mul(-x), Some(squared));

        // 82 requires 8 signed integer bits
        let x: FixedI128<121> = "-9.079999999999999999999".parse().unwrap();
        assert!(x.checked_mul(x).is_none());
        assert!((-x).checked_mul(x).is_none());
        assert!(x.checked_mul(-x).is_none());
        assert!((-x).checked_mul(-x).is_none());
        let x: FixedI128<122> = "-9.079999999999999999999".parse().unwrap();
        assert!(x.checked_mul(x).is_none());
        assert!((-x).checked_mul(x).is_none());
        assert!(x.checked_mul(-x).is_none());
        assert!((-x).checked_mul(-x).is_none());
        let x: FixedI128<123> = "-9.079999999999999999999".parse().unwrap();
        assert!(x.checked_mul(x).is_none());
        assert!((-x).checked_mul(x).is_none());
        assert!(x.checked_mul(-x).is_none());
        assert!((-x).checked_mul(-x).is_none());

        let x: Result<FixedI128<124>, _> = "-9.079999999999999999999".parse();
        assert!(x.is_err());

        // Test unsigned

        let x: FixedU128<120> = "9.079999999999999999999".parse().unwrap();
        let squared = x.checked_mul(x).unwrap();
        assert!(82.44639 < squared && squared < 82.44641);

        // 82 requires 8 signed integer bits
        let x: FixedU128<122> = "9.079999999999999999999".parse().unwrap();
        assert!(x.checked_mul(x).is_none());
        let x: FixedU128<123> = "9.079999999999999999999".parse().unwrap();
        assert!(x.checked_mul(x).is_none());
        let x: FixedU128<124> = "9.079999999999999999999".parse().unwrap();
        assert!(x.checked_mul(x).is_none());

        let x: Result<FixedI128<125>, _> = "9.079999999999999999999".parse();
        assert!(x.is_err());
    }

    #[test]
    fn issue_51() {
        use crate::types::*;
        // these are for the bug:
        assert_eq!(I0F8::MIN.overflowing_div(-I0F8::DELTA), (I0F8::ZERO, true));
        assert_eq!(
            I0F16::MIN.overflowing_div(-I0F16::DELTA),
            (I0F16::ZERO, true)
        );
        assert_eq!(
            I0F32::MIN.overflowing_div(-I0F32::DELTA),
            (I0F32::ZERO, true)
        );
        assert_eq!(
            I0F64::MIN.overflowing_div(-I0F64::DELTA),
            (I0F64::ZERO, true)
        );
        assert_eq!(
            I0F128::MIN.overflowing_div(-I0F128::DELTA),
            (I0F128::ZERO, true)
        );
        // some extra tests:
        assert_eq!(
            I0F32::MIN.overflowing_div(I0F32::DELTA),
            (I0F32::ZERO, true)
        );
        assert_eq!(I0F32::MIN.overflowing_div(I0F32::MIN), (I0F32::ZERO, true));
        assert_eq!(
            (-I0F32::MAX).overflowing_div(-I0F32::DELTA),
            (I0F32::ZERO, true)
        );
        assert_eq!(
            (-I0F32::MAX).overflowing_div(I0F32::DELTA),
            (I0F32::ZERO, true)
        );
        assert_eq!(
            (-I0F32::MAX).overflowing_div(I0F32::MIN),
            (I0F32::from_bits(-2), true)
        );
        assert_eq!(
            I0F128::MIN.overflowing_div(I0F128::DELTA),
            (I0F128::ZERO, true)
        );
        assert_eq!(
            I0F128::MIN.overflowing_div(I0F128::MIN),
            (I0F128::ZERO, true)
        );
        assert_eq!(
            (-I0F128::MAX).overflowing_div(-I0F128::DELTA),
            (I0F128::ZERO, true)
        );
        assert_eq!(
            (-I0F128::MAX).overflowing_div(I0F128::DELTA),
            (I0F128::ZERO, true)
        );
        assert_eq!(
            (-I0F128::MAX).overflowing_div(I0F128::MIN),
            (I0F128::from_bits(-2), true)
        );
    }
}
