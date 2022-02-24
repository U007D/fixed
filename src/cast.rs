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
    types::extra::{If, True},
    F128Bits, FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32,
    FixedU64, FixedU8,
};
use az_crate::{Cast, CheckedCast, OverflowingCast, SaturatingCast, UnwrappedCast, WrappingCast};
use half::{bf16, f16};

macro_rules! cast {
    ($Src:ident($nbits_src:expr); $Dst:ident($nbits_dst:expr)) => {
        impl<const FRAC_SRC: u32, const FRAC_DST: u32> Cast<$Dst<FRAC_DST>> for $Src<FRAC_SRC>
        where
            If<{ FRAC_SRC <= $nbits_src }>: True,
            If<{ FRAC_DST <= $nbits_dst }>: True,
        {
            #[inline]
            fn cast(self) -> $Dst<FRAC_DST> {
                self.to_num()
            }
        }

        impl<const FRAC_SRC: u32, const FRAC_DST: u32> CheckedCast<$Dst<FRAC_DST>>
            for $Src<FRAC_SRC>
        where
            If<{ FRAC_SRC <= $nbits_src }>: True,
            If<{ FRAC_DST <= $nbits_dst }>: True,
        {
            #[inline]
            fn checked_cast(self) -> Option<$Dst<FRAC_DST>> {
                self.checked_to_num()
            }
        }

        impl<const FRAC_SRC: u32, const FRAC_DST: u32> SaturatingCast<$Dst<FRAC_DST>>
            for $Src<FRAC_SRC>
        where
            If<{ FRAC_SRC <= $nbits_src }>: True,
            If<{ FRAC_DST <= $nbits_dst }>: True,
        {
            #[inline]
            fn saturating_cast(self) -> $Dst<FRAC_DST> {
                self.saturating_to_num()
            }
        }

        impl<const FRAC_SRC: u32, const FRAC_DST: u32> WrappingCast<$Dst<FRAC_DST>>
            for $Src<FRAC_SRC>
        where
            If<{ FRAC_SRC <= $nbits_src }>: True,
            If<{ FRAC_DST <= $nbits_dst }>: True,
        {
            #[inline]
            fn wrapping_cast(self) -> $Dst<FRAC_DST> {
                self.wrapping_to_num()
            }
        }

        impl<const FRAC_SRC: u32, const FRAC_DST: u32> OverflowingCast<$Dst<FRAC_DST>>
            for $Src<FRAC_SRC>
        where
            If<{ FRAC_SRC <= $nbits_src }>: True,
            If<{ FRAC_DST <= $nbits_dst }>: True,
        {
            #[inline]
            fn overflowing_cast(self) -> ($Dst<FRAC_DST>, bool) {
                self.overflowing_to_num()
            }
        }

        impl<const FRAC_SRC: u32, const FRAC_DST: u32> UnwrappedCast<$Dst<FRAC_DST>>
            for $Src<FRAC_SRC>
        where
            If<{ FRAC_SRC <= $nbits_src }>: True,
            If<{ FRAC_DST <= $nbits_dst }>: True,
        {
            #[inline]
            #[track_caller]
            fn unwrapped_cast(self) -> $Dst<FRAC_DST> {
                self.unwrapped_to_num()
            }
        }
    };

    ($Fixed:ident($nbits:expr); $Dst:ident) => {
        impl<const FRAC: u32> Cast<$Dst> for $Fixed<FRAC>
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn cast(self) -> $Dst {
                self.to_num()
            }
        }

        impl<const FRAC: u32> CheckedCast<$Dst> for $Fixed<FRAC>
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn checked_cast(self) -> Option<$Dst> {
                self.checked_to_num()
            }
        }

        impl<const FRAC: u32> SaturatingCast<$Dst> for $Fixed<FRAC>
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn saturating_cast(self) -> $Dst {
                self.saturating_to_num()
            }
        }

        impl<const FRAC: u32> WrappingCast<$Dst> for $Fixed<FRAC>
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn wrapping_cast(self) -> $Dst {
                self.wrapping_to_num()
            }
        }

        impl<const FRAC: u32> OverflowingCast<$Dst> for $Fixed<FRAC>
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn overflowing_cast(self) -> ($Dst, bool) {
                self.overflowing_to_num()
            }
        }

        impl<const FRAC: u32> UnwrappedCast<$Dst> for $Fixed<FRAC>
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            #[track_caller]
            fn unwrapped_cast(self) -> $Dst {
                self.unwrapped_to_num()
            }
        }
    };

    ($Src:ident; $Fixed:ident($nbits:expr)) => {
        impl<const FRAC: u32> Cast<$Fixed<FRAC>> for $Src
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn cast(self) -> $Fixed<FRAC> {
                <$Fixed<FRAC>>::from_num(self)
            }
        }

        impl<const FRAC: u32> CheckedCast<$Fixed<FRAC>> for $Src
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn checked_cast(self) -> Option<$Fixed<FRAC>> {
                <$Fixed<FRAC>>::checked_from_num(self)
            }
        }

        impl<const FRAC: u32> SaturatingCast<$Fixed<FRAC>> for $Src
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn saturating_cast(self) -> $Fixed<FRAC> {
                <$Fixed<FRAC>>::saturating_from_num(self)
            }
        }

        impl<const FRAC: u32> WrappingCast<$Fixed<FRAC>> for $Src
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn wrapping_cast(self) -> $Fixed<FRAC> {
                <$Fixed<FRAC>>::wrapping_from_num(self)
            }
        }

        impl<const FRAC: u32> OverflowingCast<$Fixed<FRAC>> for $Src
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            fn overflowing_cast(self) -> ($Fixed<FRAC>, bool) {
                <$Fixed<FRAC>>::overflowing_from_num(self)
            }
        }

        impl<const FRAC: u32> UnwrappedCast<$Fixed<FRAC>> for $Src
        where
            If<{ FRAC <= $nbits }>: True,
        {
            #[inline]
            #[track_caller]
            fn unwrapped_cast(self) -> $Fixed<FRAC> {
                <$Fixed<FRAC>>::unwrapped_from_num(self)
            }
        }
    };
}

macro_rules! cast_num {
    ($Src:ident($nbits_src:expr); $($Dst:ident($nbits_dst:expr),)*) => { $(
        cast! { $Src($nbits_src); $Dst($nbits_dst) }
    )* };
    ($Fixed:ident($nbits:expr); $($Num:ident,)*) => { $(
        cast! { $Fixed($nbits); $Num }
        cast! { $Num; $Fixed($nbits) }
    )* };
    ($($Fixed:ident($nbits:expr),)*) => { $(
        cast_num! {
            $Fixed($nbits);
            FixedI8(8), FixedI16(16), FixedI32(32), FixedI64(64), FixedI128(128),
            FixedU8(8), FixedU16(16), FixedU32(32), FixedU64(64), FixedU128(128),
        }
        cast! { bool; $Fixed($nbits) }
        cast_num! {
            $Fixed($nbits);
            i8, i16, i32, i64, i128, isize,
            u8, u16, u32, u64, u128, usize,
            f16, bf16, f32, f64, F128Bits,
        }
    )* };
}

cast_num! {
    FixedI8(8), FixedI16(16), FixedI32(32), FixedI64(64), FixedI128(128),
    FixedU8(8), FixedU16(16), FixedU32(32), FixedU64(64), FixedU128(128),
}
