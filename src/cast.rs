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
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8, F128,
};
use az::{Cast, CheckedCast, OverflowingCast, SaturatingCast, UnwrappedCast, WrappingCast};
use half::{bf16, f16};

macro_rules! cast {
    ($Src:ident($nbits_src:expr); $Dst:ident($nbits_dst:expr)) => {
        impl<const SRC_FRAC: i32, const DST_FRAC: i32> Cast<$Dst<DST_FRAC>> for $Src<SRC_FRAC> {
            #[inline]
            fn cast(self) -> $Dst<DST_FRAC> {
                self.to_num()
            }
        }

        impl<const SRC_FRAC: i32, const DST_FRAC: i32> CheckedCast<$Dst<DST_FRAC>>
            for $Src<SRC_FRAC>
        {
            #[inline]
            fn checked_cast(self) -> Option<$Dst<DST_FRAC>> {
                self.checked_to_num()
            }
        }

        impl<const SRC_FRAC: i32, const DST_FRAC: i32> SaturatingCast<$Dst<DST_FRAC>>
            for $Src<SRC_FRAC>
        {
            #[inline]
            fn saturating_cast(self) -> $Dst<DST_FRAC> {
                self.saturating_to_num()
            }
        }

        impl<const SRC_FRAC: i32, const DST_FRAC: i32> WrappingCast<$Dst<DST_FRAC>>
            for $Src<SRC_FRAC>
        {
            #[inline]
            fn wrapping_cast(self) -> $Dst<DST_FRAC> {
                self.wrapping_to_num()
            }
        }

        impl<const SRC_FRAC: i32, const DST_FRAC: i32> OverflowingCast<$Dst<DST_FRAC>>
            for $Src<SRC_FRAC>
        {
            #[inline]
            fn overflowing_cast(self) -> ($Dst<DST_FRAC>, bool) {
                self.overflowing_to_num()
            }
        }

        impl<const SRC_FRAC: i32, const DST_FRAC: i32> UnwrappedCast<$Dst<DST_FRAC>>
            for $Src<SRC_FRAC>
        {
            #[inline]
            #[track_caller]
            fn unwrapped_cast(self) -> $Dst<DST_FRAC> {
                self.unwrapped_to_num()
            }
        }
    };

    ($Fixed:ident($nbits:expr); $Dst:ident) => {
        impl<const FRAC: i32> Cast<$Dst> for $Fixed<FRAC> {
            #[inline]
            fn cast(self) -> $Dst {
                self.to_num()
            }
        }

        impl<const FRAC: i32> CheckedCast<$Dst> for $Fixed<FRAC> {
            #[inline]
            fn checked_cast(self) -> Option<$Dst> {
                self.checked_to_num()
            }
        }

        impl<const FRAC: i32> SaturatingCast<$Dst> for $Fixed<FRAC> {
            #[inline]
            fn saturating_cast(self) -> $Dst {
                self.saturating_to_num()
            }
        }

        impl<const FRAC: i32> WrappingCast<$Dst> for $Fixed<FRAC> {
            #[inline]
            fn wrapping_cast(self) -> $Dst {
                self.wrapping_to_num()
            }
        }

        impl<const FRAC: i32> OverflowingCast<$Dst> for $Fixed<FRAC> {
            #[inline]
            fn overflowing_cast(self) -> ($Dst, bool) {
                self.overflowing_to_num()
            }
        }

        impl<const FRAC: i32> UnwrappedCast<$Dst> for $Fixed<FRAC> {
            #[inline]
            #[track_caller]
            fn unwrapped_cast(self) -> $Dst {
                self.unwrapped_to_num()
            }
        }
    };

    ($Src:ident; $Fixed:ident($nbits:expr)) => {
        impl<const FRAC: i32> Cast<$Fixed<FRAC>> for $Src {
            #[inline]
            fn cast(self) -> $Fixed<FRAC> {
                <$Fixed<FRAC>>::from_num(self)
            }
        }

        impl<const FRAC: i32> CheckedCast<$Fixed<FRAC>> for $Src {
            #[inline]
            fn checked_cast(self) -> Option<$Fixed<FRAC>> {
                <$Fixed<FRAC>>::checked_from_num(self)
            }
        }

        impl<const FRAC: i32> SaturatingCast<$Fixed<FRAC>> for $Src {
            #[inline]
            fn saturating_cast(self) -> $Fixed<FRAC> {
                <$Fixed<FRAC>>::saturating_from_num(self)
            }
        }

        impl<const FRAC: i32> WrappingCast<$Fixed<FRAC>> for $Src {
            #[inline]
            fn wrapping_cast(self) -> $Fixed<FRAC> {
                <$Fixed<FRAC>>::wrapping_from_num(self)
            }
        }

        impl<const FRAC: i32> OverflowingCast<$Fixed<FRAC>> for $Src {
            #[inline]
            fn overflowing_cast(self) -> ($Fixed<FRAC>, bool) {
                <$Fixed<FRAC>>::overflowing_from_num(self)
            }
        }

        impl<const FRAC: i32> UnwrappedCast<$Fixed<FRAC>> for $Src {
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
            f16, bf16, f32, f64, F128,
        }
    )* };
}

cast_num! {
    FixedI8(8), FixedI16(16), FixedI32(32), FixedI64(64), FixedI128(128),
    FixedU8(8), FixedU16(16), FixedU32(32), FixedU64(64), FixedU128(128),
}
