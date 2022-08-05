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
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8, Unwrapped, Wrapping,
};
use bytemuck::{Pod, TransparentWrapper, Zeroable};

macro_rules! unsafe_impl_traits {
    ($Fixed:ident, $nbits:expr, $Inner:ident) => {
        unsafe impl<const FRAC: i32> Zeroable for $Fixed<FRAC> {}
        unsafe impl<const FRAC: i32> Pod for $Fixed<FRAC> {}
        unsafe impl<const FRAC: i32> TransparentWrapper<$Inner> for $Fixed<FRAC> {}

        unsafe impl<const FRAC: i32> Zeroable for Wrapping<$Fixed<FRAC>> {}
        unsafe impl<const FRAC: i32> Pod for Wrapping<$Fixed<FRAC>> {}
        unsafe impl<const FRAC: i32> TransparentWrapper<$Fixed<FRAC>> for Wrapping<$Fixed<FRAC>> {}

        unsafe impl<const FRAC: i32> Zeroable for Unwrapped<$Fixed<FRAC>> {}
        unsafe impl<const FRAC: i32> Pod for Unwrapped<$Fixed<FRAC>> {}
        unsafe impl<const FRAC: i32> TransparentWrapper<$Fixed<FRAC>> for Unwrapped<$Fixed<FRAC>> {}
    };
}

// SAFETY: all fixed-point numbers are repr(transparent) over primitive integer
// types which are both Pod and Zeroable, and Wrapping and Unwrapped are both
// repr(transparent) over fixed-point numbers.
unsafe_impl_traits! { FixedI8, 8, i8 }
unsafe_impl_traits! { FixedI16, 16, i16 }
unsafe_impl_traits! { FixedI32, 32, i32 }
unsafe_impl_traits! { FixedI64, 64, i64 }
unsafe_impl_traits! { FixedI128, 128, i128 }
unsafe_impl_traits! { FixedU8, 8, u8 }
unsafe_impl_traits! { FixedU16, 16, u16 }
unsafe_impl_traits! { FixedU32, 32, u32 }
unsafe_impl_traits! { FixedU64, 64, u64 }
unsafe_impl_traits! { FixedU128, 128, u128 }
