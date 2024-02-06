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
    FixedU8, Unwrapped, Wrapping,
};
use arbitrary::{Arbitrary, Result as ArbitraryResult, Unstructured};

macro_rules! impl_trait {
    ($Fixed:ident, $nbits:expr, $Inner:ident) => {
        impl<'a, const FRAC: i32> Arbitrary<'a> for $Fixed<FRAC> {
            #[inline]
            fn arbitrary(u: &mut Unstructured<'a>) -> ArbitraryResult<Self> {
                Ok(Self::from_bits(<$Inner as Arbitrary<'a>>::arbitrary(u)?))
            }

            #[inline]
            fn size_hint(depth: usize) -> (usize, Option<usize>) {
                <$Inner as Arbitrary<'a>>::size_hint(depth)
            }
        }

        impl<'a, const FRAC: i32> Arbitrary<'a> for Wrapping<$Fixed<FRAC>> {
            #[inline]
            fn arbitrary(u: &mut Unstructured<'a>) -> ArbitraryResult<Self> {
                Ok(Self::from_bits(<$Inner as Arbitrary<'a>>::arbitrary(u)?))
            }

            #[inline]
            fn size_hint(depth: usize) -> (usize, Option<usize>) {
                <$Inner as Arbitrary<'a>>::size_hint(depth)
            }
        }

        impl<'a, const FRAC: i32> Arbitrary<'a> for Unwrapped<$Fixed<FRAC>> {
            #[inline]
            fn arbitrary(u: &mut Unstructured<'a>) -> ArbitraryResult<Self> {
                Ok(Self::from_bits(<$Inner as Arbitrary<'a>>::arbitrary(u)?))
            }

            #[inline]
            fn size_hint(depth: usize) -> (usize, Option<usize>) {
                <$Inner as Arbitrary<'a>>::size_hint(depth)
            }
        }
    };
}

impl_trait! { FixedI8, 8, i8 }
impl_trait! { FixedI16, 16, i16 }
impl_trait! { FixedI32, 32, i32 }
impl_trait! { FixedI64, 64, i64 }
impl_trait! { FixedI128, 128, i128 }
impl_trait! { FixedU8, 8, u8 }
impl_trait! { FixedU16, 16, u16 }
impl_trait! { FixedU32, 32, u32 }
impl_trait! { FixedU64, 64, u64 }
impl_trait! { FixedU128, 128, u128 }
