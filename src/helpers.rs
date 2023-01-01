// Copyright © 2018–2023 Trevor Spiteri

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
    FixedU8,
};

pub trait Sealed {}

macro_rules! impl_sealed {
    ($Fixed:ident) => {
        impl<const FRAC: i32> Sealed for $Fixed<FRAC> {}
    };
}

impl_sealed! { FixedI8 }
impl_sealed! { FixedI16 }
impl_sealed! { FixedI32 }
impl_sealed! { FixedI64 }
impl_sealed! { FixedI128 }
impl_sealed! { FixedU8 }
impl_sealed! { FixedU16 }
impl_sealed! { FixedU32 }
impl_sealed! { FixedU64 }
impl_sealed! { FixedU128 }
