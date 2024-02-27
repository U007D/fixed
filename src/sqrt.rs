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

use core::num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8};

macro_rules! impl_sqrt {
    ($u:ident, $NZ:ident) => {
        pub const fn $u(val: $NZ, _frac_nbits: u32) -> $u {
            val.get()
        }
    };
}

impl_sqrt! { u8, NonZeroU8 }
impl_sqrt! { u16, NonZeroU16 }
impl_sqrt! { u32, NonZeroU32 }
impl_sqrt! { u64, NonZeroU64 }
impl_sqrt! { u128, NonZeroU128 }
