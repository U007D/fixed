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

macro_rules! make_helper {
    ($i: ident, $u:ident) => {
        pub mod $i {
            #[inline]
            pub const fn neg_abs(val: $i) -> (bool, $u) {
                (val.is_negative(), val.unsigned_abs())
            }
        }

        pub mod $u {
            #[inline]
            pub fn neg_abs(val: $u) -> (bool, $u) {
                (false, val)
            }
        }
    };
}

make_helper! { i8, u8 }
make_helper! { i16, u16 }
make_helper! { i32, u32 }
make_helper! { i64, u64 }
make_helper! { i128, u128 }
