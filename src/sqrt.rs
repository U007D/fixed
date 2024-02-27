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

// q_i = sqrt(y) truncated to i bits after point.
// q_0 = 1
// y_i = 2^i (y - q_i^2)
// y_0 = y - 1
//
// If (q_i + 1>>(i+1))^2 <= y:
//     q_(i+1) = q_i + 1>>(i+1)
// Else:
//     q_(i+1) = q_i
//
// Equivalently:
//
// If q_i + 1>>(i+2) <= y_i:
//     q_(i+1) = q_i + 1>>(i+1)
//     y_(i+1) = 2 (y_i - q_i - 1>>(i+2))
// Else:
//     q_i+1 = q_i
//     y_i+1 = 2 y_i
//
//   * Iterations do not include q_0, y_0 as they are initialization.
//   * i goes from 1 to iter.
//   * Both q and y are stored with 2 integer bits. q is in range [1, 2); y is
//     in range [1, 4).
//   * 1>>(i+2) needs special code when i + 2 > nbits - 2. Since maximum iter is
//     nbits - 1, i + 2 can be nbits + 1 which is > nbits - 2 by 2.
//
// Some examples for u8.
//
// frac_nbits == 0:
//     sip = 4 - leading / 2
//     4 significant int pairs: 0100 0000. -> 0000 1000. (y << 0, 3 iter, q >> 3)
//     3 significant int pairs: 0001 0000. -> 0000 0100. (y << 2, 2 iter, q >> 4)
//     2 significant int pairs: 0000 0100. -> 0000 0010. (y << 4, 1 iter, q >> 5)
//     1 significant int pairs: 0000 0001. -> 0000 0001. (y << 6, 0 iter, q >> 6)
//     General: y << 8 - 2sip, -1 + sip iter, q >> 7 - sip
//
// frac_nbits == 1:
//     sip = 4 - (leading + 1) / 2
//     4 significant int pairs: 100 0000.0 -> 000 1000.0 (y >> 1, 4 iter, q >> 2)
//     3 significant int pairs: 001 0000.0 -> 000 0100.0 (y << 1, 3 iter, q >> 3)
//     2 significant int pairs: 000 0100.0 -> 000 0010.0 (y << 3, 2 iter, q >> 4)
//     1 significant int pairs: 000 0001.0 -> 000 0001.0 (y << 5, 1 iter, q >> 5)
//     0 significant int pairs: 000 0000.1 -> 000 0000.1 (y << 7, 0 iter, q >> 6)
//     General: y << 7 - 2sip, sip iter, q >> 6 - sip
//
// frac_nbits == 2:
//     sip = 3 - leading / 2
//     3 significant int pairs: 01 0000.00 -> 00 0100.00 (y << 0, 4 iter, q >> 2)
//     2 significant int pairs: 00 0100.00 -> 00 0010.00 (y << 2, 3 iter, q >> 3)
//     1 significant int pairs: 00 0001.00 -> 00 0001.00 (y << 4, 2 iter, q >> 4)
//     0 significant int pairs: 00 0000.01 -> 00 0000.10 (y << 6, 1 iter, q >> 5)
//     General: y << 6 - 2sip, 1 + sip iter, q >> 5 - sip
//
// frac_nbits = 3:
//     sip = 3 - (leading + 1) / 2
//     3 significant int pairs: 1 0000.000 -> 0 0100.000 (y >> 1, 5 iter, q >> 1)
//     2 significant int pairs: 0 0100.000 -> 0 0010.000 (y << 1, 4 iter, q >> 2)
//     1 significant int pairs: 0 0001.000 -> 0 0001.000 (y << 3, 3 iter, q >> 3)
//     0 significant int pairs: 0 0000.010 -> 0 0000.100 (y << 5, 2 iter, q >> 4)
//    -1 significant int pairs: 0 0000.001 -> 0 0000.010 (y << 7, 1 iter, q >> 5)
//     General: y << 5 - 2sip, 2 + sip iter, q >> 4 - sip
//
// frac_nbits == 4:
//     sip = 2 - leading / 2
//     2 significant int pairs: 0100.0000 -> 0010.0000 (y << 0, 5 iter, q >> 1)
//     1 significant int pairs: 0001.0000 -> 0001.0000 (y << 2, 4 iter, q >> 2)
//     0 significant int pairs: 0000.0100 -> 0000.1000 (y << 4, 3 iter, q >> 3)
//    -1 significant int pairs: 0000.0001 -> 0000.0100 (y << 6, 2 iter, q >> 4)
//     General: y << 4 - 2sip, 3 + sip iter, q >> 3 - sip
//
// frac_nbits = 5:
//     sip = 2 - (leading + 1) / 2
//     2 significant int pairs: 100.0000 0 -> 010.0000 0 (y >> 1, 6 iter, q >> 0)
//     1 significant int pairs: 001.0000 0 -> 001.0000 0 (y << 1, 5 iter, q >> 1)
//     0 significant int pairs: 000.0100 0 -> 000.1000 0 (y << 3, 4 iter, q >> 2)
//    -1 significant int pairs: 000.0001 0 -> 000.0100 0 (y << 5, 3 iter, q >> 3)
//    -2 significant int pairs: 000.0000 1 -> 000.0010 1 (y << 7, 2 iter, q >> 4)
//     General: y << 3 - 2sip, 4 + sip iter, q >> 2 - sip
//
// frac_nbits == 6:
//     sip = 1 - leading / 2
//     1 significant int pairs: 01.0000 00 -> 01.0000 00 (y << 0, 6 iter, q >> 0)
//     0 significant int pairs: 00.0100 00 -> 00.1000 00 (y << 2, 5 iter, q >> 1)
//    -1 significant int pairs: 00.0001 00 -> 00.0100 00 (y << 4, 4 iter, q >> 2)
//    -2 significant int pairs: 00.0000 01 -> 00.0010 00 (y << 6, 3 iter, q >> 3)
//     General: y << 2 - 2sip, 5 + sip iter, q >> 1 - sip
//
// frac_nbits == 7:
//     sip = 1 - (leading + 1) / 2
//     1 significant int pairs: 1.0000 000 -> 1.0000 000 (y >> 1, 7 iter, q << 1)
//     0 significant int pairs: 0.0100 000 -> 0.1000 000 (y << 1, 6 iter, q >> 0)
//    -1 significant int pairs: 0.0001 000 -> 0.0100 000 (y << 3, 5 iter, q >> 1)
//    -2 significant int pairs: 0.0000 010 -> 0.0010 000 (y << 5, 4 iter, q >> 2)
//    -3 significant int pairs: 0.0000 001 -> 0.0001 011 (y << 7, 3 iter, q >> 3)
//     General: y << 1 - 2sip, 6 + sip iter, q >> -sip
//
// frac_nbits == 8:
//     sip = 0 - leading / 2
//     0 significant int pairs: .0100 0000 -> .1000 0000 (y << 0, 7 iter, q << 1)
//    -1 significant int pairs: .0001 0000 -> .0100 0000 (y << 2, 6 iter, q >> 0)
//    -2 significant int pairs: .0000 0100 -> .0010 0000 (y << 4, 5 iter, q >> 1)
//    -3 significant int pairs: .0000 0001 -> .0001 0000 (y << 6, 4 iter, q >> 2)
//     General: y << -2sip, 7 + sip iter, q >> -1 - sip
//
// General:
//     Even frac_nbits:
//         sip = int_nbits / 2 - leading / 2
//     Odd frac_nbits:
//         sip = int_nbits / 2 - (leading + 1) / 2
//     Then:
//         y << int_nbits - 2sip, frac_nbits - 1 + sip iter, q >> int_nbits - 1 - sip

macro_rules! impl_sqrt {
    ($u:ident, $NZ:ident) => {
        pub const fn $u(val: $NZ, frac_nbits: u32) -> $u {
            let int_nbits = $u::BITS - frac_nbits;
            let odd_frac_nbits = frac_nbits % 2 != 0;
            let leading = val.leading_zeros();
            // significant integer pairs
            let sip = (int_nbits / 2) as i32
                - if odd_frac_nbits {
                    (leading + 1) / 2
                } else {
                    leading / 2
                } as i32;
            let shift = int_nbits as i32 - sip * 2;
            let y = if shift < 0 {
                val.get() >> -shift
            } else {
                val.get() << shift
            };
            let mut q_i = 1 << ($u::BITS - 2);
            let mut y_i = y - q_i;
            let mut next_bit = q_i >> 1;
            let iters = (frac_nbits as i32 - 1 + sip) as u32;
            let mut i = 1;
            while i <= iters {
                let d = next_bit >> 1;
                if d == 0 {
                    if i == iters {
                        // here final shift must be 0, otherwise we wouldn't have
                        // room to potentially insert one extra bit
                        debug_assert!(int_nbits as i32 - 1 - sip == 0);

                        // d == 0.5, so we really need q_i + 0.5 <= y_i,
                        // which can be obtained with q_i < y_i
                        if q_i < y_i {
                            q_i += 1;
                        }

                        return q_i;
                    }

                    debug_assert!(i == iters + 1);
                    // here final shift must be -1, otherwise we wouldn't have
                    // room to potentially insert two extra bits
                    debug_assert!(int_nbits as i32 - 1 - sip == -1);

                    // d == 0.5, so we really need q_i + 0.5 <= y_i,
                    // which can be obtained with q_i < y_i
                    if q_i < y_i {
                        // we cannot subtract d == 0.5 from y_i immediately, so
                        // we subtract 1 from y_i after the multiplication by 2
                        y_i = (y_i - q_i) * 2 - 1;
                        q_i += 1;
                    } else {
                        y_i *= 2;
                    }

                    // d == 0.25, so we really need q_i + 0.25 <= y_i,
                    // which can be obtained with q_i < y_i
                    if q_i < y_i {
                        // we cannot add next_bit == 0.5 to q_i immediately, so we
                        // add 1 to q_i after the left shift
                        q_i = (q_i << 1) + 1;
                    } else {
                        q_i <<= 1;
                    }

                    return q_i;
                }
                if q_i + d <= y_i {
                    y_i -= q_i + d;
                    q_i += next_bit;
                }
                y_i *= 2;

                i += 1;
                next_bit = d;
            }
            let shift = int_nbits as i32 - 1 - sip;
            q_i >> shift
        }
    };
}

impl_sqrt! { u8, NonZeroU8 }
impl_sqrt! { u16, NonZeroU16 }
impl_sqrt! { u32, NonZeroU32 }
impl_sqrt! { u64, NonZeroU64 }
impl_sqrt! { u128, NonZeroU128 }
