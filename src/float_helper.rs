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

macro_rules! make_helper {
    ($Float:ident($Bits:ident, $IBits:ident) $(; use $path:path)?) => {
        #[allow(non_snake_case)]
        pub mod $Float {
            use crate::{
                fixed_from_bits::{self, Shift},
                traits::Fixed,
            };
            use az::OverflowingCastFrom;
            use core::mem;
            $(use $path as $Float;)?

            // msb must be one
            pub fn from_neg_abs(
                neg: bool,
                abs: $Bits,
                frac_bits: i32,
            ) -> $Float {
                debug_assert!(abs.leading_zeros() == 0);

                let bits_sign = if neg { SIGN_MASK } else { 0 };

                // remove implicit ones
                let mut mantissa = abs << 1;
                let exponent = ($Bits::BITS as i32 - 1).saturating_sub(frac_bits);
                let biased_exponent = if exponent > EXP_MAX {
                    return $Float::from_bits(EXP_MASK | bits_sign);
                } else if exponent < EXP_MIN {
                    let lost_prec = EXP_MIN - exponent;
                    if lost_prec as u32 >= $Bits::BITS {
                        mantissa = 0;
                    } else {
                        // reinsert implicit one for subnormals (SIGN_MASK is most significant bit)
                        mantissa = (mantissa >> 1) | SIGN_MASK;
                        mantissa >>= lost_prec - 1;
                    }
                    0
                } else {
                    (exponent + EXP_BIAS) as $Bits
                };
                // check for rounding
                let round_up = {
                    let mid_bit = SIGN_MASK >> (PREC - 1);
                    let lower_bits = mid_bit - 1;
                    if mantissa & mid_bit == 0 {
                        false
                    } else if mantissa & lower_bits != 0 {
                        true
                    } else {
                        // round to even
                        mantissa & (mid_bit << 1) != 0
                    }
                };
                let bits_exp = biased_exponent << (PREC - 1);
                let bits_mantissa = mantissa >> ($Bits::BITS - (PREC - 1));
                let mut bits_exp_mantissa = bits_exp | bits_mantissa;
                if round_up {
                    bits_exp_mantissa += 1;
                }
                $Float::from_bits(bits_sign | bits_exp_mantissa)
            }

            pub fn overflowing_to_fixed<Dst: Fixed>(src: $Float) -> (Dst, bool) {
                // the most significant bits of src are zero, because of the
                // sign bit and exponent bits in floating-point representations
                let (neg, mut abs, mut src_frac) = match kind(src) {
                    Kind::NaN => panic!("NaN"),
                    Kind::Infinite { .. } => panic!("infinite"),
                    Kind::Finite {
                        neg,
                        abs,
                        frac_bits,
                    } => (neg, abs, frac_bits),
                };

                // Perform any shift right now to handle rounding and to trying
                // to convert negative numbers to unsigned if they should be
                // shifted to zero.
                match fixed_from_bits::src_shift(Dst::FRAC_BITS, src_frac, $Bits::BITS) {
                    Shift::Right(shift) => if shift > 0 {
                        let will_be_lsb = 1 << shift;
                        let removed_bits = abs & (will_be_lsb - 1);
                        let tie = will_be_lsb >> 1;
                        if removed_bits > tie || (removed_bits == tie && (abs & will_be_lsb) != 0) {
                            // either closer to next up (> tie)
                            // or tie and currently odd (prospective lsb != 0)
                            // so we round up
                            abs += will_be_lsb;
                        }
                        abs >>= shift;
                        src_frac -= shift as i32;
                    }
                    Shift::RightAll => return (Dst::ZERO, false),
                    _ => {}
                }

                let signed = (if neg { abs.wrapping_neg() } else { abs }) as  $IBits;

                let dst_bits = mem::size_of::<Dst>() as u32 * 8;

                // overflow1 is only for negative floats to unsigned fixed
                if dst_bits > $IBits::BITS {
                    let (wide, overflow1) = <Dst as Fixed>::Bits::overflowing_cast_from(signed);

                    match fixed_from_bits::src_shift(Dst::FRAC_BITS, src_frac, dst_bits) {
                        Shift::Right(shift) => {
                            // we have already done the right shift
                            debug_assert!(shift == 0);
                            (Dst::from_bits(wide), overflow1)
                        }
                        Shift::Left(shift) => {
                            let shifted = wide << shift;
                            let overflow2 = (shifted >> shift) != wide;
                            (Dst::from_bits(shifted), overflow2)
                        }
                        Shift::RightAll => {
                            // we have already done the right shift
                            unreachable!()
                        }
                        Shift::LeftAll => {
                            (Dst::ZERO, abs != 0)
                        }
                    }
                } else {
                    // src is at least as wide as dst,
                    match fixed_from_bits::src_shift(Dst::FRAC_BITS, src_frac, $IBits::BITS) {
                        Shift::Right(shift) => {
                            // we have already done the right shift
                            debug_assert!(shift == 0);
                            let (bits, overflow)
                                = <Dst as Fixed>::Bits::overflowing_cast_from(signed);
                            (Dst::from_bits(bits), overflow)
                        }
                        Shift::Left(shift) => {
                            let shifted = signed << shift;
                            let overflow1 = (shifted >> shift) != signed;
                            let (bits, overflow2)
                                = <Dst as Fixed>::Bits::overflowing_cast_from(shifted);
                            (Dst::from_bits(bits), overflow1 || overflow2)
                        }
                        Shift::RightAll => {
                            // we have already done the right shift
                            unreachable!()
                        }
                        Shift::LeftAll => {
                            (Dst::ZERO, abs != 0)
                        }
                    }
                }
            }

            const PREC: u32 = $Float::MANTISSA_DIGITS;
            const EXP_BIAS: i32 = (1 << ($Bits::BITS - PREC - 1)) - 1;
            const EXP_MIN: i32 = 1 - EXP_BIAS;
            const EXP_MAX: i32 = EXP_BIAS;
            pub const SIGN_MASK: $Bits = 1 << ($Bits::BITS - 1);
            pub const EXP_MASK: $Bits = !(SIGN_MASK | MANT_MASK);
            const MANT_MASK: $Bits = (1 << (PREC - 1)) - 1;

            // zero is NOT negative, that is zero is represented as
            // Kind::Finite { neg: false, abs: 0, frac_bits: 0 },
            pub enum Kind {
                NaN,
                Infinite { neg: bool },
                Finite { neg: bool, abs: $Bits, frac_bits: i32 },
            }

            #[inline]
            pub fn kind(val: $Float) -> Kind {
                let (neg, mut exp, mut mantissa) = parts(val);
                if exp > EXP_MAX {
                    return if mantissa == 0 {
                        Kind::Infinite { neg }
                    } else {
                        Kind::NaN
                    };
                }
                // if not subnormal, add implicit bit
                if exp >= EXP_MIN {
                    mantissa |= 1 << (PREC - 1);
                } else {
                    exp = EXP_MIN;
                }
                if mantissa == 0 {
                    return Kind::Finite {
                        neg: false,
                        abs: 0,
                        frac_bits: 0,
                    };
                }
                Kind::Finite {
                    neg,
                    abs: mantissa,
                    frac_bits: PREC as i32 - 1 - exp,
                }
            }

            #[inline]
            fn parts(val: $Float) -> (bool, i32, $Bits) {
                let bits = val.to_bits();
                let neg = bits & SIGN_MASK != 0;
                let biased_exp = (bits & EXP_MASK) >> (PREC - 1);
                let exp = biased_exp as i32 - EXP_BIAS;
                let mant = bits & MANT_MASK;

                (neg, exp, mant)
            }
        }
    };
}

make_helper! { half_f16(u16, i16); use half::f16 }
make_helper! { half_bf16(u16, i16); use half::bf16 }
make_helper! { f16(u16, i16) }
make_helper! { f32(u32, i32) }
make_helper! { f64(u64, i64) }
make_helper! { f128(u128, i128) }
