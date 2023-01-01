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

/*!
Type aliases for all supported fixed-point numbers.
*/

use crate::{
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};

pub mod extra;

/*
```rust
fn num(n: i32, noun: &str) -> String {
    let mut ret = match n {
        0 => "no".to_string(),
        1 => "one".to_string(),
        2 => "two".to_string(),
        3 => "three".to_string(),
        4 => "four".to_string(),
        5 => "five".to_string(),
        6 => "six".to_string(),
        7 => "seven".to_string(),
        8 => "eight".to_string(),
        9 => "nine".to_string(),
        _ => n.to_string(),
    };
    ret.push_str(" ");
    ret.push_str(noun);
    if n != 1 {
        ret.push_str("s");
    }
    ret
}

fn main() {
    for &sign in &["I", "U"] {
        for &prim_bits in &[8, 16, 32, 64, 128] {
            for frac_bits in 0..=prim_bits {
                let int_bits = prim_bits - frac_bits;
                let int_desc = num(int_bits, "integer bit");
                let frac_desc = num(frac_bits, "fractional bit");
                println!(
                    "/// [`Fixed{}{}`] with {} and {}.",
                    sign, prim_bits, int_desc, frac_desc,
                );
                println!(
                    "pub type {0}{2}F{3} = Fixed{0}{1}<{3}>;",
                    sign, prim_bits, int_bits, frac_bits,
                );
            }
        }
    }
}
```
*/

/// [`FixedI8`] with eight integer bits and no fractional bits.
pub type I8F0 = FixedI8<0>;
/// [`FixedI8`] with seven integer bits and one fractional bit.
pub type I7F1 = FixedI8<1>;
/// [`FixedI8`] with six integer bits and two fractional bits.
pub type I6F2 = FixedI8<2>;
/// [`FixedI8`] with five integer bits and three fractional bits.
pub type I5F3 = FixedI8<3>;
/// [`FixedI8`] with four integer bits and four fractional bits.
pub type I4F4 = FixedI8<4>;
/// [`FixedI8`] with three integer bits and five fractional bits.
pub type I3F5 = FixedI8<5>;
/// [`FixedI8`] with two integer bits and six fractional bits.
pub type I2F6 = FixedI8<6>;
/// [`FixedI8`] with one integer bit and seven fractional bits.
pub type I1F7 = FixedI8<7>;
/// [`FixedI8`] with no integer bits and eight fractional bits.
pub type I0F8 = FixedI8<8>;
/// [`FixedI16`] with 16 integer bits and no fractional bits.
pub type I16F0 = FixedI16<0>;
/// [`FixedI16`] with 15 integer bits and one fractional bit.
pub type I15F1 = FixedI16<1>;
/// [`FixedI16`] with 14 integer bits and two fractional bits.
pub type I14F2 = FixedI16<2>;
/// [`FixedI16`] with 13 integer bits and three fractional bits.
pub type I13F3 = FixedI16<3>;
/// [`FixedI16`] with 12 integer bits and four fractional bits.
pub type I12F4 = FixedI16<4>;
/// [`FixedI16`] with 11 integer bits and five fractional bits.
pub type I11F5 = FixedI16<5>;
/// [`FixedI16`] with 10 integer bits and six fractional bits.
pub type I10F6 = FixedI16<6>;
/// [`FixedI16`] with nine integer bits and seven fractional bits.
pub type I9F7 = FixedI16<7>;
/// [`FixedI16`] with eight integer bits and eight fractional bits.
pub type I8F8 = FixedI16<8>;
/// [`FixedI16`] with seven integer bits and nine fractional bits.
pub type I7F9 = FixedI16<9>;
/// [`FixedI16`] with six integer bits and 10 fractional bits.
pub type I6F10 = FixedI16<10>;
/// [`FixedI16`] with five integer bits and 11 fractional bits.
pub type I5F11 = FixedI16<11>;
/// [`FixedI16`] with four integer bits and 12 fractional bits.
pub type I4F12 = FixedI16<12>;
/// [`FixedI16`] with three integer bits and 13 fractional bits.
pub type I3F13 = FixedI16<13>;
/// [`FixedI16`] with two integer bits and 14 fractional bits.
pub type I2F14 = FixedI16<14>;
/// [`FixedI16`] with one integer bit and 15 fractional bits.
pub type I1F15 = FixedI16<15>;
/// [`FixedI16`] with no integer bits and 16 fractional bits.
pub type I0F16 = FixedI16<16>;
/// [`FixedI32`] with 32 integer bits and no fractional bits.
pub type I32F0 = FixedI32<0>;
/// [`FixedI32`] with 31 integer bits and one fractional bit.
pub type I31F1 = FixedI32<1>;
/// [`FixedI32`] with 30 integer bits and two fractional bits.
pub type I30F2 = FixedI32<2>;
/// [`FixedI32`] with 29 integer bits and three fractional bits.
pub type I29F3 = FixedI32<3>;
/// [`FixedI32`] with 28 integer bits and four fractional bits.
pub type I28F4 = FixedI32<4>;
/// [`FixedI32`] with 27 integer bits and five fractional bits.
pub type I27F5 = FixedI32<5>;
/// [`FixedI32`] with 26 integer bits and six fractional bits.
pub type I26F6 = FixedI32<6>;
/// [`FixedI32`] with 25 integer bits and seven fractional bits.
pub type I25F7 = FixedI32<7>;
/// [`FixedI32`] with 24 integer bits and eight fractional bits.
pub type I24F8 = FixedI32<8>;
/// [`FixedI32`] with 23 integer bits and nine fractional bits.
pub type I23F9 = FixedI32<9>;
/// [`FixedI32`] with 22 integer bits and 10 fractional bits.
pub type I22F10 = FixedI32<10>;
/// [`FixedI32`] with 21 integer bits and 11 fractional bits.
pub type I21F11 = FixedI32<11>;
/// [`FixedI32`] with 20 integer bits and 12 fractional bits.
pub type I20F12 = FixedI32<12>;
/// [`FixedI32`] with 19 integer bits and 13 fractional bits.
pub type I19F13 = FixedI32<13>;
/// [`FixedI32`] with 18 integer bits and 14 fractional bits.
pub type I18F14 = FixedI32<14>;
/// [`FixedI32`] with 17 integer bits and 15 fractional bits.
pub type I17F15 = FixedI32<15>;
/// [`FixedI32`] with 16 integer bits and 16 fractional bits.
pub type I16F16 = FixedI32<16>;
/// [`FixedI32`] with 15 integer bits and 17 fractional bits.
pub type I15F17 = FixedI32<17>;
/// [`FixedI32`] with 14 integer bits and 18 fractional bits.
pub type I14F18 = FixedI32<18>;
/// [`FixedI32`] with 13 integer bits and 19 fractional bits.
pub type I13F19 = FixedI32<19>;
/// [`FixedI32`] with 12 integer bits and 20 fractional bits.
pub type I12F20 = FixedI32<20>;
/// [`FixedI32`] with 11 integer bits and 21 fractional bits.
pub type I11F21 = FixedI32<21>;
/// [`FixedI32`] with 10 integer bits and 22 fractional bits.
pub type I10F22 = FixedI32<22>;
/// [`FixedI32`] with nine integer bits and 23 fractional bits.
pub type I9F23 = FixedI32<23>;
/// [`FixedI32`] with eight integer bits and 24 fractional bits.
pub type I8F24 = FixedI32<24>;
/// [`FixedI32`] with seven integer bits and 25 fractional bits.
pub type I7F25 = FixedI32<25>;
/// [`FixedI32`] with six integer bits and 26 fractional bits.
pub type I6F26 = FixedI32<26>;
/// [`FixedI32`] with five integer bits and 27 fractional bits.
pub type I5F27 = FixedI32<27>;
/// [`FixedI32`] with four integer bits and 28 fractional bits.
pub type I4F28 = FixedI32<28>;
/// [`FixedI32`] with three integer bits and 29 fractional bits.
pub type I3F29 = FixedI32<29>;
/// [`FixedI32`] with two integer bits and 30 fractional bits.
pub type I2F30 = FixedI32<30>;
/// [`FixedI32`] with one integer bit and 31 fractional bits.
pub type I1F31 = FixedI32<31>;
/// [`FixedI32`] with no integer bits and 32 fractional bits.
pub type I0F32 = FixedI32<32>;
/// [`FixedI64`] with 64 integer bits and no fractional bits.
pub type I64F0 = FixedI64<0>;
/// [`FixedI64`] with 63 integer bits and one fractional bit.
pub type I63F1 = FixedI64<1>;
/// [`FixedI64`] with 62 integer bits and two fractional bits.
pub type I62F2 = FixedI64<2>;
/// [`FixedI64`] with 61 integer bits and three fractional bits.
pub type I61F3 = FixedI64<3>;
/// [`FixedI64`] with 60 integer bits and four fractional bits.
pub type I60F4 = FixedI64<4>;
/// [`FixedI64`] with 59 integer bits and five fractional bits.
pub type I59F5 = FixedI64<5>;
/// [`FixedI64`] with 58 integer bits and six fractional bits.
pub type I58F6 = FixedI64<6>;
/// [`FixedI64`] with 57 integer bits and seven fractional bits.
pub type I57F7 = FixedI64<7>;
/// [`FixedI64`] with 56 integer bits and eight fractional bits.
pub type I56F8 = FixedI64<8>;
/// [`FixedI64`] with 55 integer bits and nine fractional bits.
pub type I55F9 = FixedI64<9>;
/// [`FixedI64`] with 54 integer bits and 10 fractional bits.
pub type I54F10 = FixedI64<10>;
/// [`FixedI64`] with 53 integer bits and 11 fractional bits.
pub type I53F11 = FixedI64<11>;
/// [`FixedI64`] with 52 integer bits and 12 fractional bits.
pub type I52F12 = FixedI64<12>;
/// [`FixedI64`] with 51 integer bits and 13 fractional bits.
pub type I51F13 = FixedI64<13>;
/// [`FixedI64`] with 50 integer bits and 14 fractional bits.
pub type I50F14 = FixedI64<14>;
/// [`FixedI64`] with 49 integer bits and 15 fractional bits.
pub type I49F15 = FixedI64<15>;
/// [`FixedI64`] with 48 integer bits and 16 fractional bits.
pub type I48F16 = FixedI64<16>;
/// [`FixedI64`] with 47 integer bits and 17 fractional bits.
pub type I47F17 = FixedI64<17>;
/// [`FixedI64`] with 46 integer bits and 18 fractional bits.
pub type I46F18 = FixedI64<18>;
/// [`FixedI64`] with 45 integer bits and 19 fractional bits.
pub type I45F19 = FixedI64<19>;
/// [`FixedI64`] with 44 integer bits and 20 fractional bits.
pub type I44F20 = FixedI64<20>;
/// [`FixedI64`] with 43 integer bits and 21 fractional bits.
pub type I43F21 = FixedI64<21>;
/// [`FixedI64`] with 42 integer bits and 22 fractional bits.
pub type I42F22 = FixedI64<22>;
/// [`FixedI64`] with 41 integer bits and 23 fractional bits.
pub type I41F23 = FixedI64<23>;
/// [`FixedI64`] with 40 integer bits and 24 fractional bits.
pub type I40F24 = FixedI64<24>;
/// [`FixedI64`] with 39 integer bits and 25 fractional bits.
pub type I39F25 = FixedI64<25>;
/// [`FixedI64`] with 38 integer bits and 26 fractional bits.
pub type I38F26 = FixedI64<26>;
/// [`FixedI64`] with 37 integer bits and 27 fractional bits.
pub type I37F27 = FixedI64<27>;
/// [`FixedI64`] with 36 integer bits and 28 fractional bits.
pub type I36F28 = FixedI64<28>;
/// [`FixedI64`] with 35 integer bits and 29 fractional bits.
pub type I35F29 = FixedI64<29>;
/// [`FixedI64`] with 34 integer bits and 30 fractional bits.
pub type I34F30 = FixedI64<30>;
/// [`FixedI64`] with 33 integer bits and 31 fractional bits.
pub type I33F31 = FixedI64<31>;
/// [`FixedI64`] with 32 integer bits and 32 fractional bits.
pub type I32F32 = FixedI64<32>;
/// [`FixedI64`] with 31 integer bits and 33 fractional bits.
pub type I31F33 = FixedI64<33>;
/// [`FixedI64`] with 30 integer bits and 34 fractional bits.
pub type I30F34 = FixedI64<34>;
/// [`FixedI64`] with 29 integer bits and 35 fractional bits.
pub type I29F35 = FixedI64<35>;
/// [`FixedI64`] with 28 integer bits and 36 fractional bits.
pub type I28F36 = FixedI64<36>;
/// [`FixedI64`] with 27 integer bits and 37 fractional bits.
pub type I27F37 = FixedI64<37>;
/// [`FixedI64`] with 26 integer bits and 38 fractional bits.
pub type I26F38 = FixedI64<38>;
/// [`FixedI64`] with 25 integer bits and 39 fractional bits.
pub type I25F39 = FixedI64<39>;
/// [`FixedI64`] with 24 integer bits and 40 fractional bits.
pub type I24F40 = FixedI64<40>;
/// [`FixedI64`] with 23 integer bits and 41 fractional bits.
pub type I23F41 = FixedI64<41>;
/// [`FixedI64`] with 22 integer bits and 42 fractional bits.
pub type I22F42 = FixedI64<42>;
/// [`FixedI64`] with 21 integer bits and 43 fractional bits.
pub type I21F43 = FixedI64<43>;
/// [`FixedI64`] with 20 integer bits and 44 fractional bits.
pub type I20F44 = FixedI64<44>;
/// [`FixedI64`] with 19 integer bits and 45 fractional bits.
pub type I19F45 = FixedI64<45>;
/// [`FixedI64`] with 18 integer bits and 46 fractional bits.
pub type I18F46 = FixedI64<46>;
/// [`FixedI64`] with 17 integer bits and 47 fractional bits.
pub type I17F47 = FixedI64<47>;
/// [`FixedI64`] with 16 integer bits and 48 fractional bits.
pub type I16F48 = FixedI64<48>;
/// [`FixedI64`] with 15 integer bits and 49 fractional bits.
pub type I15F49 = FixedI64<49>;
/// [`FixedI64`] with 14 integer bits and 50 fractional bits.
pub type I14F50 = FixedI64<50>;
/// [`FixedI64`] with 13 integer bits and 51 fractional bits.
pub type I13F51 = FixedI64<51>;
/// [`FixedI64`] with 12 integer bits and 52 fractional bits.
pub type I12F52 = FixedI64<52>;
/// [`FixedI64`] with 11 integer bits and 53 fractional bits.
pub type I11F53 = FixedI64<53>;
/// [`FixedI64`] with 10 integer bits and 54 fractional bits.
pub type I10F54 = FixedI64<54>;
/// [`FixedI64`] with nine integer bits and 55 fractional bits.
pub type I9F55 = FixedI64<55>;
/// [`FixedI64`] with eight integer bits and 56 fractional bits.
pub type I8F56 = FixedI64<56>;
/// [`FixedI64`] with seven integer bits and 57 fractional bits.
pub type I7F57 = FixedI64<57>;
/// [`FixedI64`] with six integer bits and 58 fractional bits.
pub type I6F58 = FixedI64<58>;
/// [`FixedI64`] with five integer bits and 59 fractional bits.
pub type I5F59 = FixedI64<59>;
/// [`FixedI64`] with four integer bits and 60 fractional bits.
pub type I4F60 = FixedI64<60>;
/// [`FixedI64`] with three integer bits and 61 fractional bits.
pub type I3F61 = FixedI64<61>;
/// [`FixedI64`] with two integer bits and 62 fractional bits.
pub type I2F62 = FixedI64<62>;
/// [`FixedI64`] with one integer bit and 63 fractional bits.
pub type I1F63 = FixedI64<63>;
/// [`FixedI64`] with no integer bits and 64 fractional bits.
pub type I0F64 = FixedI64<64>;
/// [`FixedI128`] with 128 integer bits and no fractional bits.
pub type I128F0 = FixedI128<0>;
/// [`FixedI128`] with 127 integer bits and one fractional bit.
pub type I127F1 = FixedI128<1>;
/// [`FixedI128`] with 126 integer bits and two fractional bits.
pub type I126F2 = FixedI128<2>;
/// [`FixedI128`] with 125 integer bits and three fractional bits.
pub type I125F3 = FixedI128<3>;
/// [`FixedI128`] with 124 integer bits and four fractional bits.
pub type I124F4 = FixedI128<4>;
/// [`FixedI128`] with 123 integer bits and five fractional bits.
pub type I123F5 = FixedI128<5>;
/// [`FixedI128`] with 122 integer bits and six fractional bits.
pub type I122F6 = FixedI128<6>;
/// [`FixedI128`] with 121 integer bits and seven fractional bits.
pub type I121F7 = FixedI128<7>;
/// [`FixedI128`] with 120 integer bits and eight fractional bits.
pub type I120F8 = FixedI128<8>;
/// [`FixedI128`] with 119 integer bits and nine fractional bits.
pub type I119F9 = FixedI128<9>;
/// [`FixedI128`] with 118 integer bits and 10 fractional bits.
pub type I118F10 = FixedI128<10>;
/// [`FixedI128`] with 117 integer bits and 11 fractional bits.
pub type I117F11 = FixedI128<11>;
/// [`FixedI128`] with 116 integer bits and 12 fractional bits.
pub type I116F12 = FixedI128<12>;
/// [`FixedI128`] with 115 integer bits and 13 fractional bits.
pub type I115F13 = FixedI128<13>;
/// [`FixedI128`] with 114 integer bits and 14 fractional bits.
pub type I114F14 = FixedI128<14>;
/// [`FixedI128`] with 113 integer bits and 15 fractional bits.
pub type I113F15 = FixedI128<15>;
/// [`FixedI128`] with 112 integer bits and 16 fractional bits.
pub type I112F16 = FixedI128<16>;
/// [`FixedI128`] with 111 integer bits and 17 fractional bits.
pub type I111F17 = FixedI128<17>;
/// [`FixedI128`] with 110 integer bits and 18 fractional bits.
pub type I110F18 = FixedI128<18>;
/// [`FixedI128`] with 109 integer bits and 19 fractional bits.
pub type I109F19 = FixedI128<19>;
/// [`FixedI128`] with 108 integer bits and 20 fractional bits.
pub type I108F20 = FixedI128<20>;
/// [`FixedI128`] with 107 integer bits and 21 fractional bits.
pub type I107F21 = FixedI128<21>;
/// [`FixedI128`] with 106 integer bits and 22 fractional bits.
pub type I106F22 = FixedI128<22>;
/// [`FixedI128`] with 105 integer bits and 23 fractional bits.
pub type I105F23 = FixedI128<23>;
/// [`FixedI128`] with 104 integer bits and 24 fractional bits.
pub type I104F24 = FixedI128<24>;
/// [`FixedI128`] with 103 integer bits and 25 fractional bits.
pub type I103F25 = FixedI128<25>;
/// [`FixedI128`] with 102 integer bits and 26 fractional bits.
pub type I102F26 = FixedI128<26>;
/// [`FixedI128`] with 101 integer bits and 27 fractional bits.
pub type I101F27 = FixedI128<27>;
/// [`FixedI128`] with 100 integer bits and 28 fractional bits.
pub type I100F28 = FixedI128<28>;
/// [`FixedI128`] with 99 integer bits and 29 fractional bits.
pub type I99F29 = FixedI128<29>;
/// [`FixedI128`] with 98 integer bits and 30 fractional bits.
pub type I98F30 = FixedI128<30>;
/// [`FixedI128`] with 97 integer bits and 31 fractional bits.
pub type I97F31 = FixedI128<31>;
/// [`FixedI128`] with 96 integer bits and 32 fractional bits.
pub type I96F32 = FixedI128<32>;
/// [`FixedI128`] with 95 integer bits and 33 fractional bits.
pub type I95F33 = FixedI128<33>;
/// [`FixedI128`] with 94 integer bits and 34 fractional bits.
pub type I94F34 = FixedI128<34>;
/// [`FixedI128`] with 93 integer bits and 35 fractional bits.
pub type I93F35 = FixedI128<35>;
/// [`FixedI128`] with 92 integer bits and 36 fractional bits.
pub type I92F36 = FixedI128<36>;
/// [`FixedI128`] with 91 integer bits and 37 fractional bits.
pub type I91F37 = FixedI128<37>;
/// [`FixedI128`] with 90 integer bits and 38 fractional bits.
pub type I90F38 = FixedI128<38>;
/// [`FixedI128`] with 89 integer bits and 39 fractional bits.
pub type I89F39 = FixedI128<39>;
/// [`FixedI128`] with 88 integer bits and 40 fractional bits.
pub type I88F40 = FixedI128<40>;
/// [`FixedI128`] with 87 integer bits and 41 fractional bits.
pub type I87F41 = FixedI128<41>;
/// [`FixedI128`] with 86 integer bits and 42 fractional bits.
pub type I86F42 = FixedI128<42>;
/// [`FixedI128`] with 85 integer bits and 43 fractional bits.
pub type I85F43 = FixedI128<43>;
/// [`FixedI128`] with 84 integer bits and 44 fractional bits.
pub type I84F44 = FixedI128<44>;
/// [`FixedI128`] with 83 integer bits and 45 fractional bits.
pub type I83F45 = FixedI128<45>;
/// [`FixedI128`] with 82 integer bits and 46 fractional bits.
pub type I82F46 = FixedI128<46>;
/// [`FixedI128`] with 81 integer bits and 47 fractional bits.
pub type I81F47 = FixedI128<47>;
/// [`FixedI128`] with 80 integer bits and 48 fractional bits.
pub type I80F48 = FixedI128<48>;
/// [`FixedI128`] with 79 integer bits and 49 fractional bits.
pub type I79F49 = FixedI128<49>;
/// [`FixedI128`] with 78 integer bits and 50 fractional bits.
pub type I78F50 = FixedI128<50>;
/// [`FixedI128`] with 77 integer bits and 51 fractional bits.
pub type I77F51 = FixedI128<51>;
/// [`FixedI128`] with 76 integer bits and 52 fractional bits.
pub type I76F52 = FixedI128<52>;
/// [`FixedI128`] with 75 integer bits and 53 fractional bits.
pub type I75F53 = FixedI128<53>;
/// [`FixedI128`] with 74 integer bits and 54 fractional bits.
pub type I74F54 = FixedI128<54>;
/// [`FixedI128`] with 73 integer bits and 55 fractional bits.
pub type I73F55 = FixedI128<55>;
/// [`FixedI128`] with 72 integer bits and 56 fractional bits.
pub type I72F56 = FixedI128<56>;
/// [`FixedI128`] with 71 integer bits and 57 fractional bits.
pub type I71F57 = FixedI128<57>;
/// [`FixedI128`] with 70 integer bits and 58 fractional bits.
pub type I70F58 = FixedI128<58>;
/// [`FixedI128`] with 69 integer bits and 59 fractional bits.
pub type I69F59 = FixedI128<59>;
/// [`FixedI128`] with 68 integer bits and 60 fractional bits.
pub type I68F60 = FixedI128<60>;
/// [`FixedI128`] with 67 integer bits and 61 fractional bits.
pub type I67F61 = FixedI128<61>;
/// [`FixedI128`] with 66 integer bits and 62 fractional bits.
pub type I66F62 = FixedI128<62>;
/// [`FixedI128`] with 65 integer bits and 63 fractional bits.
pub type I65F63 = FixedI128<63>;
/// [`FixedI128`] with 64 integer bits and 64 fractional bits.
pub type I64F64 = FixedI128<64>;
/// [`FixedI128`] with 63 integer bits and 65 fractional bits.
pub type I63F65 = FixedI128<65>;
/// [`FixedI128`] with 62 integer bits and 66 fractional bits.
pub type I62F66 = FixedI128<66>;
/// [`FixedI128`] with 61 integer bits and 67 fractional bits.
pub type I61F67 = FixedI128<67>;
/// [`FixedI128`] with 60 integer bits and 68 fractional bits.
pub type I60F68 = FixedI128<68>;
/// [`FixedI128`] with 59 integer bits and 69 fractional bits.
pub type I59F69 = FixedI128<69>;
/// [`FixedI128`] with 58 integer bits and 70 fractional bits.
pub type I58F70 = FixedI128<70>;
/// [`FixedI128`] with 57 integer bits and 71 fractional bits.
pub type I57F71 = FixedI128<71>;
/// [`FixedI128`] with 56 integer bits and 72 fractional bits.
pub type I56F72 = FixedI128<72>;
/// [`FixedI128`] with 55 integer bits and 73 fractional bits.
pub type I55F73 = FixedI128<73>;
/// [`FixedI128`] with 54 integer bits and 74 fractional bits.
pub type I54F74 = FixedI128<74>;
/// [`FixedI128`] with 53 integer bits and 75 fractional bits.
pub type I53F75 = FixedI128<75>;
/// [`FixedI128`] with 52 integer bits and 76 fractional bits.
pub type I52F76 = FixedI128<76>;
/// [`FixedI128`] with 51 integer bits and 77 fractional bits.
pub type I51F77 = FixedI128<77>;
/// [`FixedI128`] with 50 integer bits and 78 fractional bits.
pub type I50F78 = FixedI128<78>;
/// [`FixedI128`] with 49 integer bits and 79 fractional bits.
pub type I49F79 = FixedI128<79>;
/// [`FixedI128`] with 48 integer bits and 80 fractional bits.
pub type I48F80 = FixedI128<80>;
/// [`FixedI128`] with 47 integer bits and 81 fractional bits.
pub type I47F81 = FixedI128<81>;
/// [`FixedI128`] with 46 integer bits and 82 fractional bits.
pub type I46F82 = FixedI128<82>;
/// [`FixedI128`] with 45 integer bits and 83 fractional bits.
pub type I45F83 = FixedI128<83>;
/// [`FixedI128`] with 44 integer bits and 84 fractional bits.
pub type I44F84 = FixedI128<84>;
/// [`FixedI128`] with 43 integer bits and 85 fractional bits.
pub type I43F85 = FixedI128<85>;
/// [`FixedI128`] with 42 integer bits and 86 fractional bits.
pub type I42F86 = FixedI128<86>;
/// [`FixedI128`] with 41 integer bits and 87 fractional bits.
pub type I41F87 = FixedI128<87>;
/// [`FixedI128`] with 40 integer bits and 88 fractional bits.
pub type I40F88 = FixedI128<88>;
/// [`FixedI128`] with 39 integer bits and 89 fractional bits.
pub type I39F89 = FixedI128<89>;
/// [`FixedI128`] with 38 integer bits and 90 fractional bits.
pub type I38F90 = FixedI128<90>;
/// [`FixedI128`] with 37 integer bits and 91 fractional bits.
pub type I37F91 = FixedI128<91>;
/// [`FixedI128`] with 36 integer bits and 92 fractional bits.
pub type I36F92 = FixedI128<92>;
/// [`FixedI128`] with 35 integer bits and 93 fractional bits.
pub type I35F93 = FixedI128<93>;
/// [`FixedI128`] with 34 integer bits and 94 fractional bits.
pub type I34F94 = FixedI128<94>;
/// [`FixedI128`] with 33 integer bits and 95 fractional bits.
pub type I33F95 = FixedI128<95>;
/// [`FixedI128`] with 32 integer bits and 96 fractional bits.
pub type I32F96 = FixedI128<96>;
/// [`FixedI128`] with 31 integer bits and 97 fractional bits.
pub type I31F97 = FixedI128<97>;
/// [`FixedI128`] with 30 integer bits and 98 fractional bits.
pub type I30F98 = FixedI128<98>;
/// [`FixedI128`] with 29 integer bits and 99 fractional bits.
pub type I29F99 = FixedI128<99>;
/// [`FixedI128`] with 28 integer bits and 100 fractional bits.
pub type I28F100 = FixedI128<100>;
/// [`FixedI128`] with 27 integer bits and 101 fractional bits.
pub type I27F101 = FixedI128<101>;
/// [`FixedI128`] with 26 integer bits and 102 fractional bits.
pub type I26F102 = FixedI128<102>;
/// [`FixedI128`] with 25 integer bits and 103 fractional bits.
pub type I25F103 = FixedI128<103>;
/// [`FixedI128`] with 24 integer bits and 104 fractional bits.
pub type I24F104 = FixedI128<104>;
/// [`FixedI128`] with 23 integer bits and 105 fractional bits.
pub type I23F105 = FixedI128<105>;
/// [`FixedI128`] with 22 integer bits and 106 fractional bits.
pub type I22F106 = FixedI128<106>;
/// [`FixedI128`] with 21 integer bits and 107 fractional bits.
pub type I21F107 = FixedI128<107>;
/// [`FixedI128`] with 20 integer bits and 108 fractional bits.
pub type I20F108 = FixedI128<108>;
/// [`FixedI128`] with 19 integer bits and 109 fractional bits.
pub type I19F109 = FixedI128<109>;
/// [`FixedI128`] with 18 integer bits and 110 fractional bits.
pub type I18F110 = FixedI128<110>;
/// [`FixedI128`] with 17 integer bits and 111 fractional bits.
pub type I17F111 = FixedI128<111>;
/// [`FixedI128`] with 16 integer bits and 112 fractional bits.
pub type I16F112 = FixedI128<112>;
/// [`FixedI128`] with 15 integer bits and 113 fractional bits.
pub type I15F113 = FixedI128<113>;
/// [`FixedI128`] with 14 integer bits and 114 fractional bits.
pub type I14F114 = FixedI128<114>;
/// [`FixedI128`] with 13 integer bits and 115 fractional bits.
pub type I13F115 = FixedI128<115>;
/// [`FixedI128`] with 12 integer bits and 116 fractional bits.
pub type I12F116 = FixedI128<116>;
/// [`FixedI128`] with 11 integer bits and 117 fractional bits.
pub type I11F117 = FixedI128<117>;
/// [`FixedI128`] with 10 integer bits and 118 fractional bits.
pub type I10F118 = FixedI128<118>;
/// [`FixedI128`] with nine integer bits and 119 fractional bits.
pub type I9F119 = FixedI128<119>;
/// [`FixedI128`] with eight integer bits and 120 fractional bits.
pub type I8F120 = FixedI128<120>;
/// [`FixedI128`] with seven integer bits and 121 fractional bits.
pub type I7F121 = FixedI128<121>;
/// [`FixedI128`] with six integer bits and 122 fractional bits.
pub type I6F122 = FixedI128<122>;
/// [`FixedI128`] with five integer bits and 123 fractional bits.
pub type I5F123 = FixedI128<123>;
/// [`FixedI128`] with four integer bits and 124 fractional bits.
pub type I4F124 = FixedI128<124>;
/// [`FixedI128`] with three integer bits and 125 fractional bits.
pub type I3F125 = FixedI128<125>;
/// [`FixedI128`] with two integer bits and 126 fractional bits.
pub type I2F126 = FixedI128<126>;
/// [`FixedI128`] with one integer bit and 127 fractional bits.
pub type I1F127 = FixedI128<127>;
/// [`FixedI128`] with no integer bits and 128 fractional bits.
pub type I0F128 = FixedI128<128>;
/// [`FixedU8`] with eight integer bits and no fractional bits.
pub type U8F0 = FixedU8<0>;
/// [`FixedU8`] with seven integer bits and one fractional bit.
pub type U7F1 = FixedU8<1>;
/// [`FixedU8`] with six integer bits and two fractional bits.
pub type U6F2 = FixedU8<2>;
/// [`FixedU8`] with five integer bits and three fractional bits.
pub type U5F3 = FixedU8<3>;
/// [`FixedU8`] with four integer bits and four fractional bits.
pub type U4F4 = FixedU8<4>;
/// [`FixedU8`] with three integer bits and five fractional bits.
pub type U3F5 = FixedU8<5>;
/// [`FixedU8`] with two integer bits and six fractional bits.
pub type U2F6 = FixedU8<6>;
/// [`FixedU8`] with one integer bit and seven fractional bits.
pub type U1F7 = FixedU8<7>;
/// [`FixedU8`] with no integer bits and eight fractional bits.
pub type U0F8 = FixedU8<8>;
/// [`FixedU16`] with 16 integer bits and no fractional bits.
pub type U16F0 = FixedU16<0>;
/// [`FixedU16`] with 15 integer bits and one fractional bit.
pub type U15F1 = FixedU16<1>;
/// [`FixedU16`] with 14 integer bits and two fractional bits.
pub type U14F2 = FixedU16<2>;
/// [`FixedU16`] with 13 integer bits and three fractional bits.
pub type U13F3 = FixedU16<3>;
/// [`FixedU16`] with 12 integer bits and four fractional bits.
pub type U12F4 = FixedU16<4>;
/// [`FixedU16`] with 11 integer bits and five fractional bits.
pub type U11F5 = FixedU16<5>;
/// [`FixedU16`] with 10 integer bits and six fractional bits.
pub type U10F6 = FixedU16<6>;
/// [`FixedU16`] with nine integer bits and seven fractional bits.
pub type U9F7 = FixedU16<7>;
/// [`FixedU16`] with eight integer bits and eight fractional bits.
pub type U8F8 = FixedU16<8>;
/// [`FixedU16`] with seven integer bits and nine fractional bits.
pub type U7F9 = FixedU16<9>;
/// [`FixedU16`] with six integer bits and 10 fractional bits.
pub type U6F10 = FixedU16<10>;
/// [`FixedU16`] with five integer bits and 11 fractional bits.
pub type U5F11 = FixedU16<11>;
/// [`FixedU16`] with four integer bits and 12 fractional bits.
pub type U4F12 = FixedU16<12>;
/// [`FixedU16`] with three integer bits and 13 fractional bits.
pub type U3F13 = FixedU16<13>;
/// [`FixedU16`] with two integer bits and 14 fractional bits.
pub type U2F14 = FixedU16<14>;
/// [`FixedU16`] with one integer bit and 15 fractional bits.
pub type U1F15 = FixedU16<15>;
/// [`FixedU16`] with no integer bits and 16 fractional bits.
pub type U0F16 = FixedU16<16>;
/// [`FixedU32`] with 32 integer bits and no fractional bits.
pub type U32F0 = FixedU32<0>;
/// [`FixedU32`] with 31 integer bits and one fractional bit.
pub type U31F1 = FixedU32<1>;
/// [`FixedU32`] with 30 integer bits and two fractional bits.
pub type U30F2 = FixedU32<2>;
/// [`FixedU32`] with 29 integer bits and three fractional bits.
pub type U29F3 = FixedU32<3>;
/// [`FixedU32`] with 28 integer bits and four fractional bits.
pub type U28F4 = FixedU32<4>;
/// [`FixedU32`] with 27 integer bits and five fractional bits.
pub type U27F5 = FixedU32<5>;
/// [`FixedU32`] with 26 integer bits and six fractional bits.
pub type U26F6 = FixedU32<6>;
/// [`FixedU32`] with 25 integer bits and seven fractional bits.
pub type U25F7 = FixedU32<7>;
/// [`FixedU32`] with 24 integer bits and eight fractional bits.
pub type U24F8 = FixedU32<8>;
/// [`FixedU32`] with 23 integer bits and nine fractional bits.
pub type U23F9 = FixedU32<9>;
/// [`FixedU32`] with 22 integer bits and 10 fractional bits.
pub type U22F10 = FixedU32<10>;
/// [`FixedU32`] with 21 integer bits and 11 fractional bits.
pub type U21F11 = FixedU32<11>;
/// [`FixedU32`] with 20 integer bits and 12 fractional bits.
pub type U20F12 = FixedU32<12>;
/// [`FixedU32`] with 19 integer bits and 13 fractional bits.
pub type U19F13 = FixedU32<13>;
/// [`FixedU32`] with 18 integer bits and 14 fractional bits.
pub type U18F14 = FixedU32<14>;
/// [`FixedU32`] with 17 integer bits and 15 fractional bits.
pub type U17F15 = FixedU32<15>;
/// [`FixedU32`] with 16 integer bits and 16 fractional bits.
pub type U16F16 = FixedU32<16>;
/// [`FixedU32`] with 15 integer bits and 17 fractional bits.
pub type U15F17 = FixedU32<17>;
/// [`FixedU32`] with 14 integer bits and 18 fractional bits.
pub type U14F18 = FixedU32<18>;
/// [`FixedU32`] with 13 integer bits and 19 fractional bits.
pub type U13F19 = FixedU32<19>;
/// [`FixedU32`] with 12 integer bits and 20 fractional bits.
pub type U12F20 = FixedU32<20>;
/// [`FixedU32`] with 11 integer bits and 21 fractional bits.
pub type U11F21 = FixedU32<21>;
/// [`FixedU32`] with 10 integer bits and 22 fractional bits.
pub type U10F22 = FixedU32<22>;
/// [`FixedU32`] with nine integer bits and 23 fractional bits.
pub type U9F23 = FixedU32<23>;
/// [`FixedU32`] with eight integer bits and 24 fractional bits.
pub type U8F24 = FixedU32<24>;
/// [`FixedU32`] with seven integer bits and 25 fractional bits.
pub type U7F25 = FixedU32<25>;
/// [`FixedU32`] with six integer bits and 26 fractional bits.
pub type U6F26 = FixedU32<26>;
/// [`FixedU32`] with five integer bits and 27 fractional bits.
pub type U5F27 = FixedU32<27>;
/// [`FixedU32`] with four integer bits and 28 fractional bits.
pub type U4F28 = FixedU32<28>;
/// [`FixedU32`] with three integer bits and 29 fractional bits.
pub type U3F29 = FixedU32<29>;
/// [`FixedU32`] with two integer bits and 30 fractional bits.
pub type U2F30 = FixedU32<30>;
/// [`FixedU32`] with one integer bit and 31 fractional bits.
pub type U1F31 = FixedU32<31>;
/// [`FixedU32`] with no integer bits and 32 fractional bits.
pub type U0F32 = FixedU32<32>;
/// [`FixedU64`] with 64 integer bits and no fractional bits.
pub type U64F0 = FixedU64<0>;
/// [`FixedU64`] with 63 integer bits and one fractional bit.
pub type U63F1 = FixedU64<1>;
/// [`FixedU64`] with 62 integer bits and two fractional bits.
pub type U62F2 = FixedU64<2>;
/// [`FixedU64`] with 61 integer bits and three fractional bits.
pub type U61F3 = FixedU64<3>;
/// [`FixedU64`] with 60 integer bits and four fractional bits.
pub type U60F4 = FixedU64<4>;
/// [`FixedU64`] with 59 integer bits and five fractional bits.
pub type U59F5 = FixedU64<5>;
/// [`FixedU64`] with 58 integer bits and six fractional bits.
pub type U58F6 = FixedU64<6>;
/// [`FixedU64`] with 57 integer bits and seven fractional bits.
pub type U57F7 = FixedU64<7>;
/// [`FixedU64`] with 56 integer bits and eight fractional bits.
pub type U56F8 = FixedU64<8>;
/// [`FixedU64`] with 55 integer bits and nine fractional bits.
pub type U55F9 = FixedU64<9>;
/// [`FixedU64`] with 54 integer bits and 10 fractional bits.
pub type U54F10 = FixedU64<10>;
/// [`FixedU64`] with 53 integer bits and 11 fractional bits.
pub type U53F11 = FixedU64<11>;
/// [`FixedU64`] with 52 integer bits and 12 fractional bits.
pub type U52F12 = FixedU64<12>;
/// [`FixedU64`] with 51 integer bits and 13 fractional bits.
pub type U51F13 = FixedU64<13>;
/// [`FixedU64`] with 50 integer bits and 14 fractional bits.
pub type U50F14 = FixedU64<14>;
/// [`FixedU64`] with 49 integer bits and 15 fractional bits.
pub type U49F15 = FixedU64<15>;
/// [`FixedU64`] with 48 integer bits and 16 fractional bits.
pub type U48F16 = FixedU64<16>;
/// [`FixedU64`] with 47 integer bits and 17 fractional bits.
pub type U47F17 = FixedU64<17>;
/// [`FixedU64`] with 46 integer bits and 18 fractional bits.
pub type U46F18 = FixedU64<18>;
/// [`FixedU64`] with 45 integer bits and 19 fractional bits.
pub type U45F19 = FixedU64<19>;
/// [`FixedU64`] with 44 integer bits and 20 fractional bits.
pub type U44F20 = FixedU64<20>;
/// [`FixedU64`] with 43 integer bits and 21 fractional bits.
pub type U43F21 = FixedU64<21>;
/// [`FixedU64`] with 42 integer bits and 22 fractional bits.
pub type U42F22 = FixedU64<22>;
/// [`FixedU64`] with 41 integer bits and 23 fractional bits.
pub type U41F23 = FixedU64<23>;
/// [`FixedU64`] with 40 integer bits and 24 fractional bits.
pub type U40F24 = FixedU64<24>;
/// [`FixedU64`] with 39 integer bits and 25 fractional bits.
pub type U39F25 = FixedU64<25>;
/// [`FixedU64`] with 38 integer bits and 26 fractional bits.
pub type U38F26 = FixedU64<26>;
/// [`FixedU64`] with 37 integer bits and 27 fractional bits.
pub type U37F27 = FixedU64<27>;
/// [`FixedU64`] with 36 integer bits and 28 fractional bits.
pub type U36F28 = FixedU64<28>;
/// [`FixedU64`] with 35 integer bits and 29 fractional bits.
pub type U35F29 = FixedU64<29>;
/// [`FixedU64`] with 34 integer bits and 30 fractional bits.
pub type U34F30 = FixedU64<30>;
/// [`FixedU64`] with 33 integer bits and 31 fractional bits.
pub type U33F31 = FixedU64<31>;
/// [`FixedU64`] with 32 integer bits and 32 fractional bits.
pub type U32F32 = FixedU64<32>;
/// [`FixedU64`] with 31 integer bits and 33 fractional bits.
pub type U31F33 = FixedU64<33>;
/// [`FixedU64`] with 30 integer bits and 34 fractional bits.
pub type U30F34 = FixedU64<34>;
/// [`FixedU64`] with 29 integer bits and 35 fractional bits.
pub type U29F35 = FixedU64<35>;
/// [`FixedU64`] with 28 integer bits and 36 fractional bits.
pub type U28F36 = FixedU64<36>;
/// [`FixedU64`] with 27 integer bits and 37 fractional bits.
pub type U27F37 = FixedU64<37>;
/// [`FixedU64`] with 26 integer bits and 38 fractional bits.
pub type U26F38 = FixedU64<38>;
/// [`FixedU64`] with 25 integer bits and 39 fractional bits.
pub type U25F39 = FixedU64<39>;
/// [`FixedU64`] with 24 integer bits and 40 fractional bits.
pub type U24F40 = FixedU64<40>;
/// [`FixedU64`] with 23 integer bits and 41 fractional bits.
pub type U23F41 = FixedU64<41>;
/// [`FixedU64`] with 22 integer bits and 42 fractional bits.
pub type U22F42 = FixedU64<42>;
/// [`FixedU64`] with 21 integer bits and 43 fractional bits.
pub type U21F43 = FixedU64<43>;
/// [`FixedU64`] with 20 integer bits and 44 fractional bits.
pub type U20F44 = FixedU64<44>;
/// [`FixedU64`] with 19 integer bits and 45 fractional bits.
pub type U19F45 = FixedU64<45>;
/// [`FixedU64`] with 18 integer bits and 46 fractional bits.
pub type U18F46 = FixedU64<46>;
/// [`FixedU64`] with 17 integer bits and 47 fractional bits.
pub type U17F47 = FixedU64<47>;
/// [`FixedU64`] with 16 integer bits and 48 fractional bits.
pub type U16F48 = FixedU64<48>;
/// [`FixedU64`] with 15 integer bits and 49 fractional bits.
pub type U15F49 = FixedU64<49>;
/// [`FixedU64`] with 14 integer bits and 50 fractional bits.
pub type U14F50 = FixedU64<50>;
/// [`FixedU64`] with 13 integer bits and 51 fractional bits.
pub type U13F51 = FixedU64<51>;
/// [`FixedU64`] with 12 integer bits and 52 fractional bits.
pub type U12F52 = FixedU64<52>;
/// [`FixedU64`] with 11 integer bits and 53 fractional bits.
pub type U11F53 = FixedU64<53>;
/// [`FixedU64`] with 10 integer bits and 54 fractional bits.
pub type U10F54 = FixedU64<54>;
/// [`FixedU64`] with nine integer bits and 55 fractional bits.
pub type U9F55 = FixedU64<55>;
/// [`FixedU64`] with eight integer bits and 56 fractional bits.
pub type U8F56 = FixedU64<56>;
/// [`FixedU64`] with seven integer bits and 57 fractional bits.
pub type U7F57 = FixedU64<57>;
/// [`FixedU64`] with six integer bits and 58 fractional bits.
pub type U6F58 = FixedU64<58>;
/// [`FixedU64`] with five integer bits and 59 fractional bits.
pub type U5F59 = FixedU64<59>;
/// [`FixedU64`] with four integer bits and 60 fractional bits.
pub type U4F60 = FixedU64<60>;
/// [`FixedU64`] with three integer bits and 61 fractional bits.
pub type U3F61 = FixedU64<61>;
/// [`FixedU64`] with two integer bits and 62 fractional bits.
pub type U2F62 = FixedU64<62>;
/// [`FixedU64`] with one integer bit and 63 fractional bits.
pub type U1F63 = FixedU64<63>;
/// [`FixedU64`] with no integer bits and 64 fractional bits.
pub type U0F64 = FixedU64<64>;
/// [`FixedU128`] with 128 integer bits and no fractional bits.
pub type U128F0 = FixedU128<0>;
/// [`FixedU128`] with 127 integer bits and one fractional bit.
pub type U127F1 = FixedU128<1>;
/// [`FixedU128`] with 126 integer bits and two fractional bits.
pub type U126F2 = FixedU128<2>;
/// [`FixedU128`] with 125 integer bits and three fractional bits.
pub type U125F3 = FixedU128<3>;
/// [`FixedU128`] with 124 integer bits and four fractional bits.
pub type U124F4 = FixedU128<4>;
/// [`FixedU128`] with 123 integer bits and five fractional bits.
pub type U123F5 = FixedU128<5>;
/// [`FixedU128`] with 122 integer bits and six fractional bits.
pub type U122F6 = FixedU128<6>;
/// [`FixedU128`] with 121 integer bits and seven fractional bits.
pub type U121F7 = FixedU128<7>;
/// [`FixedU128`] with 120 integer bits and eight fractional bits.
pub type U120F8 = FixedU128<8>;
/// [`FixedU128`] with 119 integer bits and nine fractional bits.
pub type U119F9 = FixedU128<9>;
/// [`FixedU128`] with 118 integer bits and 10 fractional bits.
pub type U118F10 = FixedU128<10>;
/// [`FixedU128`] with 117 integer bits and 11 fractional bits.
pub type U117F11 = FixedU128<11>;
/// [`FixedU128`] with 116 integer bits and 12 fractional bits.
pub type U116F12 = FixedU128<12>;
/// [`FixedU128`] with 115 integer bits and 13 fractional bits.
pub type U115F13 = FixedU128<13>;
/// [`FixedU128`] with 114 integer bits and 14 fractional bits.
pub type U114F14 = FixedU128<14>;
/// [`FixedU128`] with 113 integer bits and 15 fractional bits.
pub type U113F15 = FixedU128<15>;
/// [`FixedU128`] with 112 integer bits and 16 fractional bits.
pub type U112F16 = FixedU128<16>;
/// [`FixedU128`] with 111 integer bits and 17 fractional bits.
pub type U111F17 = FixedU128<17>;
/// [`FixedU128`] with 110 integer bits and 18 fractional bits.
pub type U110F18 = FixedU128<18>;
/// [`FixedU128`] with 109 integer bits and 19 fractional bits.
pub type U109F19 = FixedU128<19>;
/// [`FixedU128`] with 108 integer bits and 20 fractional bits.
pub type U108F20 = FixedU128<20>;
/// [`FixedU128`] with 107 integer bits and 21 fractional bits.
pub type U107F21 = FixedU128<21>;
/// [`FixedU128`] with 106 integer bits and 22 fractional bits.
pub type U106F22 = FixedU128<22>;
/// [`FixedU128`] with 105 integer bits and 23 fractional bits.
pub type U105F23 = FixedU128<23>;
/// [`FixedU128`] with 104 integer bits and 24 fractional bits.
pub type U104F24 = FixedU128<24>;
/// [`FixedU128`] with 103 integer bits and 25 fractional bits.
pub type U103F25 = FixedU128<25>;
/// [`FixedU128`] with 102 integer bits and 26 fractional bits.
pub type U102F26 = FixedU128<26>;
/// [`FixedU128`] with 101 integer bits and 27 fractional bits.
pub type U101F27 = FixedU128<27>;
/// [`FixedU128`] with 100 integer bits and 28 fractional bits.
pub type U100F28 = FixedU128<28>;
/// [`FixedU128`] with 99 integer bits and 29 fractional bits.
pub type U99F29 = FixedU128<29>;
/// [`FixedU128`] with 98 integer bits and 30 fractional bits.
pub type U98F30 = FixedU128<30>;
/// [`FixedU128`] with 97 integer bits and 31 fractional bits.
pub type U97F31 = FixedU128<31>;
/// [`FixedU128`] with 96 integer bits and 32 fractional bits.
pub type U96F32 = FixedU128<32>;
/// [`FixedU128`] with 95 integer bits and 33 fractional bits.
pub type U95F33 = FixedU128<33>;
/// [`FixedU128`] with 94 integer bits and 34 fractional bits.
pub type U94F34 = FixedU128<34>;
/// [`FixedU128`] with 93 integer bits and 35 fractional bits.
pub type U93F35 = FixedU128<35>;
/// [`FixedU128`] with 92 integer bits and 36 fractional bits.
pub type U92F36 = FixedU128<36>;
/// [`FixedU128`] with 91 integer bits and 37 fractional bits.
pub type U91F37 = FixedU128<37>;
/// [`FixedU128`] with 90 integer bits and 38 fractional bits.
pub type U90F38 = FixedU128<38>;
/// [`FixedU128`] with 89 integer bits and 39 fractional bits.
pub type U89F39 = FixedU128<39>;
/// [`FixedU128`] with 88 integer bits and 40 fractional bits.
pub type U88F40 = FixedU128<40>;
/// [`FixedU128`] with 87 integer bits and 41 fractional bits.
pub type U87F41 = FixedU128<41>;
/// [`FixedU128`] with 86 integer bits and 42 fractional bits.
pub type U86F42 = FixedU128<42>;
/// [`FixedU128`] with 85 integer bits and 43 fractional bits.
pub type U85F43 = FixedU128<43>;
/// [`FixedU128`] with 84 integer bits and 44 fractional bits.
pub type U84F44 = FixedU128<44>;
/// [`FixedU128`] with 83 integer bits and 45 fractional bits.
pub type U83F45 = FixedU128<45>;
/// [`FixedU128`] with 82 integer bits and 46 fractional bits.
pub type U82F46 = FixedU128<46>;
/// [`FixedU128`] with 81 integer bits and 47 fractional bits.
pub type U81F47 = FixedU128<47>;
/// [`FixedU128`] with 80 integer bits and 48 fractional bits.
pub type U80F48 = FixedU128<48>;
/// [`FixedU128`] with 79 integer bits and 49 fractional bits.
pub type U79F49 = FixedU128<49>;
/// [`FixedU128`] with 78 integer bits and 50 fractional bits.
pub type U78F50 = FixedU128<50>;
/// [`FixedU128`] with 77 integer bits and 51 fractional bits.
pub type U77F51 = FixedU128<51>;
/// [`FixedU128`] with 76 integer bits and 52 fractional bits.
pub type U76F52 = FixedU128<52>;
/// [`FixedU128`] with 75 integer bits and 53 fractional bits.
pub type U75F53 = FixedU128<53>;
/// [`FixedU128`] with 74 integer bits and 54 fractional bits.
pub type U74F54 = FixedU128<54>;
/// [`FixedU128`] with 73 integer bits and 55 fractional bits.
pub type U73F55 = FixedU128<55>;
/// [`FixedU128`] with 72 integer bits and 56 fractional bits.
pub type U72F56 = FixedU128<56>;
/// [`FixedU128`] with 71 integer bits and 57 fractional bits.
pub type U71F57 = FixedU128<57>;
/// [`FixedU128`] with 70 integer bits and 58 fractional bits.
pub type U70F58 = FixedU128<58>;
/// [`FixedU128`] with 69 integer bits and 59 fractional bits.
pub type U69F59 = FixedU128<59>;
/// [`FixedU128`] with 68 integer bits and 60 fractional bits.
pub type U68F60 = FixedU128<60>;
/// [`FixedU128`] with 67 integer bits and 61 fractional bits.
pub type U67F61 = FixedU128<61>;
/// [`FixedU128`] with 66 integer bits and 62 fractional bits.
pub type U66F62 = FixedU128<62>;
/// [`FixedU128`] with 65 integer bits and 63 fractional bits.
pub type U65F63 = FixedU128<63>;
/// [`FixedU128`] with 64 integer bits and 64 fractional bits.
pub type U64F64 = FixedU128<64>;
/// [`FixedU128`] with 63 integer bits and 65 fractional bits.
pub type U63F65 = FixedU128<65>;
/// [`FixedU128`] with 62 integer bits and 66 fractional bits.
pub type U62F66 = FixedU128<66>;
/// [`FixedU128`] with 61 integer bits and 67 fractional bits.
pub type U61F67 = FixedU128<67>;
/// [`FixedU128`] with 60 integer bits and 68 fractional bits.
pub type U60F68 = FixedU128<68>;
/// [`FixedU128`] with 59 integer bits and 69 fractional bits.
pub type U59F69 = FixedU128<69>;
/// [`FixedU128`] with 58 integer bits and 70 fractional bits.
pub type U58F70 = FixedU128<70>;
/// [`FixedU128`] with 57 integer bits and 71 fractional bits.
pub type U57F71 = FixedU128<71>;
/// [`FixedU128`] with 56 integer bits and 72 fractional bits.
pub type U56F72 = FixedU128<72>;
/// [`FixedU128`] with 55 integer bits and 73 fractional bits.
pub type U55F73 = FixedU128<73>;
/// [`FixedU128`] with 54 integer bits and 74 fractional bits.
pub type U54F74 = FixedU128<74>;
/// [`FixedU128`] with 53 integer bits and 75 fractional bits.
pub type U53F75 = FixedU128<75>;
/// [`FixedU128`] with 52 integer bits and 76 fractional bits.
pub type U52F76 = FixedU128<76>;
/// [`FixedU128`] with 51 integer bits and 77 fractional bits.
pub type U51F77 = FixedU128<77>;
/// [`FixedU128`] with 50 integer bits and 78 fractional bits.
pub type U50F78 = FixedU128<78>;
/// [`FixedU128`] with 49 integer bits and 79 fractional bits.
pub type U49F79 = FixedU128<79>;
/// [`FixedU128`] with 48 integer bits and 80 fractional bits.
pub type U48F80 = FixedU128<80>;
/// [`FixedU128`] with 47 integer bits and 81 fractional bits.
pub type U47F81 = FixedU128<81>;
/// [`FixedU128`] with 46 integer bits and 82 fractional bits.
pub type U46F82 = FixedU128<82>;
/// [`FixedU128`] with 45 integer bits and 83 fractional bits.
pub type U45F83 = FixedU128<83>;
/// [`FixedU128`] with 44 integer bits and 84 fractional bits.
pub type U44F84 = FixedU128<84>;
/// [`FixedU128`] with 43 integer bits and 85 fractional bits.
pub type U43F85 = FixedU128<85>;
/// [`FixedU128`] with 42 integer bits and 86 fractional bits.
pub type U42F86 = FixedU128<86>;
/// [`FixedU128`] with 41 integer bits and 87 fractional bits.
pub type U41F87 = FixedU128<87>;
/// [`FixedU128`] with 40 integer bits and 88 fractional bits.
pub type U40F88 = FixedU128<88>;
/// [`FixedU128`] with 39 integer bits and 89 fractional bits.
pub type U39F89 = FixedU128<89>;
/// [`FixedU128`] with 38 integer bits and 90 fractional bits.
pub type U38F90 = FixedU128<90>;
/// [`FixedU128`] with 37 integer bits and 91 fractional bits.
pub type U37F91 = FixedU128<91>;
/// [`FixedU128`] with 36 integer bits and 92 fractional bits.
pub type U36F92 = FixedU128<92>;
/// [`FixedU128`] with 35 integer bits and 93 fractional bits.
pub type U35F93 = FixedU128<93>;
/// [`FixedU128`] with 34 integer bits and 94 fractional bits.
pub type U34F94 = FixedU128<94>;
/// [`FixedU128`] with 33 integer bits and 95 fractional bits.
pub type U33F95 = FixedU128<95>;
/// [`FixedU128`] with 32 integer bits and 96 fractional bits.
pub type U32F96 = FixedU128<96>;
/// [`FixedU128`] with 31 integer bits and 97 fractional bits.
pub type U31F97 = FixedU128<97>;
/// [`FixedU128`] with 30 integer bits and 98 fractional bits.
pub type U30F98 = FixedU128<98>;
/// [`FixedU128`] with 29 integer bits and 99 fractional bits.
pub type U29F99 = FixedU128<99>;
/// [`FixedU128`] with 28 integer bits and 100 fractional bits.
pub type U28F100 = FixedU128<100>;
/// [`FixedU128`] with 27 integer bits and 101 fractional bits.
pub type U27F101 = FixedU128<101>;
/// [`FixedU128`] with 26 integer bits and 102 fractional bits.
pub type U26F102 = FixedU128<102>;
/// [`FixedU128`] with 25 integer bits and 103 fractional bits.
pub type U25F103 = FixedU128<103>;
/// [`FixedU128`] with 24 integer bits and 104 fractional bits.
pub type U24F104 = FixedU128<104>;
/// [`FixedU128`] with 23 integer bits and 105 fractional bits.
pub type U23F105 = FixedU128<105>;
/// [`FixedU128`] with 22 integer bits and 106 fractional bits.
pub type U22F106 = FixedU128<106>;
/// [`FixedU128`] with 21 integer bits and 107 fractional bits.
pub type U21F107 = FixedU128<107>;
/// [`FixedU128`] with 20 integer bits and 108 fractional bits.
pub type U20F108 = FixedU128<108>;
/// [`FixedU128`] with 19 integer bits and 109 fractional bits.
pub type U19F109 = FixedU128<109>;
/// [`FixedU128`] with 18 integer bits and 110 fractional bits.
pub type U18F110 = FixedU128<110>;
/// [`FixedU128`] with 17 integer bits and 111 fractional bits.
pub type U17F111 = FixedU128<111>;
/// [`FixedU128`] with 16 integer bits and 112 fractional bits.
pub type U16F112 = FixedU128<112>;
/// [`FixedU128`] with 15 integer bits and 113 fractional bits.
pub type U15F113 = FixedU128<113>;
/// [`FixedU128`] with 14 integer bits and 114 fractional bits.
pub type U14F114 = FixedU128<114>;
/// [`FixedU128`] with 13 integer bits and 115 fractional bits.
pub type U13F115 = FixedU128<115>;
/// [`FixedU128`] with 12 integer bits and 116 fractional bits.
pub type U12F116 = FixedU128<116>;
/// [`FixedU128`] with 11 integer bits and 117 fractional bits.
pub type U11F117 = FixedU128<117>;
/// [`FixedU128`] with 10 integer bits and 118 fractional bits.
pub type U10F118 = FixedU128<118>;
/// [`FixedU128`] with nine integer bits and 119 fractional bits.
pub type U9F119 = FixedU128<119>;
/// [`FixedU128`] with eight integer bits and 120 fractional bits.
pub type U8F120 = FixedU128<120>;
/// [`FixedU128`] with seven integer bits and 121 fractional bits.
pub type U7F121 = FixedU128<121>;
/// [`FixedU128`] with six integer bits and 122 fractional bits.
pub type U6F122 = FixedU128<122>;
/// [`FixedU128`] with five integer bits and 123 fractional bits.
pub type U5F123 = FixedU128<123>;
/// [`FixedU128`] with four integer bits and 124 fractional bits.
pub type U4F124 = FixedU128<124>;
/// [`FixedU128`] with three integer bits and 125 fractional bits.
pub type U3F125 = FixedU128<125>;
/// [`FixedU128`] with two integer bits and 126 fractional bits.
pub type U2F126 = FixedU128<126>;
/// [`FixedU128`] with one integer bit and 127 fractional bits.
pub type U1F127 = FixedU128<127>;
/// [`FixedU128`] with no integer bits and 128 fractional bits.
pub type U0F128 = FixedU128<128>;
