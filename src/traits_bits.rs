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
    traits::{Fixed, FixedEquiv},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use az::{
    Cast, CastFrom, CheckedCast, CheckedCastFrom, OverflowingCast, OverflowingCastFrom,
    SaturatingCast, SaturatingCastFrom, UnwrappedCast, UnwrappedCastFrom, WrappingCast,
    WrappingCastFrom,
};
#[cfg(feature = "borsh")]
use borsh::{BorshDeserialize, BorshSerialize};
use bytemuck::{Contiguous, Pod};
use core::{
    fmt::{Binary, Debug, Display, LowerExp, LowerHex, Octal, UpperExp, UpperHex},
    hash::Hash,
    iter::{Product, Sum},
    num::ParseIntError,
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div,
        DivAssign, Mul, MulAssign, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
    str::FromStr,
};
#[cfg(feature = "num-traits")]
use num_traits::{
    cast::{AsPrimitive, FromPrimitive},
    int::PrimInt,
    ops::{
        checked::{CheckedNeg, CheckedRem, CheckedShl, CheckedShr},
        euclid::{CheckedEuclid, Euclid},
        mul_add::{MulAdd, MulAddAssign},
        overflowing::{OverflowingAdd, OverflowingMul, OverflowingSub},
        saturating::{SaturatingAdd, SaturatingMul, SaturatingSub},
        wrapping::{WrappingAdd, WrappingMul, WrappingNeg, WrappingShl, WrappingShr, WrappingSub},
    },
    Num, NumAssignRef, NumRef,
};
#[cfg(feature = "serde")]
use serde::{de::Deserialize, ser::Serialize};

macro_rules! impl_bits {
    ($Bits:ident, $Fixed:ident) => {
        impl FixedBits for $Bits {
            type Fixed<const FRAC: i32> = $Fixed<FRAC>;
            const MIN: $Bits = $Bits::MIN;
            const MAX: $Bits = $Bits::MAX;
            const IS_SIGNED: bool = $Bits::MIN != 0;
            const BITS: u32 = $Bits::BITS;
        }
        impl Sealed for $Bits {}
        impl FixedBitsCast<i8> for $Bits {}
        impl FixedBitsCast<i16> for $Bits {}
        impl FixedBitsCast<i32> for $Bits {}
        impl FixedBitsCast<i64> for $Bits {}
        impl FixedBitsCast<i128> for $Bits {}
        impl FixedBitsCast<isize> for $Bits {}
        impl FixedBitsCast<u8> for $Bits {}
        impl FixedBitsCast<u16> for $Bits {}
        impl FixedBitsCast<u32> for $Bits {}
        impl FixedBitsCast<u64> for $Bits {}
        impl FixedBitsCast<u128> for $Bits {}
        impl FixedBitsCast<usize> for $Bits {}
        impl FixedBitsOptionalArbitrary for $Bits {}
        impl FixedBitsOptionalBorsh for $Bits {}
        impl FixedBitsOptionalNum for $Bits {}
        impl FixedBitsOptionalSerde for $Bits {}
    };
}

/// This trait is implemented for <code>[Fixed]::[Bits]</code> for all
/// fixed-point numbers.
///
/// This provides some facilities to manipulate bits in generic functions.
///
/// This trait is sealed and cannot be implemented for more types; it is
/// implemented for [`i8`], [`i16`], [`i32`], [`i64`], [`i128`], [`u8`],
/// [`u16`], [`u32`], [`u64`], and [`u128`].
///
/// # Examples
///
/// ```rust
/// use az::OverflowingAs;
/// use fixed::{traits::Fixed, types::*};
/// fn limited_positive_bits<F: Fixed>(fixed: F) -> Option<u32> {
///     let bits = fixed.to_bits();
///     match bits.overflowing_as::<u32>() {
///         (wrapped, false) => Some(wrapped),
///         (_, true) => None,
///     }
/// }
/// assert_eq!(limited_positive_bits(I16F16::from_bits(100)), Some(100));
/// assert_eq!(limited_positive_bits(I16F16::from_bits(-100)), None);
/// ```
///
/// [Bits]: crate::traits::Fixed::Bits
/// [Fixed]: crate::traits::Fixed
pub trait FixedBits: Sealed
where
    Self: Default + Hash + Ord,
    Self: Contiguous + Pod,
    Self: Debug + Display + LowerExp + UpperExp,
    Self: Binary + Octal + LowerHex + UpperHex,
    Self: FromStr<Err = ParseIntError>,
    Self: Add<Output = Self> + AddAssign,
    Self: Sub<Output = Self> + SubAssign,
    Self: Mul<Output = Self> + MulAssign,
    Self: Div<Output = Self> + DivAssign,
    Self: Rem<Output = Self> + RemAssign,
    Self: Not<Output = Self>,
    Self: BitAnd<Output = Self> + BitAndAssign,
    Self: BitOr<Output = Self> + BitOrAssign,
    Self: BitXor<Output = Self> + BitXorAssign,
    Self: Shl<u32, Output = Self> + ShlAssign<u32>,
    Self: Shr<u32, Output = Self> + ShrAssign<u32>,
    Self: Sum + Product,
    Self: FixedEquiv<Equiv = Self::Fixed<0>>,
    Self: FixedBitsCast<i8> + FixedBitsCast<i16> + FixedBitsCast<i32>,
    Self: FixedBitsCast<i64> + FixedBitsCast<i128> + FixedBitsCast<isize>,
    Self: FixedBitsCast<u8> + FixedBitsCast<u16> + FixedBitsCast<u32>,
    Self: FixedBitsCast<u64> + FixedBitsCast<u128> + FixedBitsCast<usize>,
    Self: FixedBitsOptionalArbitrary,
    Self: FixedBitsOptionalBorsh,
    Self: FixedBitsOptionalNum,
    Self: FixedBitsOptionalSerde,
{
    /// A fixed-point number with this type as the underlying bit representation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// #![feature(generic_const_exprs)]
    /// # #![allow(incomplete_features)]
    ///
    /// use fixed::{
    ///     traits::{Fixed, FixedBits},
    ///     types::I4F4,
    /// };
    ///
    /// fn op<F: Fixed>(f: F) -> F {
    ///     let num = F::Bits::try_from(64).ok().unwrap();
    ///     // a requires more than 4 integer bits
    ///     let a = <F::Bits as FixedBits>::Fixed::<0>::TRY_ONE.unwrap() * num;
    ///     // b requires more than 4 fractional bits
    ///     let b = <F::Bits as FixedBits>::Fixed::<6>::TRY_ONE.unwrap() / num;
    ///
    ///     // a * b = 1, so this effectively returns f + 1
    ///     f.add_prod(a, b)
    /// }
    ///
    /// assert_eq!(op(I4F4::from_num(2.5)), 3.5);
    /// ```
    type Fixed<const FRAC: i32>: Fixed<Bits = Self>;

    /// The smallest value that can be represented by this integer type.
    const MIN: Self;

    /// The largest value that can be represented by this integer type.
    const MAX: Self;

    /// [`true`] if this integer type is signed.
    const IS_SIGNED: bool;

    /// The size of this integer type in bits.
    const BITS: u32;
}

/// This trait is used to provide supertraits to the [`FixedBits`] trait, and
/// should not be used directly.
pub trait FixedBitsCast<Prim>
where
    Self: TryInto<Prim> + TryFrom<Prim>,
    Self: Cast<Prim> + CastFrom<Prim>,
    Self: CheckedCast<Prim> + CheckedCastFrom<Prim>,
    Self: SaturatingCast<Prim> + SaturatingCastFrom<Prim>,
    Self: WrappingCast<Prim> + WrappingCastFrom<Prim>,
    Self: UnwrappedCast<Prim> + UnwrappedCastFrom<Prim>,
    Self: OverflowingCast<Prim> + OverflowingCastFrom<Prim>,
    Self: Sealed,
{
}

pub trait Sealed {}

impl_bits! { i8, FixedI8 }
impl_bits! { i16, FixedI16 }
impl_bits! { i32, FixedI32 }
impl_bits! { i64, FixedI64 }
impl_bits! { i128, FixedI128 }
impl_bits! { u8, FixedU8 }
impl_bits! { u16, FixedU16 }
impl_bits! { u32, FixedU32 }
impl_bits! { u64, FixedU64 }
impl_bits! { u128, FixedU128 }

#[cfg(not(feature = "arbitrary"))]
/// This trait is used to provide supertraits to the [`FixedBits`] trait
/// depending on the crates’s [optional features], and should not be used
/// directly.
///
/// If the `arbitrary` feature is enabled, [`Arbitrary`] is a supertrait of
/// [`FixedBits`].
///
/// [optional features]: crate#optional-features
pub trait FixedBitsOptionalArbitrary: Sealed {}

#[cfg(feature = "arbitrary")]
/// This trait is used to provide supertraits to the [`FixedBits`] trait
/// depending on the crates’s [optional features], and should not be used
/// directly.
///
/// If the `arbitrary` feature is enabled, [`Arbitrary`] is a supertrait of
/// [`FixedBits`].
///
/// [optional features]: crate#optional-features
pub trait FixedBitsOptionalArbitrary: Sealed
where
    Self: for<'a> Arbitrary<'a>,
{
}

#[cfg(not(feature = "borsh"))]
/// This trait is used to provide supertraits to the [`FixedBits`] trait
/// depending on the crates’s [optional features], and should not be used
/// directly.
///
/// If the `borsh` experimental feature is enabled, [`BorshSerialize`] and
/// [`BorshDeserialize`] are supertraits of [`FixedBits`].
///
/// [optional features]: crate#optional-features
pub trait FixedBitsOptionalBorsh: Sealed {}

#[cfg(feature = "borsh")]
/// This trait is used to provide supertraits to the [`FixedBits`] trait
/// depending on the crates’s [optional features], and should not be used
/// directly.
///
/// If the `borsh` experimental feature is enabled, [`BorshSerialize`] and
/// [`BorshDeserialize`] are supertraits of [`FixedBits`].
///
/// [optional features]: crate#optional-features
pub trait FixedBitsOptionalBorsh: Sealed
where
    Self: BorshSerialize + BorshDeserialize,
{
}

#[cfg(not(feature = "num-traits"))]
/// This trait is used to provide supertraits to the [`FixedBits`] trait
/// depending on the crates’s [optional features], and should not be used
/// directly.
///
/// If the [`num-traits` experimental feature][experimental features] is
/// enabled, the following are supertraits of [`FixedBits`]:
///
///   * [`PrimInt`], [`FromPrimitive`]
///   * <code>[AsPrimitive][`AsPrimitive`]&lt;T></code> where `T` can be [`i8`],
///     [`i16`], [`i32`], [`i64`], [`i128`], [`isize`], [`u8`], [`u16`],
///     [`u32`], [`u64`], [`u128`], [`usize`], [`f32`] or [`f64`]
///   * [`CheckedNeg`], [`CheckedRem`], [`CheckedShl`], [`CheckedShr`]
///   * [`SaturatingAdd`], [`SaturatingSub`], [`SaturatingMul`]
///   * [`WrappingAdd`], [`WrappingSub`], [`WrappingNeg`], [`WrappingMul`],
///     [`WrappingShl`], [`WrappingShr`]
///   * [`OverflowingAdd`], [`OverflowingSub`], [`OverflowingMul`]
///   * [`Euclid`], [`CheckedEuclid`]
///   * [`MulAdd`], [`MulAddAssign`]
///
/// [experimental features]: crate#experimental-optional-features
/// [optional features]: crate#optional-features
pub trait FixedBitsOptionalNum: Sealed {}

#[cfg(feature = "num-traits")]
/// This trait is used to provide supertraits to the [`FixedBits`] trait
/// depending on the crates’s [optional features], and should not be used
/// directly.
///
/// If the [`num-traits` experimental feature][experimental features] is
/// enabled, the following are supertraits of [`FixedBits`]:
///
///   * [`Num`], [`NumRef`], [`NumAssignRef`]
///   * [`PrimInt`], [`FromPrimitive`]
///   * <code>[AsPrimitive][`AsPrimitive`]&lt;T></code> where `T` can be [`i8`],
///     [`i16`], [`i32`], [`i64`], [`i128`], [`isize`], [`u8`], [`u16`],
///     [`u32`], [`u64`], [`u128`], [`usize`], [`f32`] or [`f64`]
///   * [`CheckedNeg`], [`CheckedRem`], [`CheckedShl`], [`CheckedShr`]
///   * [`SaturatingAdd`], [`SaturatingSub`], [`SaturatingMul`]
///   * [`WrappingAdd`], [`WrappingSub`], [`WrappingNeg`], [`WrappingMul`],
///     [`WrappingShl`], [`WrappingShr`]
///   * [`OverflowingAdd`], [`OverflowingSub`], [`OverflowingMul`]
///   * [`Euclid`], [`CheckedEuclid`]
///   * [`MulAdd`], [`MulAddAssign`]
///
/// [experimental features]: crate#experimental-optional-features
/// [optional features]: crate#optional-features
pub trait FixedBitsOptionalNum: Sealed
where
    Self: Num<FromStrRadixErr = ParseIntError> + NumRef + NumAssignRef,
    Self: PrimInt + FromPrimitive,
    Self: AsPrimitive<i8> + AsPrimitive<i16> + AsPrimitive<i32>,
    Self: AsPrimitive<i64> + AsPrimitive<i128> + AsPrimitive<isize>,
    Self: AsPrimitive<u8> + AsPrimitive<u16> + AsPrimitive<u32>,
    Self: AsPrimitive<u64> + AsPrimitive<u128> + AsPrimitive<usize>,
    Self: AsPrimitive<f32> + AsPrimitive<f64>,
    Self: CheckedNeg + CheckedRem + CheckedShl + CheckedShr,
    Self: SaturatingAdd + SaturatingSub + SaturatingMul,
    Self: WrappingAdd + WrappingSub + WrappingNeg + WrappingMul,
    Self: WrappingShl + WrappingShr,
    Self: OverflowingAdd + OverflowingSub + OverflowingMul,
    Self: Euclid + CheckedEuclid,
    Self: MulAdd + MulAddAssign,
{
}

#[cfg(not(feature = "serde"))]
/// This trait is used to provide supertraits to the [`FixedBits`] trait
/// depending on the crates’s [optional features], and should not be used
/// directly.
///
/// If the `serde` feature is enabled, [`Serialize`] and [`Deserialize`] are
/// supertraits of [`FixedBits`].
///
/// [optional features]: crate#optional-features
pub trait FixedBitsOptionalSerde: Sealed {}

#[cfg(feature = "serde")]
/// This trait is used to provide supertraits to the [`FixedBits`] trait
/// depending on the crates’s [optional features], and should not be used
/// directly.
///
/// If the `serde` feature is enabled, [`Serialize`] and [`Deserialize`] are
/// supertraits of [`FixedBits`].
///
/// [optional features]: crate#optional-features
pub trait FixedBitsOptionalSerde: Sealed
where
    Self: Serialize + for<'de> Deserialize<'de>,
{
}
