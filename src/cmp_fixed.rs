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
use core::cmp::Ordering;

// Works by converting the signed number to unsigned, but does not change size
// of either number.
macro_rules! diff_sign {
    ($Sig:ident($Uns:ident, $UnsInner:ident), $OtherUns:ident) => {
        impl<const FRAC_LHS: i32, const FRAC_RHS: i32> PartialEq<$Sig<FRAC_RHS>>
            for $OtherUns<FRAC_LHS>
        {
            #[inline]
            fn eq(&self, rhs: &$Sig<FRAC_RHS>) -> bool {
                if rhs.is_negative() {
                    return false;
                }
                let unsigned_rhs = $Uns::<FRAC_RHS>::from_bits(rhs.to_bits() as $UnsInner);
                PartialEq::eq(self, &unsigned_rhs)
            }
        }

        impl<const FRAC_LHS: i32, const FRAC_RHS: i32> PartialEq<$OtherUns<FRAC_RHS>>
            for $Sig<FRAC_LHS>
        {
            #[inline]
            fn eq(&self, rhs: &$OtherUns<FRAC_RHS>) -> bool {
                if self.is_negative() {
                    return false;
                }
                let unsigned_lhs = $Uns::<FRAC_LHS>::from_bits(self.to_bits() as $UnsInner);
                PartialEq::eq(&unsigned_lhs, rhs)
            }
        }

        impl<const FRAC_LHS: i32, const FRAC_RHS: i32> PartialOrd<$Sig<FRAC_RHS>>
            for $OtherUns<FRAC_LHS>
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$Sig<FRAC_RHS>) -> Option<Ordering> {
                if rhs.is_negative() {
                    return Some(Ordering::Greater);
                }
                let unsigned_rhs = $Uns::<FRAC_RHS>::from_bits(rhs.to_bits() as $UnsInner);
                PartialOrd::partial_cmp(self, &unsigned_rhs)
            }

            #[inline]
            fn lt(&self, rhs: &$Sig<FRAC_RHS>) -> bool {
                if rhs.is_negative() {
                    return false;
                }
                let unsigned_rhs = $Uns::<FRAC_RHS>::from_bits(rhs.to_bits() as $UnsInner);
                PartialOrd::lt(self, &unsigned_rhs)
            }

            #[inline]
            fn le(&self, rhs: &$Sig<FRAC_RHS>) -> bool {
                if rhs.is_negative() {
                    return false;
                }
                let unsigned_rhs = $Uns::<FRAC_RHS>::from_bits(rhs.to_bits() as $UnsInner);
                PartialOrd::le(self, &unsigned_rhs)
            }

            #[inline]
            fn gt(&self, rhs: &$Sig<FRAC_RHS>) -> bool {
                if rhs.is_negative() {
                    return true;
                }
                let unsigned_rhs = $Uns::<FRAC_RHS>::from_bits(rhs.to_bits() as $UnsInner);
                PartialOrd::gt(self, &unsigned_rhs)
            }

            #[inline]
            fn ge(&self, rhs: &$Sig<FRAC_RHS>) -> bool {
                if rhs.is_negative() {
                    return true;
                }
                let unsigned_rhs = $Uns::<FRAC_RHS>::from_bits(rhs.to_bits() as $UnsInner);
                PartialOrd::ge(self, &unsigned_rhs)
            }
        }

        impl<const FRAC_LHS: i32, const FRAC_RHS: i32> PartialOrd<$OtherUns<FRAC_RHS>>
            for $Sig<FRAC_LHS>
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$OtherUns<FRAC_RHS>) -> Option<Ordering> {
                if self.is_negative() {
                    return Some(Ordering::Less);
                }
                let unsigned_lhs = $Uns::<FRAC_LHS>::from_bits(self.to_bits() as $UnsInner);
                PartialOrd::partial_cmp(&unsigned_lhs, rhs)
            }

            #[inline]
            fn lt(&self, rhs: &$OtherUns<FRAC_RHS>) -> bool {
                if self.is_negative() {
                    return true;
                }
                let unsigned_lhs = $Uns::<FRAC_LHS>::from_bits(self.to_bits() as $UnsInner);
                PartialOrd::lt(&unsigned_lhs, rhs)
            }

            #[inline]
            fn le(&self, rhs: &$OtherUns<FRAC_RHS>) -> bool {
                if self.is_negative() {
                    return true;
                }
                let unsigned_lhs = $Uns::<FRAC_LHS>::from_bits(self.to_bits() as $UnsInner);
                PartialOrd::le(&unsigned_lhs, rhs)
            }

            #[inline]
            fn gt(&self, rhs: &$OtherUns<FRAC_RHS>) -> bool {
                if self.is_negative() {
                    return false;
                }
                let unsigned_lhs = $Uns::<FRAC_LHS>::from_bits(self.to_bits() as $UnsInner);
                PartialOrd::gt(&unsigned_lhs, rhs)
            }

            #[inline]
            fn ge(&self, rhs: &$OtherUns<FRAC_RHS>) -> bool {
                if self.is_negative() {
                    return false;
                }
                let unsigned_lhs = $Uns::<FRAC_LHS>::from_bits(self.to_bits() as $UnsInner);
                PartialOrd::ge(&unsigned_lhs, rhs)
            }
        }
    };

    ($Sig:ident($Uns:ident, $UnsInner:ident)) => {
        diff_sign! { $Sig($Uns, $UnsInner), FixedU8 }
        diff_sign! { $Sig($Uns, $UnsInner), FixedU16 }
        diff_sign! { $Sig($Uns, $UnsInner), FixedU32 }
        diff_sign! { $Sig($Uns, $UnsInner), FixedU64 }
        diff_sign! { $Sig($Uns, $UnsInner), FixedU128 }
    };
}

diff_sign! { FixedI8(FixedU8, u8) }
diff_sign! { FixedI16(FixedU16, u16) }
diff_sign! { FixedI32(FixedU32, u32) }
diff_sign! { FixedI64(FixedU64, u64) }
diff_sign! { FixedI128(FixedU128, u128) }

// Both numbers must have the same sign (both signed or both unsigned). Works by
// widening the narrow number to have the same width as the wide number.
macro_rules! diff_size {
    ($Nar:ident, $Wid:ident($WidInner:ident)) => {
        impl<const FRAC_LHS: i32, const FRAC_RHS: i32> PartialEq<$Nar<FRAC_RHS>>
            for $Wid<FRAC_LHS>
        {
            #[inline]
            fn eq(&self, rhs: &$Nar<FRAC_RHS>) -> bool {
                let widened_rhs = $Wid::<FRAC_RHS>::from_bits(rhs.to_bits() as $WidInner);
                PartialEq::eq(self, &widened_rhs)
            }
        }

        impl<const FRAC_LHS: i32, const FRAC_RHS: i32> PartialEq<$Wid<FRAC_RHS>>
            for $Nar<FRAC_LHS>
        {
            #[inline]
            fn eq(&self, rhs: &$Wid<FRAC_RHS>) -> bool {
                let widened_lhs = $Wid::<FRAC_LHS>::from_bits(self.to_bits() as $WidInner);
                PartialEq::eq(&widened_lhs, rhs)
            }
        }

        impl<const FRAC_LHS: i32, const FRAC_RHS: i32> PartialOrd<$Nar<FRAC_RHS>>
            for $Wid<FRAC_LHS>
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$Nar<FRAC_RHS>) -> Option<Ordering> {
                let widened_rhs = $Wid::<FRAC_RHS>::from_bits(rhs.to_bits() as $WidInner);
                PartialOrd::partial_cmp(self, &widened_rhs)
            }

            #[inline]
            fn lt(&self, rhs: &$Nar<FRAC_RHS>) -> bool {
                let widened_rhs = $Wid::<FRAC_RHS>::from_bits(rhs.to_bits() as $WidInner);
                PartialOrd::lt(self, &widened_rhs)
            }

            #[inline]
            fn le(&self, rhs: &$Nar<FRAC_RHS>) -> bool {
                let widened_rhs = $Wid::<FRAC_RHS>::from_bits(rhs.to_bits() as $WidInner);
                PartialOrd::le(self, &widened_rhs)
            }

            #[inline]
            fn gt(&self, rhs: &$Nar<FRAC_RHS>) -> bool {
                let widened_rhs = $Wid::<FRAC_RHS>::from_bits(rhs.to_bits() as $WidInner);
                PartialOrd::gt(self, &widened_rhs)
            }

            #[inline]
            fn ge(&self, rhs: &$Nar<FRAC_RHS>) -> bool {
                let widened_rhs = $Wid::<FRAC_RHS>::from_bits(rhs.to_bits() as $WidInner);
                PartialOrd::ge(self, &widened_rhs)
            }
        }

        impl<const FRAC_LHS: i32, const FRAC_RHS: i32> PartialOrd<$Wid<FRAC_RHS>>
            for $Nar<FRAC_LHS>
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$Wid<FRAC_RHS>) -> Option<Ordering> {
                let widened_lhs = $Wid::<FRAC_LHS>::from_bits(self.to_bits() as $WidInner);
                PartialOrd::partial_cmp(&widened_lhs, rhs)
            }

            #[inline]
            fn lt(&self, rhs: &$Wid<FRAC_RHS>) -> bool {
                let widened_lhs = $Wid::<FRAC_LHS>::from_bits(self.to_bits() as $WidInner);
                PartialOrd::lt(&widened_lhs, rhs)
            }

            #[inline]
            fn le(&self, rhs: &$Wid<FRAC_RHS>) -> bool {
                let widened_lhs = $Wid::<FRAC_LHS>::from_bits(self.to_bits() as $WidInner);
                PartialOrd::le(&widened_lhs, rhs)
            }

            #[inline]
            fn gt(&self, rhs: &$Wid<FRAC_RHS>) -> bool {
                let widened_lhs = $Wid::<FRAC_LHS>::from_bits(self.to_bits() as $WidInner);
                PartialOrd::gt(&widened_lhs, rhs)
            }

            #[inline]
            fn ge(&self, rhs: &$Wid<FRAC_RHS>) -> bool {
                let widened_lhs = $Wid::<FRAC_LHS>::from_bits(self.to_bits() as $WidInner);
                PartialOrd::ge(&widened_lhs, rhs)
            }
        }
    };
}

diff_size! { FixedI8, FixedI16(i16) }
diff_size! { FixedI8, FixedI32(i32) }
diff_size! { FixedI8, FixedI64(i64) }
diff_size! { FixedI8, FixedI128(i128) }
diff_size! { FixedI16, FixedI32(i32) }
diff_size! { FixedI16, FixedI64(i64) }
diff_size! { FixedI16, FixedI128(i128) }
diff_size! { FixedI32, FixedI64(i64) }
diff_size! { FixedI32, FixedI128(i128) }
diff_size! { FixedI64, FixedI128(i128) }
diff_size! { FixedU8, FixedU16(u16) }
diff_size! { FixedU8, FixedU32(u32) }
diff_size! { FixedU8, FixedU64(u64) }
diff_size! { FixedU8, FixedU128(u128) }
diff_size! { FixedU16, FixedU32(u32) }
diff_size! { FixedU16, FixedU64(u64) }
diff_size! { FixedU16, FixedU128(u128) }
diff_size! { FixedU32, FixedU64(u64) }
diff_size! { FixedU32, FixedU128(u128) }
diff_size! { FixedU64, FixedU128(u128) }

macro_rules! cmp {
    ($Fixed:ident($Inner:ident)) => {
        impl<const FRAC_LHS: i32, const FRAC_RHS: i32> PartialEq<$Fixed<FRAC_RHS>>
            for $Fixed<FRAC_LHS>
        {
            #[inline]
            fn eq(&self, rhs: &$Fixed<FRAC_RHS>) -> bool {
                let lhs = self.to_bits();
                let rhs = rhs.to_bits();

                // lhs_extra_frac and nbits are known exactly at compile time,
                // so with optimizations the branch is selected at compile time
                let lhs_extra_frac = FRAC_LHS.saturating_sub(FRAC_RHS);
                let nbits = $Inner::BITS as i32;

                if lhs_extra_frac <= -nbits {
                    let shifted_rhs = rhs >> (nbits - 1) >> 1;
                    let rhs_is_reduced = rhs != 0;
                    lhs == shifted_rhs && !rhs_is_reduced
                } else if lhs_extra_frac < 0 {
                    let shifted_rhs = rhs >> -lhs_extra_frac;
                    let rhs_is_reduced = rhs != (shifted_rhs << -lhs_extra_frac);
                    lhs == shifted_rhs && !rhs_is_reduced
                } else if lhs_extra_frac == 0 {
                    lhs == rhs
                } else if lhs_extra_frac < nbits {
                    let shifted_lhs = lhs >> lhs_extra_frac;
                    let lhs_is_reduced = lhs != (shifted_lhs << lhs_extra_frac);
                    shifted_lhs == rhs && !lhs_is_reduced
                } else {
                    let shifted_lhs = lhs >> (nbits - 1) >> 1;
                    let lhs_is_reduced = lhs != 0;
                    shifted_lhs == rhs && !lhs_is_reduced
                }
            }
        }

        impl<const FRAC_LHS: i32, const FRAC_RHS: i32> PartialOrd<$Fixed<FRAC_RHS>>
            for $Fixed<FRAC_LHS>
        {
            #[inline]
            fn partial_cmp(&self, rhs: &$Fixed<FRAC_RHS>) -> Option<Ordering> {
                let lhs = self.to_bits();
                let rhs = rhs.to_bits();

                // lhs_extra_frac and nbits are known exactly at compile time,
                // so with optimizations the branch is selected at compile time
                let lhs_extra_frac = FRAC_LHS.saturating_sub(FRAC_RHS);
                let nbits = $Inner::BITS as i32;
                if lhs_extra_frac <= -nbits {
                    let shifted_rhs = rhs >> (nbits - 1) >> 1;
                    let rhs_is_reduced = rhs != 0;
                    if lhs == shifted_rhs && rhs_is_reduced {
                        Some(Ordering::Less)
                    } else {
                        Some(Ord::cmp(&lhs, &shifted_rhs))
                    }
                } else if lhs_extra_frac < 0 {
                    let shifted_rhs = rhs >> -lhs_extra_frac;
                    let rhs_is_reduced = rhs != (shifted_rhs << -lhs_extra_frac);
                    if lhs == shifted_rhs && rhs_is_reduced {
                        Some(Ordering::Less)
                    } else {
                        Some(Ord::cmp(&lhs, &shifted_rhs))
                    }
                } else if lhs_extra_frac == 0 {
                    Some(Ord::cmp(&lhs, &rhs))
                } else if lhs_extra_frac < nbits {
                    let shifted_lhs = lhs >> lhs_extra_frac;
                    let lhs_is_reduced = lhs != (shifted_lhs << lhs_extra_frac);
                    if shifted_lhs == rhs && lhs_is_reduced {
                        Some(Ordering::Greater)
                    } else {
                        Some(Ord::cmp(&shifted_lhs, &rhs))
                    }
                } else {
                    let shifted_lhs = lhs >> (nbits - 1) >> 1;
                    let lhs_is_reduced = lhs != 0;
                    if shifted_lhs == rhs && lhs_is_reduced {
                        Some(Ordering::Greater)
                    } else {
                        Some(Ord::cmp(&shifted_lhs, &rhs))
                    }
                }
            }

            #[inline]
            fn lt(&self, rhs: &$Fixed<FRAC_RHS>) -> bool {
                let lhs = self.to_bits();
                let rhs = rhs.to_bits();

                // lhs_extra_frac and nbits are known exactly at compile time,
                // so with optimizations the branch is selected at compile time
                let lhs_extra_frac = FRAC_LHS.saturating_sub(FRAC_RHS);
                let nbits = $Inner::BITS as i32;
                if lhs_extra_frac <= -nbits {
                    let shifted_rhs = rhs >> (nbits - 1) >> 1;
                    let rhs_is_reduced = rhs != 0;
                    (lhs == shifted_rhs && rhs_is_reduced) || lhs < shifted_rhs
                } else if lhs_extra_frac < 0 {
                    let shifted_rhs = rhs >> -lhs_extra_frac;
                    let rhs_is_reduced = rhs != (shifted_rhs << -lhs_extra_frac);
                    (lhs == shifted_rhs && rhs_is_reduced) || lhs < shifted_rhs
                } else if lhs_extra_frac == 0 {
                    lhs < rhs
                } else if lhs_extra_frac < nbits {
                    let shifted_lhs = lhs >> lhs_extra_frac;
                    shifted_lhs < rhs
                } else {
                    let shifted_lhs = lhs >> (nbits - 1) >> 1;
                    shifted_lhs < rhs
                }
            }

            #[inline]
            fn le(&self, rhs: &$Fixed<FRAC_RHS>) -> bool {
                let lhs = self.to_bits();
                let rhs = rhs.to_bits();

                // lhs_extra_frac and nbits are known exactly at compile time,
                // so with optimizations the branch is selected at compile time
                let lhs_extra_frac = FRAC_LHS.saturating_sub(FRAC_RHS);
                let nbits = $Inner::BITS as i32;
                if lhs_extra_frac <= -nbits {
                    let shifted_rhs = rhs >> (nbits - 1) >> 1;
                    lhs <= shifted_rhs
                } else if lhs_extra_frac < 0 {
                    let shifted_rhs = rhs >> -lhs_extra_frac;
                    lhs <= shifted_rhs
                } else if lhs_extra_frac == 0 {
                    lhs <= rhs
                } else if lhs_extra_frac < nbits {
                    let shifted_lhs = lhs >> lhs_extra_frac;
                    let lhs_is_reduced = lhs != (shifted_lhs << lhs_extra_frac);
                    !(shifted_lhs == rhs && lhs_is_reduced) && shifted_lhs <= rhs
                } else {
                    let shifted_lhs = lhs >> (nbits - 1) >> 1;
                    let lhs_is_reduced = lhs != 0;
                    !(shifted_lhs == rhs && lhs_is_reduced) && shifted_lhs <= rhs
                }
            }

            #[inline]
            fn gt(&self, rhs: &$Fixed<FRAC_RHS>) -> bool {
                let lhs = self.to_bits();
                let rhs = rhs.to_bits();

                // lhs_extra_frac and nbits are known exactly at compile time,
                // so with optimizations the branch is selected at compile time
                let lhs_extra_frac = FRAC_LHS.saturating_sub(FRAC_RHS);
                let nbits = $Inner::BITS as i32;
                if lhs_extra_frac <= -nbits {
                    let shifted_rhs = rhs >> (nbits - 1) >> 1;
                    lhs > shifted_rhs
                } else if lhs_extra_frac < 0 {
                    let shifted_rhs = rhs >> -lhs_extra_frac;
                    lhs > shifted_rhs
                } else if lhs_extra_frac == 0 {
                    lhs > rhs
                } else if lhs_extra_frac < nbits {
                    let shifted_lhs = lhs >> lhs_extra_frac;
                    let lhs_is_reduced = lhs != (shifted_lhs << lhs_extra_frac);
                    (shifted_lhs == rhs && lhs_is_reduced) || shifted_lhs > rhs
                } else {
                    let shifted_lhs = lhs >> (nbits - 1) >> 1;
                    let lhs_is_reduced = lhs != 0;
                    (shifted_lhs == rhs && lhs_is_reduced) || shifted_lhs > rhs
                }
            }

            #[inline]
            fn ge(&self, rhs: &$Fixed<FRAC_RHS>) -> bool {
                let lhs = self.to_bits();
                let rhs = rhs.to_bits();

                // lhs_extra_frac and nbits are known exactly at compile time,
                // so with optimizations the branch is selected at compile time
                let lhs_extra_frac = FRAC_LHS.saturating_sub(FRAC_RHS);
                let nbits = $Inner::BITS as i32;
                if lhs_extra_frac <= -nbits {
                    let shifted_rhs = rhs >> (nbits - 1) >> 1;
                    let rhs_is_reduced = rhs != 0;
                    !(lhs == shifted_rhs && rhs_is_reduced) && lhs >= shifted_rhs
                } else if lhs_extra_frac < 0 {
                    let shifted_rhs = rhs >> -lhs_extra_frac;
                    let rhs_is_reduced = rhs != (shifted_rhs << -lhs_extra_frac);
                    !(lhs == shifted_rhs && rhs_is_reduced) && lhs >= shifted_rhs
                } else if lhs_extra_frac == 0 {
                    lhs >= rhs
                } else if lhs_extra_frac < nbits {
                    let shifted_lhs = lhs >> lhs_extra_frac;
                    shifted_lhs >= rhs
                } else {
                    let shifted_lhs = lhs >> (nbits - 1) >> 1;
                    shifted_lhs >= rhs
                }
            }
        }

        impl<const FRAC: i32> Eq for $Fixed<FRAC> {}

        impl<const FRAC: i32> Ord for $Fixed<FRAC> {
            #[inline]
            fn cmp(&self, rhs: &$Fixed<FRAC>) -> Ordering {
                let lhs = self.to_bits();
                let rhs = rhs.to_bits();
                Ord::cmp(&lhs, &rhs)
            }
        }
    };
}

cmp! { FixedI8(i8) }
cmp! { FixedI16(i16) }
cmp! { FixedI32(i32) }
cmp! { FixedI64(i64) }
cmp! { FixedI128(i128) }
cmp! { FixedU8(u8) }
cmp! { FixedU16(u16) }
cmp! { FixedU32(u32) }
cmp! { FixedU64(u64) }
cmp! { FixedU128(u128) }

#[cfg(test)]
mod tests {
    #[test]
    fn issue_57() {
        use crate::types::I80F48;
        let a: u64 = 66000;
        let b: u64 = 1000;
        assert!(I80F48::from(a) > b);
    }
}
