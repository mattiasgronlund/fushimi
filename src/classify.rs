use crate::{interval::Interval, simd::*};
use std::mem::transmute;

// `classify_bits(x) = (bitmask(le(*x, splat(0.0))) << 2) | bitmask(ge(*x, splat(0.0)))`,
// computed by the build's backend: the code of the class of the interval whose `rep` is `*x` (see
// `IntervalClass`). Each `bitmask` is below 4, so the casts to `u8` keep the values, and the
// result is below 16.
//
// It is the `classify_bits` of `Baseline` (`src/simd/token.rs`), except in the x86-64 builds with
// neither `docsrs` nor `force-generic`, where this function is not compiled: there `Baseline`,
// like the copies of `V2`, `V3` and `V4` in every build that has them, calls the `classify_bits` of
// `src/simd/x86_64.rs`, which computes the same class code with one `movmskps`. These are the
// builds whose backend is one of that file (`sse42`, `fma` or `avx512f`), and those without
// `sse4.2`, such as a build for plain `x86-64`, whose backend is the portable one. The body is
// here, in a function that is not generic, rather than in `Interval::classify_with` with the
// methods `bitmask`, `ge` and `le` of `Baseline`: in a build for plain `x86-64` in which
// `Baseline` called this function, as it now does there only with `docsrs` or `force-generic`,
// rustc 1.98.1 compiled that generic body with the portable `bitmask`, `ge` and `le` to a mask
// in a vector register whose sign bits were read back, at 11 more instructions per call of
// `classify` and 21 more per call of `classify2` than this body, which it compiled to a flag per
// lane's comparison (`ucomisd` and `setae`).
//
// `x` is a reference: with `x: F64X2`, rustc 1.98.1 compiled `<Interval as Mul>::mul` and
// `<Interval as Div>::div` of a build for plain `x86-64` with the feature `force-generic` so that
// they copied each operand to the stack and read its lanes from the copy, at 1 to 7 more
// instructions per call in the classes counted. With `x: &F64X2`, they read the lanes from the
// operand.
//
// The `cfg` is that of the `classify_bits` of `Baseline` that calls this function: the complement
// of the union of the `cfg`s of the two that call the one of `src/simd/x86_64.rs`, as `build.rs`
// sets `fushimi_generic_backend` wherever `force-generic` is on.
#[cfg(not(all(target_arch = "x86_64", not(feature = "force-generic"), not(docsrs))))]
#[inline]
pub(crate) fn classify_bits(x: &F64X2) -> u8 {
    // `rocq/theories/Model.v` transcribes this function in `classify`, its transcription of
    // `Interval::classify_with`, for the proofs listed on `classify_with`.
    let x = *x;
    let zero = splat(0.0);
    let ge_zero = bitmask(ge(x, zero)) as u8;
    let le_zero = bitmask(le(x, zero)) as u8;
    (le_zero << 2) | ge_zero
}

impl Interval {
    // The class of `self`, computed by the backend of `s`, as the `*_with` methods that call it
    // compute the rest of their result.
    //
    // `#[inline]` lets a `*_with` method instantiated in a user's crate inline this function
    // and `classify2_with`, and with them the backend functions of `s` into a region of
    // `vectorize` (`src/simd/token.rs`). Without it on `classify` and `classify2`, which took
    // no token before, a `V3` region in a build for plain `x86-64` called `classify2` out of line
    // in every `mul_with`.
    #[inline]
    pub(crate) fn classify_with<S: Simd>(self, s: S) -> IntervalClass {
        // `rocq/theories/Model.v` transcribes this function for an `s` whose backend is the
        // portable one and whose `classify_bits` is the one above: every `s` whose backend is
        // the portable one but `Baseline` and `CrateBaseline` in an x86-64 build without
        // `sse4.2`, such as one for plain `x86-64`, and without the feature `force-generic`,
        // whose `classify_bits` is that of `src/simd/x86_64.rs`. It does so for the proofs of
        // `(Dec)Interval::abs`, `(Dec)Interval::atan2`, `(Dec)Interval::div`, `(Dec)Interval::mul`,
        // `(Dec)Interval::mul_add`, `(Dec)Interval::mul_rev_to_pair`, `(Dec)Interval::powi`,
        // `(Dec)Interval::recip` and `(Dec)Interval::sqr`. For such an `s`, `classify_defined` in
        // `rocq/theories/Abs.v` shows, for the portable backend, that `transmute` gets the
        // discriminant of a variant whenever `self` is `valid`, as the comment on
        // `Interval::rep` defines it.
        unsafe { transmute(s.classify_bits(&self.rep)) }
    }

    // `#[inline]`, for the reason given on `classify_with`.
    #[inline]
    pub(crate) fn classify2_with<S: Simd>(self, s: S, rhs: Self) -> IntervalClass2 {
        // `rocq/theories/Model.v` transcribes this function for an `s` for which it transcribes
        // `classify_with`, for the proofs of `(Dec)Interval::atan2`, `(Dec)Interval::div`,
        // `(Dec)Interval::mul`, `(Dec)Interval::mul_add` and `(Dec)Interval::mul_rev_to_pair`.
        // `classify2_pair` in `rocq/theories/Classify2.v` shows that `transmute` gets the
        // discriminant of the variant for the classes of `self` and `rhs` whenever
        // `classify_with` is defined on both, for such an `s`.
        unsafe { transmute(((self.classify_with(s) as u8) << 4) | rhs.classify_with(s) as u8) }
    }

    // `classify_with` called with `Baseline`, whose backend is the build's, for the operations
    // that have no `*_with` form, such as `Interval::abs`. `rocq/theories/Model.v` transcribes it
    // as `classify_with`, in a build where `Baseline` is an `s` for which it transcribes
    // `classify_with`: one whose backend is the portable one, but not an x86-64 build without
    // `sse4.2` and without the feature `force-generic`. So it has to be updated along with it.
    #[inline]
    pub(crate) fn classify(self) -> IntervalClass {
        self.classify_with(Baseline)
    }

    // `classify2_with` called with `Baseline`, as `classify` calls `classify_with`.
    #[inline]
    pub(crate) fn classify2(self, rhs: Self) -> IntervalClass2 {
        self.classify2_with(Baseline, rhs)
    }
}

// The following codes are used to represent the class of an interval:
//
//  Code | Description
// ------+---------------
//     E | Empty
//     M | a < 0 < b
//    N0 | a < 0 ∧ b = 0
//    N1 | b < 0
//    P0 | a = 0 ∧ 0 < b
//    P1 | 0 < a
//     Z | a = b = 0
//    N* | a < 0 ∧ b ≤ 0
//    P* | a = 0 ∧ 0 ≤ b
// * These codes are used only in comments.

// `rocq/theories/Model.v` transcribes the discriminants in `transmute_class`, for the
// proofs of `(Dec)Interval::abs`, `(Dec)Interval::atan2`, `(Dec)Interval::div`,
// `(Dec)Interval::mul`, `(Dec)Interval::mul_add`, `(Dec)Interval::mul_rev_to_pair`,
// `(Dec)Interval::powi`, `(Dec)Interval::recip` and `(Dec)Interval::sqr`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub(crate) enum IntervalClass {
    // Each bit represents b ≤ 0, -a ≤ 0, b ≥ 0 and -a ≥ 0, respectively.
    E = 0b0000,  // empty
    M = 0b0011,  // b > 0 ∧ -a > 0
    N0 = 0b1011, // b = 0 ∧ -a > 0
    N1 = 0b1001, // b < 0 ∧ -a > 0
    P0 = 0b0111, // b > 0 ∧ -a = 0
    P1 = 0b0110, // b > 0 ∧ -a < 0
    Z = 0b1111,  // b = 0 ∧ -a = 0
}

macro_rules! discr {
    ($x:ident, $y:ident) => {
        ((IntervalClass::$x as u8) << 4) | IntervalClass::$y as u8
    };
}

// `rocq/theories/Model.v` transcribes the discriminants in `transmute_class2`, with the
// variant `X_Y` as the pair of the variants `X` and `Y` of `IntervalClass`, for the
// proofs of `(Dec)Interval::atan2`, `(Dec)Interval::div`, `(Dec)Interval::mul`,
// `(Dec)Interval::mul_add` and `(Dec)Interval::mul_rev_to_pair`.
#[allow(dead_code)]
#[allow(non_camel_case_types)] // We could rename E_E to ExE, etc., but that would degrade the legibility.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub(crate) enum IntervalClass2 {
    E_E = discr!(E, E),
    E_M = discr!(E, M),
    E_N0 = discr!(E, N0),
    E_N1 = discr!(E, N1),
    E_P0 = discr!(E, P0),
    E_P1 = discr!(E, P1),
    E_Z = discr!(E, Z),

    M_E = discr!(M, E),
    M_M = discr!(M, M),
    M_N0 = discr!(M, N0),
    M_N1 = discr!(M, N1),
    M_P0 = discr!(M, P0),
    M_P1 = discr!(M, P1),
    M_Z = discr!(M, Z),

    N0_E = discr!(N0, E),
    N0_M = discr!(N0, M),
    N0_N0 = discr!(N0, N0),
    N0_N1 = discr!(N0, N1),
    N0_P0 = discr!(N0, P0),
    N0_P1 = discr!(N0, P1),
    N0_Z = discr!(N0, Z),

    N1_E = discr!(N1, E),
    N1_M = discr!(N1, M),
    N1_N0 = discr!(N1, N0),
    N1_N1 = discr!(N1, N1),
    N1_P0 = discr!(N1, P0),
    N1_P1 = discr!(N1, P1),
    N1_Z = discr!(N1, Z),

    P0_E = discr!(P0, E),
    P0_M = discr!(P0, M),
    P0_N0 = discr!(P0, N0),
    P0_N1 = discr!(P0, N1),
    P0_P0 = discr!(P0, P0),
    P0_P1 = discr!(P0, P1),
    P0_Z = discr!(P0, Z),

    P1_E = discr!(P1, E),
    P1_M = discr!(P1, M),
    P1_N0 = discr!(P1, N0),
    P1_N1 = discr!(P1, N1),
    P1_P0 = discr!(P1, P0),
    P1_P1 = discr!(P1, P1),
    P1_Z = discr!(P1, Z),

    Z_E = discr!(Z, E),
    Z_M = discr!(Z, M),
    Z_N0 = discr!(Z, N0),
    Z_N1 = discr!(Z, N1),
    Z_P0 = discr!(Z, P0),
    Z_P1 = discr!(Z, P1),
    Z_Z = discr!(Z, Z),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;
    use Interval as I;

    #[test]
    fn classify() {
        use IntervalClass::*;
        assert_eq!(I::EMPTY.classify(), E);
        assert_eq!(I::ENTIRE.classify(), M);
        assert_eq!(const_interval!(-1.0, 1.0).classify(), M);
        assert_eq!(const_interval!(-1.0, 0.0).classify(), N0);
        assert_eq!(const_interval!(-1.0, -1.0).classify(), N1);
        assert_eq!(const_interval!(0.0, 1.0).classify(), P0);
        assert_eq!(const_interval!(1.0, 1.0).classify(), P1);
        assert_eq!(I::zero().classify(), Z);
    }
}
