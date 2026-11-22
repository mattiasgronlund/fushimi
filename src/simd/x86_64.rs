use std::{arch::x86_64::*, mem::transmute};

pub(crate) const HAS_MAXIMUM: bool = false;

pub(crate) type F64X2 = __m128d;

#[inline(always)]
pub(crate) fn abs(x: F64X2) -> F64X2 {
    // Drop sign bits.
    unsafe { _mm_andnot_pd(splat(-0.0), x) }
}

/// `add_rn([x0, x1], [y0, y1]) = [x0 + y0, x1 + y1]` rounded to nearest.
#[inline(always)]
pub(crate) fn add_rn(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_add_pd(x, y) }
}

#[inline(always)]
pub(crate) fn all(x: F64X2) -> bool {
    bitmask(x) == 3
}

#[inline(always)]
pub(crate) fn and(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_and_pd(x, y) }
}

#[inline(always)]
pub(crate) fn any(x: F64X2) -> bool {
    bitmask(x) != 0
}

#[inline(always)]
pub(crate) fn bitmask(x: F64X2) -> u32 {
    unsafe { _mm_movemask_pd(x) as u32 }
}

#[inline(always)]
pub(crate) fn ceil(x: F64X2) -> F64X2 {
    unsafe { _mm_ceil_pd(x) }
}

/// `classify_bits(x) = (bitmask(le(x, splat(0.0))) << 2) | bitmask(ge(x, splat(0.0)))`, the code
/// of the class of the interval whose `rep` is `x`, as `crate::classify::classify_bits` computes
/// it, with one `movmskps` in place of the two `movmskpd` of `bitmask`.
// `_mm_shuffle_ps(ge, le, 0xdd)` is [ge[63:32], ge[127:96], le[63:32], le[127:96]]: the upper
// halves of the lanes of the two masks, whose sign bits are bits 63 of the lanes, which
// `_mm_movemask_ps` reads into bits 0 to 3. With `avx`, rustc 1.98.1 compiled the two `movmskpd`
// of `crate::classify::classify_bits` to one `vmovmskpd` of a 256-bit register that it filled with
// `vinsertf128`, both in the builds for Haswell and `x86-64-v4` and in the copies of `V3`. As that
// left the upper halves of the `ymm` registers in use, LLVM then put a `vzeroupper` before the
// calls and returns of the operations that classify, such as `Interval::mul`, which cost a
// call of `Interval::mul` 2 instructions in a build for Haswell, and one of `Interval::mul_with`
// at `V3` 1 in a build for `x86-64` (cachegrind, row 150). This body takes no `ymm` register
// there. Without `avx`, it compiled the two `movmskpd` to `packssdw` and one `movmskps`, as many
// instructions as this body.
#[inline(always)]
pub(super) fn classify_bits(x: F64X2) -> u8 {
    let zero = splat(0.0);
    let ge_zero = unsafe { _mm_castpd_ps(ge(x, zero)) };
    let le_zero = unsafe { _mm_castpd_ps(le(x, zero)) };
    unsafe { _mm_movemask_ps(_mm_shuffle_ps(ge_zero, le_zero, 0xdd)) as u8 }
}

#[inline(always)]
pub(crate) fn constant(x: f64, y: f64) -> F64X2 {
    unsafe { transmute([x, y]) }
}

#[inline(always)]
pub(crate) fn eq(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_cmpeq_pd(x, y) }
}

#[inline(always)]
pub(crate) fn extract(x: F64X2) -> [f64; 2] {
    unsafe { transmute::<F64X2, [f64; 2]>(x) }
}

#[inline(always)]
pub(crate) fn extract0(x: F64X2) -> f64 {
    unsafe { transmute::<F64X2, [f64; 2]>(x)[0] }
}

// This is slower than extract0, which usually turns into a no-op.
#[inline(always)]
pub(crate) fn extract1(x: F64X2) -> f64 {
    unsafe { transmute::<F64X2, [f64; 2]>(x)[1] }
}

#[inline(always)]
pub(crate) fn floor(x: F64X2) -> F64X2 {
    unsafe { _mm_floor_pd(x) }
}

#[inline(always)]
pub(crate) fn ge(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_cmpge_pd(x, y) }
}

#[inline(always)]
pub(crate) fn gt(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_cmpgt_pd(x, y) }
}

/// `hadd_rn([x0, x1], [y0, y1]) = [x0 + x1, y0 + y1]` rounded to nearest.
#[inline(always)]
pub(crate) fn hadd_rn(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_hadd_pd(x, y) }
}

#[inline(always)]
pub(crate) fn le(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_cmple_pd(x, y) }
}

#[inline(always)]
pub(crate) fn lt(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_cmplt_pd(x, y) }
}

// The vector version of `x > y ? x : y`, lane by lane: `_mm_max_pd` returns the lane of `y` where
// either lane is a NaN, and where both are zeros, so it differs from the `maximumNumber` operation
// of IEEE 754-2019 (`generic::max`) where only the lane of `y` is a NaN, and where that of `x` is
// +0 and that of `y` is -0. Its callers handle empty intervals before it, or want a NaN for them
// (`mag`).
#[inline(always)]
pub(crate) fn max(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_max_pd(x, y) }
}

// The vector version of the `maximum` operation defined in IEEE 754-2019,
// which propagates NaNs.
#[inline(always)]
pub(crate) fn maximum(_x: F64X2, _y: F64X2) -> F64X2 {
    unimplemented!()
}

#[inline(always)]
pub(crate) fn min(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_min_pd(x, y) }
}

#[inline(always)]
pub(crate) fn minimum(_x: F64X2, _y: F64X2) -> F64X2 {
    unimplemented!()
}

#[inline(always)]
pub(crate) fn neg(x: F64X2) -> F64X2 {
    xor(splat(-0.0), x)
}

#[inline(always)]
pub(crate) fn neg0(x: F64X2) -> F64X2 {
    unsafe { xor(x, _mm_set_sd(-0.0)) }
}

#[inline(always)]
pub(crate) fn or(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_or_pd(x, y) }
}

// This one is hard to implement correctly.
// https://www.cockroachlabs.com/blog/rounding-implementations-in-go/
#[inline(always)]
pub(crate) fn round(x: F64X2) -> F64X2 {
    constant(extract0(x).round(), extract1(x).round())
}

#[inline(always)]
pub(crate) fn round_ties_even(x: F64X2) -> F64X2 {
    unsafe { _mm_round_pd(x, _MM_FROUND_TO_NEAREST_INT | _MM_FROUND_NO_EXC) }
}

/// `shuffle02([x0, x1], [x2, x3]) = [x0, x2]`
#[inline(always)]
pub(crate) fn shuffle02(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_shuffle_pd(x, y, 0) }
}

/// `shuffle03([x0, x1], [x2, x3]) = [x0, x3]`
#[inline(always)]
pub(crate) fn shuffle03(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_shuffle_pd(x, y, 2) }
}

/// `shuffle13([x0, x1], [x2, x3]) = [x1, x3]`
#[inline(always)]
pub(crate) fn shuffle13(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_shuffle_pd(x, y, 3) }
}

#[inline(always)]
pub(crate) fn splat(x: f64) -> F64X2 {
    unsafe { transmute([x, x]) }
}

/// `sub_rn([x0, x1], [y0, y1]) = [x0 - y0, x1 - y1]` rounded to nearest.
#[inline(always)]
pub(crate) fn sub_rn(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_sub_pd(x, y) }
}

#[inline(always)]
pub(crate) fn swap(x: F64X2) -> F64X2 {
    shuffle12(x, x)
}

#[inline(always)]
pub(crate) fn trunc(x: F64X2) -> F64X2 {
    unsafe { _mm_round_pd(x, _MM_FROUND_TO_ZERO | _MM_FROUND_NO_EXC) }
}

/// `shuffle12([x0, x1], [x2, x3]) = [x1, x2]`
#[inline(always)]
fn shuffle12(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_shuffle_pd(x, y, 1) }
}

#[inline(always)]
fn xor(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_xor_pd(x, y) }
}

cfg_if::cfg_if! {
    if #[cfg(target_feature = "avx512f")] {
        mod avx512f;
        pub(crate) use avx512f::*;
    } else if #[cfg(all(target_feature = "avx", target_feature = "fma"))] {
        mod lanewise;
        mod fma;
        pub(crate) use fma::*;

        // With the feature `avx512`, the backend of the token `V4` (`src/simd/token.rs`), whose
        // copies of the functions below compile it with the target features of `x86-64-v4`.
        #[cfg(feature = "avx512")]
        #[allow(dead_code, unused_imports)] // Only what those copies call is used.
        pub(super) mod avx512f;

        // The vectors of this build are those of the backends: the copies take them as they are.
        // Only those of `V4` call these.
        #[cfg(feature = "avx512")]
        #[inline(always)]
        pub(super) fn to_m128d(x: F64X2) -> __m128d {
            x
        }

        #[cfg(feature = "avx512")]
        #[inline(always)]
        pub(super) fn from_m128d(x: __m128d) -> F64X2 {
            x
        }
    } else if #[cfg(target_feature = "sse4.2")] {
        mod lanewise;
        mod sse42;
        pub(crate) use sse42::*;

        // The backends of the tokens `V3` and, with the feature `avx512`, `V4`
        // (`src/simd/token.rs`), whose copies of the functions below compile them with the target
        // features of `x86-64-v3` and `x86-64-v4`.
        #[allow(dead_code, unused_imports)] // Only what those copies call is used.
        pub(super) mod fma;
        #[cfg(feature = "avx512")]
        #[allow(dead_code, unused_imports)] // Only what those copies call is used.
        pub(super) mod avx512f;

        // The vectors of this build are those of the backends: the copies take them as they are.
        #[inline(always)]
        pub(super) fn to_m128d(x: F64X2) -> __m128d {
            x
        }

        #[inline(always)]
        pub(super) fn from_m128d(x: __m128d) -> F64X2 {
            x
        }
    } else {
        // Plain `x86-64`, without `sse4.2`: `src/simd.rs` takes the portable backend, and
        // compiles this module as the backends of the tokens `V2`, `V3` and, with the feature
        // `avx512`, `V4` (`src/simd/token.rs`), whose copies of the functions below compile them
        // with the target features of `x86-64-v2`, `x86-64-v3` and `x86-64-v4`, and for the
        // `classify_bits` above, which the `classify_bits` of `Baseline` calls in place of that
        // of `src/classify.rs`: its intrinsics are of SSE and SSE2, which every x86-64 CPU has.
        mod lanewise;
        pub(super) mod sse42;
        pub(super) mod fma;
        #[cfg(feature = "avx512")]
        pub(super) mod avx512f;

        // The vectors of this build, `[f64; 2]`, to and from those of the backends.
        #[inline(always)]
        pub(super) fn to_m128d(x: [f64; 2]) -> __m128d {
            constant(x[0], x[1])
        }

        #[inline(always)]
        pub(super) fn from_m128d(x: __m128d) -> [f64; 2] {
            extract(x)
        }
    }
}
