// The lane-wise port of the generic backend (see `generic.rs`) to `float64x2_t`,
// the counterpart of `x86_64/lanewise.rs`: the fast paths that do not involve a
// product, and the helpers that `fma.rs` builds the others from.
//
// Masks have all bits of a lane set for true, and none for false.

use super::{add_rn, all, and, constant, eq, extract, gt, lt, neg, or, sub_rn, F64X2};
use crate::simd::generic;
use std::{arch::aarch64::*, mem::transmute};

/// `add_ru([x0, x1], [y0, y1]) = [x0 + y0, x1 + y1]` rounded toward +∞.
pub(crate) fn add_ru(x: F64X2, y: F64X2) -> F64X2 {
    // See `generic::add1_ru_fast`.
    let s = add_rn(x, y);
    let e = two_sum_err(x, y, s);
    // `generic::add1_ru_fast`'s check is: x or y is not finite, or both have
    // exponents <= 1022 and s is finite. The last part is implied: |x|, |y| <=
    // 2^1023 - 2^970 gives |x + y| <= 2^1024 - 2^971 = MAX. So the check fails
    // exactly where the larger exponent is 1023 (it is 1024 for ±∞ and NaN).
    let slow = max_exponent_eq(x, y, 1023);
    // `generic::add1_ru_fast` also requires x and y to be finite, which e > 0
    // implies: if x or y is ±∞ or NaN, s is ±∞ or NaN, and then s - y or s - a is
    // NaN or ∞ - ∞, so e is NaN. If s overflows, e is NaN as well, and the lane is
    // slow.
    let up = gt(e, zero());
    // Where the lane is not slow and e > 0, s is finite, and it is not ±0: x + y is
    // inexact, and a sum below 2^-1022 in magnitude is a multiple of 2^-1074, so
    // exact. The slow lanes are recomputed.
    or_generic_slow(slow, step_up_where(up, s), || {
        generic::add_ru(extract(x), extract(y))
    })
}

/// `sqrt1_ru(x) = √x` rounded toward +∞.
pub(crate) fn sqrt1_ru(x: f64) -> f64 {
    generic::sqrt1_ru(x)
}

/// `sub_ru([x0, x1], [y0, y1]) = [x0 - y0, x1 - y1]` rounded toward +∞.
pub(crate) fn sub_ru(x: F64X2, y: F64X2) -> F64X2 {
    // x - y is defined as x + (-y) by IEEE 754, including the signs of zeros.
    add_ru(x, neg(y))
}

/// `sub1_ru(x, y) = x - y` rounded toward +∞.
pub(crate) fn sub1_ru(x: f64, y: f64) -> f64 {
    generic::sub1_ru(x, y)
}

// The operations with the rounding mode switched in FPCR, as independent
// references for the differential tests. This is how the backend rounded before
// it computed the rounding explicitly. The whole of FPCR is written: RMode
// (bits 23:22) is RM or RP, and FZ, DN and the trap enables are cleared, which
// is the default environment on Linux and macOS.
#[cfg(test)]
macro_rules! impl_op_round {
    ($t:ty, $f:ident ($x:ident $(,$y:ident)*), $inst:literal, rd) => {
        impl_op_round!($t, $f ($x $(,$y)*), $inst, 0x800000);
    };

    ($t:ty, $f:ident ($x:ident $(,$y:ident)*), $inst:literal, ru) => {
        impl_op_round!($t, $f ($x $(,$y)*), $inst, 0x400000);
    };

    ($t:ty, $f:ident ($x:ident $(,$y:ident)*), $inst:literal, $fpcr:literal) => {
        pub(crate) fn $f(mut $x: $t, $($y: $t,)*) -> $t {
            unsafe {
                std::arch::asm!(
                    "mrs {fpcr_bak}, fpcr",
                    "msr fpcr, {fpcr:x}",
                    $inst,
                    "msr fpcr, {fpcr_bak}",
                    $x = inout(vreg) $x,
                    $($y = in(vreg) $y,)*
                    fpcr = in(reg) $fpcr,
                    fpcr_bak = out(reg) _,
                    options(pure, nomem, nostack, preserves_flags)
                );
            }
            $x
        }
    };
}

#[cfg(test)]
impl_op_round!(f64, sqrt1_rd_fpcr(x), "fsqrt {x:d}, {x:d}", rd);
#[cfg(test)]
impl_op_round!(f64, sqrt1_ru_fpcr(x), "fsqrt {x:d}, {x:d}", ru);
#[cfg(test)]
impl_op_round!(f64, sub1_ru_fpcr(x, y), "fsub {x:d}, {x:d}, {y:d}", ru);
#[cfg(test)]
impl_op_round!(F64X2, add_ru_fpcr(x, y), "fadd.2d {x:v}, {x:v}, {y:v}", ru);
#[cfg(test)]
impl_op_round!(F64X2, sub_ru_fpcr(x, y), "fsub.2d {x:v}, {x:v}, {y:v}", ru);
#[cfg(test)]
impl_op_round!(F64X2, mul_ru_fpcr(x, y), "fmul.2d {x:v}, {x:v}, {y:v}", ru);
#[cfg(test)]
impl_op_round!(F64X2, div_ru_fpcr(x, y), "fdiv.2d {x:v}, {x:v}, {y:v}", ru);

/// `mul_add_ru_fpcr([x0, x1], [y0, y1], [z0, z1]) = [x0 * y0 + z0, x1 * y1 + z1]`
/// rounded toward +∞ (with a single rounding), with the rounding mode switched.
#[cfg(test)]
pub(crate) fn mul_add_ru_fpcr(x: F64X2, y: F64X2, mut z: F64X2) -> F64X2 {
    unsafe {
        std::arch::asm!(
            "mrs {fpcr_bak}, fpcr",
            "msr fpcr, {fpcr:x}",
            "fmla.2d {z:v}, {x:v}, {y:v}",
            "msr fpcr, {fpcr_bak}",
            x = in(vreg) x,
            y = in(vreg) y,
            z = inout(vreg) z,
            fpcr = in(reg) 0x400000,
            fpcr_bak = out(reg) _,
            options(pure, nomem, nostack, preserves_flags)
        );
    }
    z
}

// Lane-wise versions of the helpers of the generic backend.

pub(super) fn zero() -> F64X2 {
    unsafe { vdupq_n_f64(0.0) }
}

/// The mask of lane 0 alone.
pub(super) fn lane0() -> F64X2 {
    unsafe { transmute([-1i64, 0]) }
}

/// `mul_rn([x0, x1], [y0, y1]) = [x0 * y0, x1 * y1]` rounded to nearest.
pub(super) fn mul_rn(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { vmulq_f64(x, y) }
}

/// `div_rn([x0, x1], [y0, y1]) = [x0 / y0, x1 / y1]` rounded to nearest.
pub(super) fn div_rn(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { vdivq_f64(x, y) }
}

/// `sqrt_rn([x0, x1]) = [√x0, √x1]` rounded to nearest.
pub(super) fn sqrt_rn(x: F64X2) -> F64X2 {
    unsafe { vsqrtq_f64(x) }
}

/// `select(m, x, y)` takes the lanes of x where m is set, and those of y elsewhere.
/// `vbslq_f64` selects bit by bit, so m must be all ones or all zeros per lane, as
/// every mask here is.
pub(super) fn select(m: F64X2, x: F64X2, y: F64X2) -> F64X2 {
    unsafe { vbslq_f64(vreinterpretq_u64_f64(m), x, y) }
}

/// `andnot(x, y) = x & !y`.
pub(super) fn andnot(x: F64X2, y: F64X2) -> F64X2 {
    unsafe {
        vreinterpretq_f64_u64(vbicq_u64(
            vreinterpretq_u64_f64(x),
            vreinterpretq_u64_f64(y),
        ))
    }
}

pub(super) fn not(x: F64X2) -> F64X2 {
    // NEON's bitwise NOT has no 64-bit lane form; the lane width does not matter.
    unsafe { vreinterpretq_f64_u32(vmvnq_u32(vreinterpretq_u32_f64(x))) }
}

/// `xor(x, y) = x ^ y`.
pub(super) fn xor(x: F64X2, y: F64X2) -> F64X2 {
    unsafe {
        vreinterpretq_f64_u64(veorq_u64(
            vreinterpretq_u64_f64(x),
            vreinterpretq_u64_f64(y),
        ))
    }
}

// Operations on the lanes as 64-bit integers.

pub(super) fn splat_i64(x: i64) -> F64X2 {
    unsafe { vreinterpretq_f64_s64(vdupq_n_s64(x)) }
}

pub(super) fn add_i64(x: F64X2, y: F64X2) -> F64X2 {
    unsafe {
        vreinterpretq_f64_s64(vaddq_s64(
            vreinterpretq_s64_f64(x),
            vreinterpretq_s64_f64(y),
        ))
    }
}

pub(super) fn sub_i64(x: F64X2, y: F64X2) -> F64X2 {
    unsafe {
        vreinterpretq_f64_s64(vsubq_s64(
            vreinterpretq_s64_f64(x),
            vreinterpretq_s64_f64(y),
        ))
    }
}

pub(super) fn gt_i64(x: F64X2, y: F64X2) -> F64X2 {
    unsafe {
        vreinterpretq_f64_u64(vcgtq_s64(
            vreinterpretq_s64_f64(x),
            vreinterpretq_s64_f64(y),
        ))
    }
}

// Returns `r` if the fast path is valid in both lanes (`ok`), and otherwise the
// result of the generic backend, which recomputes the lanes that are not.
pub(super) fn or_generic(ok: F64X2, r: F64X2, generic: impl FnOnce() -> [f64; 2]) -> F64X2 {
    if all(ok) {
        r
    } else {
        cold_generic(generic)
    }
}

// Returns `r` unless the fast path is invalid in a lane (`slow`, with a 32-bit
// lane per lane of r, as `vmovn_u64` of a mask has), and otherwise the result of
// the generic backend. Testing the complement of `ok` saves the comparison with
// all ones that `all` needs.
pub(super) fn or_generic_slow(
    slow: uint32x2_t,
    r: F64X2,
    generic: impl FnOnce() -> [f64; 2],
) -> F64X2 {
    if unsafe { transmute::<uint32x2_t, u64>(slow) } != 0 {
        cold_generic(generic)
    } else {
        r
    }
}

// The fallback of `or_generic` and `or_generic_slow`. Marking it cold keeps the
// calls of the generic backend, and the registers they need saved, off the fast
// path of the callers into which LLVM then inlines the fast path.
#[cold]
fn cold_generic(generic: impl FnOnce() -> [f64; 2]) -> F64X2 {
    let [r0, r1] = generic();
    constant(r0, r1)
}

// The biased exponents of the lanes of x as u64 lanes: the unbiased exponent
// plus 1023, that is, floor(log2(|x|)) + 1023 if x is normal, 0 if x is zero or
// subnormal, and 2047 if x is infinite or NaN. The comparisons below add 1023 to
// their bounds instead of subtracting it from every exponent.
fn biased_exponent(x: F64X2) -> uint64x2_t {
    // Shifting left by one drops the sign bit.
    unsafe { vshrq_n_u64::<53>(vshlq_n_u64::<1>(vreinterpretq_u64_f64(x))) }
}

fn splat_u64(x: i64) -> uint64x2_t {
    unsafe { vdupq_n_u64(x as u64) }
}

// The lanes where lo <= the unbiased exponent of x <= hi, with one unsigned
// comparison: below lo, the subtraction wraps around to more than hi - lo.
pub(super) fn exponent_in(x: F64X2, lo: i64, hi: i64) -> F64X2 {
    unsafe {
        let d = vsubq_u64(biased_exponent(x), splat_u64(lo + 1023));
        vreinterpretq_f64_u64(vcleq_u64(d, splat_u64(hi - lo)))
    }
}

// The lanes where the larger of the unbiased exponents of x and y is e, taking
// 1024 as the exponent of ±∞ and NaN, as `biased_exponent` does. The mask has a
// 32-bit lane per lane of x, as `vmovn_u64` of a mask has, for `or_generic_slow`.
pub(super) fn max_exponent_eq(x: F64X2, y: F64X2, e: i64) -> uint32x2_t {
    unsafe {
        // After shifting out the sign bit, the upper 32 bits of a lane are the 11
        // bits of the biased exponent followed by 21 bits of the significand, so
        // the larger of two upper words as u32 has the larger exponent (NEON has no
        // 64-bit integer maximum). The lower words are dropped.
        let a = vreinterpretq_u32_u64(vshlq_n_u64::<1>(vreinterpretq_u64_f64(x)));
        let b = vreinterpretq_u32_u64(vshlq_n_u64::<1>(vreinterpretq_u64_f64(y)));
        let m = vmaxq_u32(a, b);
        // The exponent field is compared in place: in 32-bit lanes, both constants
        // take one `mvni` for e = 1023, whereas in 64-bit lanes each takes a `mov`
        // and a `dup` (LLVM turns a shift and a comparison into this form anyway).
        let field = vandq_u32(m, vdupq_n_u32(!0 << 21));
        let c = vceqq_u32(field, vdupq_n_u32(((e + 1023) as u32) << 21));
        vshrn_n_u64::<32>(vreinterpretq_u64_u32(c))
    }
}

pub(super) fn is_finite(x: F64X2) -> F64X2 {
    // |x| < +∞, one comparison of absolute values (`facgt`); false for NaN.
    unsafe { vreinterpretq_f64_u64(vcaltq_f64(x, vdupq_n_f64(f64::INFINITY))) }
}

// The lanes where x or y is ±0, ±∞ or NaN, for which the product and the
// quotient in the default rounding mode are exact.
pub(super) fn is_special(x: F64X2, y: F64X2) -> F64X2 {
    or(
        not(and(is_finite(x), is_finite(y))),
        or(eq(x, zero()), eq(y, zero())),
    )
}

/// Returns the successors of the lanes of x where m is set, and the other lanes of
/// x as they are. The lanes where m is set must be finite and must not be -0.
/// Shorter than `select(m, step_up(x), x)` with the `step_up` of
/// `x86_64/lanewise.rs`, which also steps ±0 up: one comparison and no select,
/// against three comparisons and two selects.
pub(super) fn step_up_where(m: F64X2, x: F64X2) -> F64X2 {
    // As integers, m and n = (x < 0) are -1 or 0, and b is the bit pattern of x.
    // b - (m ^ n) + n is b where m = 0. Where m = -1, it is b + 1 if x >= +0 (+0
    // goes to 2^-1074, MAX to +∞), and b - 1 if x < 0 (-2^-1074 goes to -0): in
    // both cases the next float up. At -0 it would be b + 1, -2^-1074, which the
    // precondition excludes. n is a float comparison rather than the sign bit
    // (`vcltzq_s64`), because LLVM turns b + (b >> 63) into `ssra`, which
    // overwrites its operand and costs a copy of b.
    let n = lt(x, zero());
    add_i64(sub_i64(x, xor(m, n)), n)
}

/// Returns the error e = (x + y) - s, where s = RN(x + y). See `generic::two_sum_err`.
pub(super) fn two_sum_err(x: F64X2, y: F64X2, s: F64X2) -> F64X2 {
    let a = sub_rn(s, y);
    let b = sub_rn(s, a);
    add_rn(sub_rn(x, a), sub_rn(y, b))
}
