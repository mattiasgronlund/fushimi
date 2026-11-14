// The operations of the aarch64 backend that round toward +∞, the port of
// `x86_64/fma.rs` to NEON (Advanced SIMD, which Rust enables on its aarch64
// targets except the softfloat ones), whose fused operations `fmla` and `fmls`
// are the FMA.
//
// They compute the fast paths of the generic backend on both lanes at once, and
// the few inputs that fail their checks in either lane are recomputed by the
// generic backend (see `lanewise.rs`). The FMA makes the remainders of division
// and of the square root one instruction each, and the error of TwoProduct one
// instruction in `mul_ru`, which uses its negation, and two in `mul_add_ru` (see
// `two_prod_err`). As on x86-64, `mul_ru` computes RU(x * y) itself where x and
// y are nonzero and |RN(x * y)| < 2^-968 (see `mul_ru_tiny`).
//
// The obvious alternative is to let the hardware round: `fadd` and friends with
// FPCR.RMode set to round toward +∞. That is what this backend replaced: every
// directed operation saved FPCR, set the rounding mode and restored it. On an
// Apple M1 Pro, a dot product of two 3-vectors of intervals, building the
// intervals included, took 141.0 ns that way and 44.1 ns with the generic
// backend, a cost that fits those FPCR writes (inari issue #2).
//
// The scalar operations are those of the generic backend, which uses the FMA
// here as well.

use super::lanewise::{
    add_i64, andnot, div_rn, exponent_in, gt_i64, is_finite, is_special, lane0, mul_rn, not,
    or_generic, select, splat_i64, sqrt_rn, step_up_where, sub_i64, two_sum_err, zero,
};
use super::{add_rn, all, and, eq, extract, gt, lt, or, splat, sub_rn, F64X2};
use crate::simd::generic;
use std::arch::aarch64::*;

pub(crate) use super::lanewise::{add_ru, sqrt1_ru, sub1_ru, sub_ru};
#[cfg(test)]
pub(crate) use super::lanewise::{
    add_ru_fpcr, div_ru_fpcr, mul_add_ru_fpcr, mul_ru_fpcr, sqrt1_rd_fpcr, sqrt1_ru_fpcr,
    sub1_ru_fpcr, sub_ru_fpcr,
};

/// `div_ru([x0, x1], [y0, y1]) = [x0 / y0, x1 / y1]` rounded toward +∞.
pub(crate) fn div_ru(x: F64X2, y: F64X2) -> F64X2 {
    // See `generic::div1_ru_fast`, the FMA variant.
    let q = div_rn(x, y);
    let special = is_special(x, y);
    // The remainder is representable where the check passes, so the FMA computes
    // it exactly.
    let r = fnmadd(q, y, x);
    // The check of `generic::div1_ru_fast`, -1022 <= exponent(q) <= 1023 and
    // exponent(x) >= -967, as comparisons of absolute values that share the +∞
    // of `is_finite`: 2^-1022 <= |q| < +∞ and |x| >= 2^-967, except that |q| is
    // compared with b = 2^-1022 (1 + 2^-32) from `splat_tiny_bound`, which is
    // stricter but sound (see there). They differ where x is NaN, which is
    // special, and where 2^-1022 <= |q| < b, which the generic backend
    // recomputes.
    let ok = or(
        special,
        and(
            and(abs_ge(q, splat_tiny_bound(-1022)), is_finite(q)),
            abs_ge(x, splat_pow2(-967)),
        ),
    );
    // x / y > q ⟺ r / y > 0, that is, r < 0 where y < 0, and r > 0 where y > 0.
    // y is nonzero and not NaN unless special, so its sign bit gives its sign.
    // Special lanes need no mask, as r is NaN or +0 in all of them, so both
    // comparisons with zero are false there and q, which is exact, is kept:
    // - x or y is NaN, or both are ±0 or both ±∞: q is NaN, and so is r.
    // - x is ±∞ and y finite and nonzero: q = ±∞, and q * y is ∞ with the sign
    //   of x, so r = x - q * y is ∞ - ∞ = NaN.
    // - One of x and y is ±0 and the other ±∞, or y is ±0 or ±∞ and x finite
    //   and nonzero: q * y is ∞ * 0 = NaN.
    // - x is ±0 and y finite and nonzero: q = ±0 and q * y = ±0 with the sign
    //   of x, both exact, so r = x - q * y = +0.
    let up = select(sign_bit_set(y), lt_zero(r), gt_zero(r));
    // `step_up_where` needs q finite and not -0 where up is set. Up is false in
    // the special lanes, and the others that pass `ok` have 2^-1022 < b <= |q|
    // < +∞.
    // If a lane fails `ok`, the generic backend recomputes both, and the integer
    // operations of `step_up_where` cannot trap.
    let res = step_up_where(up, q);
    or_generic(ok, res, move || generic::div_ru(extract(x), extract(y)))
}

/// `mul_add_ru([x0, x1], [y0, y1], [z0, z1]) = [x0 * y0 + z0, x1 * y1 + z1]`
/// rounded toward +∞ (with a single rounding).
pub(crate) fn mul_add_ru(a: F64X2, b: F64X2, c: F64X2) -> F64X2 {
    // See `generic::mul_add1_ru_fast` for the algorithm (ErrFma) and its
    // hypotheses, and `x86_64/fma.rs`, whose `mul_add_ru` this is.
    let u1 = mul_rn(a, b);
    let u2 = two_prod_err(a, b, u1);
    let r1 = fmadd(a, b, c);
    let alpha1 = add_rn(c, u2);
    let alpha2 = two_sum_err(c, u2, alpha1);
    let beta1 = add_rn(u1, alpha1);
    let beta2 = two_sum_err(u1, alpha1, beta1);
    let gamma = add_rn(sub_rn(beta1, r1), beta2);
    let err = add_rn(gamma, alpha2);

    let special = or(not(is_finite(c)), is_special(a, b));
    // The underflow hypotheses of `generic::mul_add1_ru_fast`, x = 0 or
    // exponent(x) >= e_min, compared as |x| >= b with one `facge` and no mask,
    // where b = 2^e_min (1 + (e_min + 1023) 2^-32) from `splat_tiny_bound`:
    // 2^-1022 (1 + 2^-32), 2^-1021 (1 + 2^-31) and 2^-1020 (1 + 3 * 2^-32)
    // below. That test is stricter than |x| >= 2^e_min, but sound (see
    // `splat_tiny_bound`), and |x| >= 2^e_min is the exponent form for every x
    // but NaN, where the exponent form is true and `facge` false. Both
    // differences can only send more lanes to the generic backend. For r1, the
    // exponent form (the exponent bits are not all zero) needs no constant, but
    // LLVM 22 merges it with r1 = 0 into an integer test for subnormals, 9
    // instructions against 5 for this form (`fcmeq`, `facge` and the `bif` that
    // LLVM makes of the `or`, and a `movi` each for the bound and the `bif`).
    let not_tiny = |x: F64X2, e_min: i64| or(eq(x, zero()), abs_ge(x, splat_tiny_bound(e_min)));
    // `two_prod_is_exact(u1)` and exponent(u1) <= 1021 are -968 <= exponent(u1)
    // <= 1021, that is, 2^-968 <= |u1| < 2^1022, which is false for NaN.
    let u1_in_range = and(abs_ge(u1, splat_pow2(-968)), abs_gt(splat_pow2(1022), u1));
    // exponent(c) <= 1021 is |c| < 2^1022 for every c, one `facgt` that shares
    // the 2^1022 of `u1_in_range`: a normal c with exponent e has 2^e <= |c| <
    // 2^(e + 1), so e <= 1021 if and only if |c| < 2^1022; ±0 and subnormals
    // pass both, as their exponent bits are zero and |c| < 2^-1022; and ±∞ and
    // NaN fail both: their exponent bits are all ones, |±∞| > 2^1022, and
    // `facgt` is false for NaN.
    let c_in_range = abs_gt(splat_pow2(1022), c);
    let ok = or(
        special,
        and(
            and(u1_in_range, and(c_in_range, is_finite(r1))),
            and(
                not_tiny(r1, -1022),
                and(not_tiny(alpha1, -1021), not_tiny(beta1, -1020)),
            ),
        ),
    );
    // As in `x86_64/fma.rs`, in every special case a * b + c is exactly
    // representable, so the FMA returns it and `r1` is already the answer.
    // Special lanes need no mask, as err is NaN or ±0 in all of them:
    // - c is ±∞ or NaN: so is alpha1 = RN(c + u2), and then alpha2 is NaN, as
    //   `two_sum_err` computes alpha1 - (alpha1 - u2) for finite u2, which is
    //   ∞ - ∞, and NaN otherwise.
    // - a or b is ±∞ or NaN: so is u1, and a * b is the same ∞ or NaN, so
    //   u2 = a * b - u1 is NaN.
    // - a or b is ±0, and the others are finite: u1 = a * b exactly, so u2 = 0,
    //   and no sum overflows, so `two_sum_err` is exact and alpha2 = beta2 = 0.
    //   Then beta1 = RN(0 + alpha1) and r1 = RN(a * b + c) are both c, up to
    //   the signs of zeros, so gamma = 0 and err = 0.
    let up = gt_zero(err);
    // `step_up_where` needs r1 finite and not -0 where err > 0. Up is false in
    // the special lanes, and in the others that pass `ok`, r1 is finite and
    // a * b + c = r1 + gamma + alpha2 exactly [BM11, Theorem 2], so err > 0
    // means a * b + c > r1: r1 is inexact, so a * b + c is nonzero. It is a
    // multiple of 2^-1074, so |r1| >= 2^-1074: c is one, as every float is, and
    // so is a * b, as a = A * 2^i and b = B * 2^j with integers |A|, |B| < 2^53
    // and |a * b| > 2^-969 (from |u1| >= 2^-968) give i + j > -1075. If a lane
    // fails `ok`, the generic backend recomputes both.
    let r = step_up_where(up, r1);
    or_generic(ok, r, move || {
        generic::mul_add_ru(extract(a), extract(b), extract(c))
    })
}

/// `mul_ru([x0, x1], [y0, y1]) = [x0 * y0, x1 * y1]` rounded toward +∞.
pub(crate) fn mul_ru(x: F64X2, y: F64X2) -> F64X2 {
    // See `generic::mul1_ru_fast`.
    let p = mul_rn(x, y);
    let special = is_special(x, y);
    let ok = or(special, two_prod_is_exact(p));
    // Each branch rounds by itself, as in `x86_64/fma.rs`.
    if all(ok) {
        mul_ru_fast(x, y, p)
    } else {
        mul_ru_tiny(x, y, p, ok)
    }
}

/// Returns RU(x * y) from p = RN(x * y), in the lanes where x or y is ±0, ±∞
/// or NaN, or where `two_prod_is_exact(p)`.
fn mul_ru_fast(x: F64X2, y: F64X2, p: F64X2) -> F64X2 {
    // NEON's fused operations add to or subtract from an accumulator, so
    // -e = p - x * y takes one instruction and e = x * y - p two. Rounding to
    // nearest is symmetric, so the computed -e is the negation of the computed e,
    // and e > 0 ⟺ -e < 0 (a zero of either sign is neither).
    let neg_e = two_prod_err_neg(x, y, p);
    // Where x or y is ±0, ±∞ or NaN, p is exact and needs no mask: if x or y is
    // ±∞ or NaN, p is ±∞ or NaN and so is x * y, so -e is ∞ - ∞ or NaN, which is
    // NaN; otherwise x * y is exactly ±0, p is the same zero, and -e = +0.
    let up = lt_zero(neg_e);
    // `step_up_where` needs p finite and not -0 where -e < 0, in the lanes named
    // above (the others are not used, and integer operations cannot trap). Where
    // x or y is ±0, ±∞ or NaN, -e is NaN or +0. Where `two_prod_is_exact(p)`, x,
    // y and p are finite, so -e = RN(p - x * y) < 0 means x * y > p, and p is not
    // -0, as a product that rounds to -0 is <= 0.
    step_up_where(up, p)
}

/// `mul_ru` where some lane fails `ok`: there, x and y are finite and nonzero,
/// and p = RN(x * y) is below 2^-968 or ±∞.
///
/// The algorithm, and the reason products below 2^-968 are rounded here rather
/// than by the generic backend, are those of `x86_64/fma.rs`'s `mul_ru_tiny`.
fn mul_ru_tiny(x: F64X2, y: F64X2, p: F64X2, ok: F64X2) -> F64X2 {
    // Powers of two, so that scaling by them is exact unless it overflows or
    // underflows.
    const TWO_POW_64: f64 = 18446744073709551616.0;
    const TWO_POW_128: f64 = TWO_POW_64 * TWO_POW_64;
    const TWO_POW_M128: f64 = 1.0 / TWO_POW_128;
    // Let z = x * y exactly, and S = 2^128. If |p| < 2^-968, then |z| < 2^-968,
    // and as |y| >= 2^-1074, |x| < 2^106, so x * S is exact. If p = ±∞, so is
    // ps, and the lane fails the check at the end.
    let xs = mul_rn(x, splat(TWO_POW_128));
    let ps = mul_rn(xs, y);
    // One TwoProduct for both kinds of lane: r = RU(z) in the lanes that pass
    // `ok`, as in `mul_ru`, and r = rs = RU(z * S) in the others where
    // `two_prod_is_exact(ps)`. The lanes that fail `ok` are not special, and
    // those that pass it pass x and p unchanged, so this meets the precondition
    // of `mul_ru_fast`.
    let r = mul_ru_fast(select(ok, x, xs), y, select(ok, p, ps));
    // There, RU(z) = RU(rs / S): see `x86_64/fma.rs`. RU(rs / S) is
    // q = RN(rs / S) if q >= rs / S, and the successor of q otherwise. q * S is
    // exact, as |q| <= 2^-968, so comparing it with rs compares q with rs / S.
    let q = mul_rn(r, splat(TWO_POW_M128));
    // `step_up_where` needs q finite and not -0 where q * S < r. There r is not
    // NaN and is finite: no float is below -∞, and r = +∞ gives q * S = +∞. So
    // q is finite, and it is not -0, which would need r > -0 * S = -0, whereas a
    // positive r * 2^-128 rounds to +0 or more.
    let q = step_up_where(lt(mul_rn(q, splat(TWO_POW_128)), r), q);
    // If p = ±0, then |z| <= 2^-1075, and RU(z) is 2^-1074 for z > 0 and -0 for
    // z < 0. p has the sign of z, and as integers, -0 < 0 and 2^-1074 = 1.
    // Otherwise |z| > 2^-1075, so |z * S| > 2^-947, and `two_prod_is_exact(ps)`
    // holds: every product below 2^-968 is computed here, and only those that
    // overflow go to the generic backend.
    let p_zero = eq(p, zero());
    let zero_rule = select(gt_i64(zero(), p), p, splat_i64(1));
    let res = select(ok, r, select(p_zero, zero_rule, q));
    let ok = or(ok, or(p_zero, two_prod_is_exact(ps)));
    or_generic(ok, res, move || generic::mul_ru(extract(x), extract(y)))
}

/// `sqrt_rd_ru([x0, x1]) = [√x0, √x1]`, the first rounded toward -∞ and the
/// second toward +∞.
pub(crate) fn sqrt_rd_ru(x: F64X2) -> F64X2 {
    // The lane-wise form of `generic::sqrt1_fast` with an FMA, correcting the two
    // lanes in opposite directions. See `x86_64/fma.rs`.
    let s = sqrt_rn(x);
    // x - s² is representable where the check passes, so the FMA computes it
    // exactly.
    let r = fnmadd(s, s, x);
    // The remainder is representable if 2^-966 <= x < 2^1024, which also excludes
    // ±0, +∞ and NaN, but not negative numbers: for those, s and r are NaN, the
    // comparisons below are false, and NaN is returned.
    let ok = exponent_in(x, -966, 1023);
    // √x < s ⟺ x - s² < 0, and then the result is the predecessor of s. Lane 0
    // rounds toward -∞, lane 1 toward +∞. Where a lane is corrected, s >= 2^-483,
    // so stepping is incrementing or decrementing its bits.
    let down = and(lt(r, zero()), lane0());
    let up = andnot(gt(r, zero()), lane0());
    let stepped = sub_i64(add_i64(s, down), up);
    or_generic(ok, stepped, move || generic::sqrt_rd_ru(extract(x)))
}

/// `sqrt1_rd(x) = √x` rounded toward -∞.
// `cr::sqrt_rd` calls it.
pub(crate) fn sqrt1_rd(x: f64) -> f64 {
    generic::sqrt1_rd(x)
}

/// `fmadd([x0, x1], [y0, y1], [z0, z1]) = [x0 * y0 + z0, x1 * y1 + z1]` with a
/// single rounding to nearest.
fn fmadd(x: F64X2, y: F64X2, z: F64X2) -> F64X2 {
    // `fmla`: the accumulator comes first.
    unsafe { vfmaq_f64(z, x, y) }
}

/// `fnmadd([x0, x1], [y0, y1], [z0, z1]) = [z0 - x0 * y0, z1 - x1 * y1]` with a
/// single rounding to nearest.
fn fnmadd(x: F64X2, y: F64X2, z: F64X2) -> F64X2 {
    // `fmls`.
    unsafe { vfmsq_f64(z, x, y) }
}

/// Returns the error e = x * y - p, where p = RN(x * y). See `generic::two_prod_err`.
fn two_prod_err(x: F64X2, y: F64X2, p: F64X2) -> F64X2 {
    // NEON has no fused x * y - z, so this is `fmla` on -p.
    unsafe { vfmaq_f64(vnegq_f64(p), x, y) }
}

/// Returns -e = p - x * y, where p = RN(x * y), in one instruction (`fmls`).
fn two_prod_err_neg(x: F64X2, y: F64X2, p: F64X2) -> F64X2 {
    fnmadd(x, y, p)
}

// The lanes where x < 0, without a zero constant (`fcmlt #0.0`); false for NaN.
fn lt_zero(x: F64X2) -> F64X2 {
    unsafe { vreinterpretq_f64_u64(vcltzq_f64(x)) }
}

// The lanes where x > 0 (`fcmgt #0.0`); false for NaN.
fn gt_zero(x: F64X2) -> F64X2 {
    unsafe { vreinterpretq_f64_u64(vcgtzq_f64(x)) }
}

// The lanes where the sign bit of x is set, from the bits as an integer
// (`cmlt #0`): x < 0 or x = -0, or a NaN with the sign bit set.
fn sign_bit_set(x: F64X2) -> F64X2 {
    unsafe { vreinterpretq_f64_u64(vcltzq_s64(vreinterpretq_s64_f64(x))) }
}

// The lanes where |x| >= |y| (`facge`); false if x or y is NaN.
fn abs_ge(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { vreinterpretq_f64_u64(vcageq_f64(x, y)) }
}

// The lanes where |x| > |y| (`facgt`); false if x or y is NaN.
fn abs_gt(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { vreinterpretq_f64_u64(vcagtq_f64(x, y)) }
}

// `splat_pow2(e) = [2^e, 2^e]`, for -1022 <= e <= 1023.
fn splat_pow2(e: i64) -> F64X2 {
    splat_i64((e + 1023) << 52)
}

// `splat_tiny_bound(e) = [b, b]` with b = 2^e (1 + (e + 1023) 2^-32), for
// -1022 <= e <= -1008, the bound of the underflow checks. With k = e + 1023,
// the bits of b are the exponent field k and the fraction field k * 2^20, so
// both 32-bit halves are k << 20, which for k <= 15 one `movi .4s` (an 8-bit
// immediate shifted left by 16) makes. The halves of 2^e differ (k << 20 and
// 0), and LLVM builds it with a `mov` and a `dup`.
//
// A check |x| >= b in place of the fast path's |x| >= 2^e is stricter, and
// still sound: b > 2^e, so a lane that passes it passes the fast path's check.
// Only the lanes with 2^e <= |x| < b fail it in addition, and the generic
// backend recomputes them. The fast path gave them the generic backend's
// result too (the differential tests check that bit for bit), so no result
// changes, only which path computes some of them.
fn splat_tiny_bound(e: i64) -> F64X2 {
    let k = e + 1023;
    splat_i64((k << 52) | (k << 20))
}

// The lanes where `two_prod_err(x, y, x * y)` is exact, which with an FMA depends
// on the product alone. See `generic::two_prod_is_exact`: -968 <= exponent(p)
// <= 1023, that is, 2^-968 <= |p| < +∞, which shares the +∞ of `is_finite`
// with the other checks. Both forms are false for NaN.
fn two_prod_is_exact(p: F64X2) -> F64X2 {
    and(abs_ge(p, splat_pow2(-968)), is_finite(p))
}
