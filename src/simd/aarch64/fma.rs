// The operations of the aarch64 backend that round toward +∞, the port of
// `x86_64/fma.rs` to NEON, which every aarch64 processor has, as it has the FMA.
//
// They compute the fast paths of the generic backend on both lanes at once, and
// the few inputs that fail their checks in either lane are recomputed by the
// generic backend (see `lanewise.rs`). The FMA makes TwoProduct and the
// remainders of division and of the square root one instruction each. As on
// x86-64, `mul_ru` computes RU(x * y) itself where x and y are nonzero and
// |RN(x * y)| < 2^-968 (see `mul_ru_tiny`).
//
// The obvious alternative is to let the hardware round: `fadd` and friends with
// FPCR.RMode set to round toward +∞. That is what this backend replaced, and it
// is slower, because FPCR has to be saved, set and restored around every
// operation: on an Apple M1 Pro, the dot product of two 3-vectors of intervals
// took 141.0 ns that way, and 44.1 ns with the generic backend (inari issue #2).
//
// The scalar operations are those of the generic backend, which uses the FMA
// here as well.

use super::lanewise::{
    add_i64, andnot, div_rn, exponent_gt, exponent_in, exponent_le, gt_i64, is_finite, is_special,
    lane0, mul_rn, not, or_generic, select, splat_i64, sqrt_rn, step_up, sub_i64, two_sum_err,
    zero,
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
    let ok = or(
        special,
        and(exponent_in(q, -1022, 1023), exponent_gt(x, -968)),
    );
    // x / y > q ⟺ r / y > 0. y is nonzero and r is not NaN unless special.
    let up = or(
        and(gt(r, zero()), gt(y, zero())),
        and(lt(r, zero()), lt(y, zero())),
    );
    let res = select(andnot(up, special), step_up(q), q);
    or_generic(ok, res, || generic::div_ru(extract(x), extract(y)))
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
    let not_tiny = |x: F64X2, e_min: i64| or(eq(x, zero()), exponent_gt(x, e_min - 1));
    let ok = or(
        special,
        and(
            and(
                and(two_prod_is_exact(u1), exponent_le(u1, 1021)),
                and(exponent_le(c, 1021), is_finite(r1)),
            ),
            and(
                not_tiny(r1, -1022),
                and(not_tiny(alpha1, -1021), not_tiny(beta1, -1020)),
            ),
        ),
    );
    // As in `x86_64/fma.rs`, in every special case a * b + c is exactly
    // representable, so the FMA returns it and `r1` is already the answer.
    // If err > 0, then r1 is inexact and thus nonzero.
    let up = andnot(gt(err, zero()), special);
    let r = select(up, step_up(r1), r1);
    or_generic(ok, r, || {
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
        mul_ru_fast(x, y, p, special)
    } else {
        mul_ru_tiny(x, y, p, ok, special)
    }
}

/// Returns RU(x * y) from p = RN(x * y), in the lanes that are `special` or
/// where `two_prod_is_exact(p)`.
fn mul_ru_fast(x: F64X2, y: F64X2, p: F64X2, special: F64X2) -> F64X2 {
    // NEON's fused operations add to or subtract from an accumulator, so
    // -e = p - x * y takes one instruction and e = x * y - p two. Rounding to
    // nearest is symmetric, so the computed -e is the negation of the computed e,
    // and e > 0 ⟺ -e < 0 (a zero of either sign is neither).
    let neg_e = two_prod_err_neg(x, y, p);
    let up = andnot(lt(neg_e, zero()), special);
    select(up, step_up(p), p)
}

/// `mul_ru` where some lane fails `ok`: there, x and y are finite and nonzero,
/// and p = RN(x * y) is below 2^-968 or ±∞.
///
/// The algorithm, and the reason products below 2^-968 are rounded here rather
/// than by the generic backend, are those of `x86_64/fma.rs`'s `mul_ru_tiny`.
fn mul_ru_tiny(x: F64X2, y: F64X2, p: F64X2, ok: F64X2, special: F64X2) -> F64X2 {
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
    // `two_prod_is_exact(ps)`.
    let r = mul_ru_fast(select(ok, x, xs), y, select(ok, p, ps), special);
    // There, RU(z) = RU(rs / S): see `x86_64/fma.rs`. RU(rs / S) is
    // q = RN(rs / S) if q >= rs / S, and the successor of q otherwise. q * S is
    // exact, as |q| <= 2^-968, so comparing it with rs compares q with rs / S.
    let q = mul_rn(r, splat(TWO_POW_M128));
    let q = select(lt(mul_rn(q, splat(TWO_POW_128)), r), step_up(q), q);
    // If p = ±0, then |z| <= 2^-1075, and RU(z) is 2^-1074 for z > 0 and -0 for
    // z < 0. p has the sign of z, and as integers, -0 < 0 and 2^-1074 = 1.
    // Otherwise |z| > 2^-1075, so |z * S| > 2^-947, and `two_prod_is_exact(ps)`
    // holds: every product below 2^-968 is computed here, and only those that
    // overflow go to the generic backend.
    let p_zero = eq(p, zero());
    let zero_rule = select(gt_i64(zero(), p), p, splat_i64(1));
    let res = select(ok, r, select(p_zero, zero_rule, q));
    let ok = or(ok, or(p_zero, two_prod_is_exact(ps)));
    or_generic(ok, res, || generic::mul_ru(extract(x), extract(y)))
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
    or_generic(ok, stepped, || generic::sqrt_rd_ru(extract(x)))
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

// The lanes where `two_prod_err(x, y, x * y)` is exact, which with an FMA depends
// on the product alone. See `generic::two_prod_is_exact`.
fn two_prod_is_exact(p: F64X2) -> F64X2 {
    exponent_in(p, -968, 1023)
}
