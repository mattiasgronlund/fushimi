// The accurate phase of x^y, which `pow_dir` and `pow_near` of `src/dyadic/pow.rs` try after
// the fast path and `exact`, and before `ziv`, at a y that is not an integer of `i32`: bounds
// on x^y about 2^-112 of its value apart, computed in integers, and the rounding of x^y where
// both bounds round to the same `f64`. Its structure is that of the second phase of CORE-MATH's
// `pow` (Tom Hubrecht and Paul Zimmermann, `src/binary64/pow/pow.c`, MIT licence): ln x from a
// table of logarithms and a polynomial, t = y ln x, and e^t = 2^(k/4096) e^w from two tables of
// powers of 2 and a polynomial. Unlike CORE-MATH's, which computes one approximation of x^y and
// bounds its error step by step, every step here computes a lower and an upper bound, rounding
// each down and each up, so that the bounds hold by monotonicity and the bounds on the remainders
// of the two polynomials, and only their width, which decides how often the test passes, depends
// on the rest of the error analysis, which nothing needs to prove.
//
// The numbers are integers scaled by a fixed power of 2 at each step: "at 2^-k" is that
// integer times 2^-k. At each argument the callers pass, the phase returns bounds or `None` (a
// decline, after which `ziv` computes x^y): the steps that could go out of the range of their
// integers return `None`, and the others stay in range (the comments at the less obvious ones
// say why), so that the phase does not panic. That is checked by reading, not proved:
// `rocq/theories/Model.v` computes those others without a check. `rocq/theories/AccPow.v`
// proves the bounds (`acc_pow_correct`) and the roundings (`acc_pow_dir_correct` and
// `acc_pow_near_correct`), from `rocq/theories/AccPowLn.v` for the bounds on t
// (`acc_t_correct`) and `rocq/theories/AccPowExp.v` for those on e^t (`acc_exp_correct`). These
// build on `rocq/theories/AccPowTables.v` for the tables and `LN2` (`acc_ln_correct`,
// `exp_hi_correct`, `exp_lo_correct` and `ln2_acc_bounds`) and on `rocq/theories/AccPowArith.v`
// for the integer operations.
//
// `rocq/theories/Model.v` transcribes each constant and function of this file, without the
// statements under `#[cfg(test)]`, so it has to be updated along with them. The comment on each
// names its transcription and the proofs, other than `Local` lemmas, that name it or unfold a
// transcription of this file that calls it.

use super::super::{log::ln_split, round, Dyadic};
use super::odd_parts;
use super::tables::{ACC_G, ACC_LN, ACC_R, EXP_HI, EXP_LO};

// The low 64 bits of a `u128`. `rocq/theories/Model.v` transcribes it (`DyadicPow.m64`) for the
// proof of `mul_wide_correct` in `rocq/theories/AccPowArith.v`.
const M64: u128 = u64::MAX as u128;

// The mask of the fraction field of an `f64`. `rocq/theories/Model.v` transcribes it
// (`DyadicPow.FRAC`) for the proofs of `mm_correct` and `acc_t_correct` in
// `rocq/theories/AccPowLn.v`.
const FRAC: u64 = (1 << 52) - 1;

// floor(2^127 / (j + 1)) for j from 0 to 13, the coefficients of ln(1 + z) / z at 2^-127, each
// within 1 below 1 / (j + 1). `rocq/theories/Model.v` transcribes the entries
// (`DyadicPow.log_c j` for `LOG_C[j]`) for the proofs of `log_c_bounds`, which shows that bound,
// `log_c_range`, `log_q_step`, `log_q_inv`, `log_q_correct` and `acc_t_correct` in
// `rocq/theories/AccPowLn.v`.
const LOG_C: [u128; 14] = {
    let mut c = [0; 14];
    let mut j = 0;
    while j < 14 {
        c[j] = (1 << 127) / (j as u128 + 1);
        j += 1;
    }
    c
};

// floor(2^127 / j!) for j from 0 to 8, the coefficients of e^w at 2^-127, each within 1 below
// 1 / j!: floor(floor(a / b) / c) = floor(a / (b c)) for positive integers.
// `rocq/theories/Model.v` transcribes the entries (`DyadicPow.exp_d j` for `EXP_D[j]`) for the
// proof of `acc_exp_correct` in `rocq/theories/AccPowExp.v`, whose lemma `exp_d_bounds` checks
// that bound by computation.
const EXP_D: [u128; 9] = {
    let mut d = [1 << 127; 9];
    let mut j = 2;
    while j < 9 {
        d[j] = d[j - 1] / j as u128;
        j += 1;
    }
    d
};

// floor(ln 2 2^128), so that ln 2 is in [LN2, LN2 + 1] at 2^-128. `rocq/theories/Model.v`
// transcribes it (`DyadicPow.LN2`) for the proofs of `ln2_acc_bounds` in
// `rocq/theories/AccPowTables.v`, which shows those bounds, `acc_t_correct` in
// `rocq/theories/AccPowLn.v` and `acc_exp_correct` in `rocq/theories/AccPowExp.v`.
pub(super) const LN2: u128 = 0xb172_17f7_d1cf_79ab_c9e3_b398_03f2_f6af;

// round(2^62 / ln 2), with which `acc_pow` picks k. Any k gives bounds, so nothing depends on
// its value but how often w is in the range of the exponential. `rocq/theories/Model.v`
// transcribes it (`DyadicPow.INV_LN2`) for the proof of `acc_exp_correct` in
// `rocq/theories/AccPowExp.v`.
pub(super) const INV_LN2: i64 = 0x5c55_1d94_ae0b_f85e;

// a b = hi 2^128 + lo, as (hi, lo), by schoolbook multiplication of the 64-bit halves of a and
// b. `mid`, the sum of the bits from 2^64 up of the low product and of the low halves of the
// two middle ones, is below 3 2^64, and `hi` takes its bits from 2^128 up.
// `rocq/theories/Model.v` transcribes it (`DyadicPow.mul_wide`) for the proofs of
// `mul_wide_correct`, `mul_dn_correct` and `mul_up_correct` in `rocq/theories/AccPowArith.v`,
// `term_bounds` and `acc_t_correct` in `rocq/theories/AccPowLn.v` and `acc_exp_correct` in
// `rocq/theories/AccPowExp.v`.
#[inline(always)]
fn mul_wide(a: u128, b: u128) -> (u128, u128) {
    let (a0, a1, b0, b1) = (a & M64, a >> 64, b & M64, b >> 64);
    let (p00, p01, p10, p11) = (a0 * b0, a0 * b1, a1 * b0, a1 * b1);
    let mid = (p00 >> 64) + (p01 & M64) + (p10 & M64);
    // `mid << 64` drops the bits of `mid` from 2^64 up, which `hi` takes.
    let lo = mid << 64 | p00 & M64;
    let hi = p11 + (p01 >> 64) + (p10 >> 64) + (mid >> 64);
    (hi, lo)
}

// floor((hi 2^128 + lo) / 2^s) for any s, where it is below 2^128, and `None` otherwise. For
// s < 0 it is the exact (hi 2^128 + lo) 2^-s. `rocq/theories/Model.v` transcribes it
// (`DyadicPow.shr_dn`) for the proofs of `shr_dn_correct` and `shr_up_correct` in
// `rocq/theories/AccPowArith.v`, and `term_bounds` and `acc_t_correct` in
// `rocq/theories/AccPowLn.v`.
#[inline(always)]
fn shr_dn((hi, lo): (u128, u128), s: i64) -> Option<u128> {
    if s >= 256 {
        // hi 2^128 + lo < 2^256 <= 2^s.
        Some(0)
    } else if s >= 128 {
        // floor((hi + lo 2^-128) / 2^(s - 128)) = floor(hi / 2^(s - 128)), as lo 2^-128 < 1.
        Some(hi >> (s - 128))
    } else if s > 0 {
        if hi >> s != 0 {
            None
        } else {
            Some(hi << (128 - s) | lo >> s)
        }
    } else if hi != 0 {
        None
    } else if s == 0 {
        Some(lo)
    } else if s > -128 && lo >> (128 + s) == 0 {
        Some(lo << -s)
    } else if lo == 0 {
        Some(0)
    } else {
        None
    }
}

// ceil((hi 2^128 + lo) / 2^s) for any s, where it is below 2^128, and `None` otherwise:
// `shr_dn` plus 1 where a bit that it drops is set. `rocq/theories/Model.v` transcribes it
// (`DyadicPow.shr_up`) for the proofs of `shr_up_correct` in `rocq/theories/AccPowArith.v`, and
// `term_bounds` and `acc_t_correct` in `rocq/theories/AccPowLn.v`.
#[inline(always)]
fn shr_up((hi, lo): (u128, u128), s: i64) -> Option<u128> {
    let q = shr_dn((hi, lo), s)?;
    let dropped = if s >= 256 {
        hi | lo != 0
    } else if s >= 128 {
        lo != 0 || hi & ((1 << (s - 128)) - 1) != 0
    } else if s > 0 {
        lo & ((1 << s) - 1) != 0
    } else {
        false
    };
    q.checked_add(u128::from(dropped))
}

// floor(a b / 2^s) for 0 < s < 128 and a b < 2^(128 + s), so that the high half of the
// product is below 2^s and nothing overflows. `rocq/theories/Model.v` transcribes it
// (`DyadicPow.mul_dn`) for the proofs of `mul_dn_correct` in `rocq/theories/AccPowArith.v`,
// `mul_63`, `log_q_step` and `log_q_inv` in `rocq/theories/AccPowLn.v` and `acc_exp_correct` in
// `rocq/theories/AccPowExp.v`.
#[inline(always)]
fn mul_dn(a: u128, b: u128, s: u32) -> u128 {
    let (hi, lo) = mul_wide(a, b);
    hi << (128 - s) | lo >> s
}

// ceil(a b / 2^s) for 0 < s < 128 and a b < 2^(128 + s) - 2^s, so that the sum does not
// overflow: `mul_dn` plus 1 where a bit that it drops is set. `rocq/theories/Model.v`
// transcribes it (`DyadicPow.mul_up`) for the proofs of `mul_up_correct` in
// `rocq/theories/AccPowArith.v`, `mul_63`, `log_q_step` and `log_q_inv` in
// `rocq/theories/AccPowLn.v` and `acc_exp_correct` in `rocq/theories/AccPowExp.v`.
#[inline(always)]
fn mul_up(a: u128, b: u128, s: u32) -> u128 {
    let (hi, lo) = mul_wide(a, b);
    (hi << (128 - s) | lo >> s) + u128::from(lo & ((1 << s) - 1) != 0)
}

// The bounds [lo, hi] on a magnitude, of the sign of -1 if `neg`, as `i128`s: [-hi, -lo] if
// `neg` and [lo, hi] otherwise, and `None` where a bound is 2^127 or above.
// `rocq/theories/Model.v` transcribes it (`DyadicPow.signed`) for the proofs of `signed_correct`
// in `rocq/theories/AccPowArith.v`, `term_bounds` and `acc_t_correct` in
// `rocq/theories/AccPowLn.v` and `acc_exp_correct` in `rocq/theories/AccPowExp.v`.
#[inline(always)]
fn signed(neg: bool, lo: u128, hi: u128) -> Option<(i128, i128)> {
    let (lo, hi) = (i128::try_from(lo).ok()?, i128::try_from(hi).ok()?);
    Some(if neg { (-hi, -lo) } else { (lo, hi) })
}

// Bounds [tl, th] at 2^-115 on t = y ln x, for a finite x > 0 and a finite y other than ±0.
//
// ln_split gives x = 2^e m with m in [(362 + i) / 512, (363 + i) / 512), and m = mm 2^-53, as
// the exponent field of m is 1022 or 1023. With r = R 2^-10 for R = `ACC_R[i]`, the inverse of
// the middle of that interval rounded to an integer at 2^-10, and 1 next to 1 (i = 149, 150),
// z = r m - 1 = (mm R - 2^63) 2^-63 is exact, and |z| <= 2^-9 (checked here, and by the tests
// at each end of each interval). Then
//   y ln x = y e ln 2 + y (-ln r) + y z Q(z), Q(z) = ln(1 + z) / z,
// three terms that each come from a product of integers, shifted to 2^-115 by floor and ceil.
// Q(z) is the Taylor polynomial sum_{j=0}^{13} (-z)^j / (j + 1) of ln(1 + z) / z, within
// |z|^14 / (15 (1 - |z|)) < 2^-129.9 of it, by Horner's scheme at 2^-127, which takes the bound
// on each side from the bound of the previous step that minimizes or maximizes it.
// `rocq/theories/Model.v` transcribes it (`DyadicPow.acc_t`) for the proofs of `acc_t_correct`
// in `rocq/theories/AccPowLn.v` and `acc_pow_correct` in `rocq/theories/AccPow.v`.
#[inline(always)]
fn acc_t(x: f64, y: f64) -> Option<(i128, i128)> {
    let (e, m, i) = ln_split(x);
    let b = m.to_bits();
    let mm = ((b & FRAC) | 1 << 52) << ((b >> 52) - 1022);
    // mm < 2^54 and R < 2^11, so that the product cannot overflow.
    let z = i128::from(mm) * i128::from(ACC_R[i]) - (1 << 63);
    let a = z.unsigned_abs();
    if a > 1 << 54 {
        return None;
    }
    // q in [ql, qh] at 2^-127, with each coefficient in [c, c + 1]. Where z > 0, q' = c - a q
    // 2^-63 decreases with q, and otherwise q' = c + a q 2^-63 increases with it. These cannot
    // overflow: a q < 2^54 2^128, and q stays in [2^123, 2^127 + 2^120].
    // `rocq/theories/Model.v` transcribes the loop (`DyadicPow.log_q`) for the proofs of
    // `log_q_inv`, `log_q_correct` and `acc_t_correct` in `rocq/theories/AccPowLn.v`.
    let (mut ql, mut qh) = (LOG_C[13], LOG_C[13] + 1);
    for &c in LOG_C[..13].iter().rev() {
        (ql, qh) = if z > 0 {
            (c - mul_up(a, qh, 63), c + 1 - mul_dn(a, ql, 63))
        } else {
            (c + mul_dn(a, ql, 63), c + 1 + mul_up(a, qh, 63))
        };
    }
    // ln(1 + z) / z in [ql - 1, qh + 1] at 2^-127, with the remainder of the Taylor polynomial.
    let (ql, qh) = (ql - 1, qh + 1);
    // |y| = my 2^ey with an odd my < 2^53.
    let (my, ey) = odd_parts(y);
    let neg_y = y < 0.0;
    let my = u128::from(my);
    // y e ln 2 = ±my |e| 2^ey ln 2, with ln 2 in [LN2, LN2 + 1] at 2^-128, so that the
    // magnitude is in [my |e| LN2, my |e| (LN2 + 1)] at 2^(ey - 128). my |e| < 2^53 2^11.
    let ae = my * u128::from(e.unsigned_abs());
    let s = 13 - ey;
    let (al, ah) = signed(
        neg_y != (e < 0),
        shr_dn(mul_wide(ae, LN2), s)?,
        shr_up(mul_wide(ae, LN2 + 1), s)?,
    )?;
    // y (-ln r), with -ln r in [T, T + 1] at 2^-(127 + g) for T = `ACC_LN[i]` and g =
    // `ACC_G[i]`, except that T = 0 only where r = 1, and then -ln r = 0. So |-ln r| is in
    // [|T| - 1, |T|] where T < 0, in [|T|, |T| + 1] where T > 0, and 0 where T = 0.
    let t = ACC_LN[i];
    let tm = t.unsigned_abs();
    let s = 12 + i64::from(ACC_G[i]) - ey;
    let (bl, bh) = signed(
        neg_y != (t < 0),
        shr_dn(mul_wide(my, tm - u128::from(t < 0)), s)?,
        shr_up(mul_wide(my, tm + u128::from(t > 0)), s)?,
    )?;
    // y z Q(z) = ±my |Z| 2^(ey - 63) Q(z), with Q(z) in [ql, qh] at 2^-127, and the sign of y
    // times that of z, as Q(z) > 0. my |Z| <= 2^53 2^54.
    let n = my * a;
    let s = 75 - ey;
    let (cl, ch) = signed(
        neg_y != (z < 0),
        shr_dn(mul_wide(n, ql), s)?,
        shr_up(mul_wide(n, qh), s)?,
    )?;
    let tl = al.checked_add(bl)?.checked_add(cl)?;
    let th = ah.checked_add(bh)?.checked_add(ch)?;
    Some((tl, th))
}

// Bounds (lo, hi, e) on e^t for each t in [tl, th] at 2^-115: lo 2^e <= e^t <= hi 2^e, with
// 2^126 <= lo.
//
// e^t = 2^(k/4096) e^w for w = t - k ln 2 / 4096, and 2^(k/4096) = 2^(k >> 12) 2^(j1/64)
// 2^(j2/4096) for k = 4096 (k >> 12) + 64 j1 + j2, with 2^(j1/64) in [EXP_HI[j1], EXP_HI[j1] + 1]
// and 2^(j2/4096) in [EXP_LO[j2], EXP_LO[j2] + 1] at 2^-127. k is t 4096 / ln 2 from the top
// bits of tl, about rounded down, so that w is in [0, 2^-12] but where k is off by one, and the
// phase declines where it is not. e^w is the Taylor polynomial sum_{j=0}^{8} w^j / j!, within
// w^9 / 9! e^w < 2^-126.4 of it, by Horner's scheme at 2^-127, which only increases with w.
// `rocq/theories/Model.v` transcribes it (`DyadicPow.acc_exp`) for the proofs of
// `acc_exp_correct` in `rocq/theories/AccPowExp.v` and `acc_pow_correct` in
// `rocq/theories/AccPow.v`.
#[inline(always)]
fn acc_exp(tl: i128, th: i128) -> Option<(u128, u128, i64)> {
    // tl >> 64 is in [-2^63, 2^63), and the product is below 2^126 in magnitude.
    let k = ((i128::from((tl >> 64) as i64) * i128::from(INV_LN2)) >> 101) as i64;
    // k ln 2 / 4096 = ±|k| ln 2 2^-12 in [|k| LN2, |k| (LN2 + 1)] at 2^-140, with |k| < 2^25.
    let km = u128::from(k.unsigned_abs());
    if km >= 1 << 25 {
        return None;
    }
    let (cl, ch) = signed(k < 0, mul_dn(km, LN2, 25), mul_up(km, LN2 + 1, 25))?;
    let (wl, wh) = (tl.checked_sub(ch)?, th.checked_sub(cl)?);
    if wl < 0 || wh > 1 << 103 {
        return None;
    }
    let (wl, wh) = (wl as u128, wh as u128);
    // p in [pl, ph] at 2^-127, with each coefficient in [d, d + 1]: p' = d + w p. These cannot
    // overflow: w p < 2^103 2^128, and p stays below 2^127 (1 + 2^-11).
    // `rocq/theories/Model.v` transcribes the loop (`DyadicPow.exp_p`) for the proof of
    // `acc_exp_correct` in `rocq/theories/AccPowExp.v`.
    let (mut pl, mut ph) = (EXP_D[8], EXP_D[8] + 1);
    for &d in EXP_D[..8].iter().rev() {
        pl = d + mul_dn(wl, pl, 115);
        ph = d + 1 + mul_up(wh, ph, 115);
    }
    // e^w in [pl, ph + 2] at 2^-127, with the remainder of the Taylor polynomial.
    let ph = ph + 2;
    let (j1, j2) = (((k >> 6) & 63) as usize, (k & 63) as usize);
    let (eh, el) = (EXP_HI[j1], EXP_LO[j2]);
    // 2^(j1/64 + j2/4096) in [sl, sh] at 2^-127, each in [2^127, 2^128), as
    // 2^(63/64 + 63/4096) < 2.
    let sl = mul_dn(eh, el, 127);
    let sh = mul_up(eh + 1, el + 1, 127);
    // sl pl and sh ph at 2^-254, and their bits from 2^128 up at 2^-126.
    let (lo, _) = mul_wide(sl, pl);
    let (hi, rest) = mul_wide(sh, ph);
    Some((lo, hi + u128::from(rest != 0), (k >> 12) - 126))
}

// Bounds (lo, hi, e) on x^y for a finite x > 0 and a finite y other than ±0: lo 2^e <= x^y <=
// hi 2^e, with 2^126 <= lo, so that both are at least 127 bits long. `None` where the phase
// declines. Behind `#[inline(never)]`, so that its one copy serves `pow_dir`, through
// `acc_pow_dir`, and `pow_near`, and its code stays out of theirs. `rocq/theories/Model.v`
// transcribes it (`DyadicPow.acc_pow`) for the proofs of `acc_pow_correct` and
// `acc_bounds_correct` in `rocq/theories/AccPow.v`.
#[inline(never)]
pub(super) fn acc_pow(x: f64, y: f64) -> Option<(u128, u128, i64)> {
    let (tl, th) = acc_t(x, y)?;
    acc_exp(tl, th)
}

// The bounds of `acc_pow` as `Dyadic<2>`s, which `round` takes exactly, as they are at most 128
// bits long. `rocq/theories/Model.v` transcribes it (`DyadicPow.acc_bounds`) for the proofs of
// `acc_bounds_correct`, `acc_pow_dir_correct` and `acc_pow_near_correct` in
// `rocq/theories/AccPow.v`.
#[inline(always)]
fn acc_bounds(x: f64, y: f64) -> Option<(Dyadic<2>, Dyadic<2>)> {
    let (lo, hi, e) = acc_pow(x, y)?;
    let lo = round::<2>(false, &[lo as u64, (lo >> 64) as u64], e, false, false);
    let hi = round::<2>(false, &[hi as u64, (hi >> 64) as u64], e, false, true);
    Some((lo, hi))
}

// x^y rounded toward +∞ if `up` and toward -∞ otherwise, where both bounds of `acc_pow` round
// to the same `f64`, as `ziv_at` tests an enclosure, and `None` otherwise. Directed rounding is
// monotonic, so that number is then also the rounding of x^y. With the fast path off in the
// tests, it declines too, so that those tests still reach `ziv`. Behind `#[inline(never)]`, so
// that the bounds of `acc_bounds` live in its own frame rather than in that of `pow_dir`, whose
// front every exact case runs, and which they made several times larger where inlined.
// `rocq/theories/Model.v` transcribes it (`DyadicPow.acc_pow_dir`) for the proofs of
// `acc_pow_dir_correct` in `rocq/theories/AccPow.v`, and `pow_dir_post` and `acc_ziv_strict` in
// `rocq/theories/DyPow.v`.
#[inline(never)]
pub(super) fn acc_pow_dir(x: f64, y: f64, up: bool) -> Option<f64> {
    #[cfg(test)]
    if !super::super::fast::fast_enabled() {
        return None;
    }
    let (lo, hi) = acc_bounds(x, y)?;
    let (lo, hi) = (lo.to_f64(up), hi.to_f64(up));
    // Both bounds are positive, so that `==` compares no zeros of two signs.
    if lo == hi {
        Some(lo)
    } else {
        None
    }
}

// x^y rounded to nearest, ties to even, where both bounds of `acc_pow` round to it, as
// `ziv_near_at` tests an enclosure, and `None` otherwise. `rocq/theories/Model.v` transcribes it
// (`DyadicPow.acc_pow_near`) for the proofs of `acc_pow_near_correct` in
// `rocq/theories/AccPow.v`, and `pow_near_correct` and `acc_ziv_near_strict` in
// `rocq/theories/DyPowNear.v`.
#[inline(always)]
pub(super) fn acc_pow_near(x: f64, y: f64) -> Option<f64> {
    #[cfg(test)]
    if !super::super::fast::fast_enabled() {
        return None;
    }
    let (lo, hi) = acc_bounds(x, y)?;
    let (lo, hi) = (lo.to_f64_near(), hi.to_f64_near());
    if lo.to_bits() == hi.to_bits() {
        Some(lo)
    } else {
        None
    }
}
