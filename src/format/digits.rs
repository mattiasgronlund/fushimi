// The digits of a finite nonzero bound of an interval that `src/format.rs` prints: the bound
// rounded in its direction, toward -∞ for the lower bound and toward +∞ for the upper one, to
// the digits that the style and the precision keep, as an integer times a power of the radix.
// `src/format.rs` writes the text from these, in MPFR's layout.
//
// `rocq/theories/Model.v` transcribes each function below for the proofs in
// `rocq/theories/FormatCut.v`, `rocq/theories/FormatLead.v`, `rocq/theories/FormatDec.v` and
// `rocq/theories/FormatHex.v`, which show that `fixed`, `sci` and `hex` round as their
// comments say, so it has to be updated along with them. The proofs give the value of
// `d * 10^k` or `d * 2^k`, and `-p <= k <= 0` for `fixed`. The other bounds on `d` and `k` in
// the comments, on which the layout in `src/format.rs` relies, are not proved:
// `src/format/diff_tests.rs` compares the text with MPFR's.

use crate::nat::Nat;

// `|x| = m * 2^e` for a finite `x`, with `m < 2^53` the stored significand with the implicit
// bit.
fn decompose(x: f64) -> (u64, i64) {
    let c = x.to_bits() & !(1 << 63);
    let be = c >> 52;
    let m = c & ((1 << 52) - 1);
    // The implicit bit is 1 unless the biased exponent is 0, and the biased exponents 0 and 1
    // have the same scale.
    let m = if be == 0 { m } else { m + (1 << 52) };
    (m, be.max(1) as i64 - 1075)
}

// `|x| = n * 10^s` for a finite `x`, with `s <= 0`.
//
// `cut` calls it in two places, and without `always` the compiler kept it out of line (in the
// haswell assembly, with `#[inline]` too), so that a bound with no digit to cut took a call and
// a second `decompose`.
#[inline(always)]
fn exact_dec(x: f64) -> (Nat, i64) {
    let (m, e) = decompose(x);
    let m = Nat::from_u64(m);
    if e >= 0 {
        (&m << e as u64, 0)
    } else {
        // m * 2^e = m * 5^-e * 10^e.
        (&m * &Nat::pow5(-e as u32), e)
    }
}

// Whether `x` rounds away from zero: toward +∞ (`up`) if it is positive, and toward -∞ if
// it is negative.
fn away(x: f64, up: bool) -> bool {
    x.is_sign_negative() != up
}

// `n * 10^s` cut to a multiple of `10^t`: `(d, max(s, t))` with `d * 10^max(s, t)` the result,
// rounded toward zero, or away from zero if `away`.
fn cut_dec(n: Nat, s: i64, t: i64, away: bool) -> (Nat, i64) {
    if t <= s {
        return (n, s);
    }
    let j = (t - s) as u32;
    let (q, r) = n.div_rem(&(&Nat::pow5(j) << u64::from(j)));
    if away && !r.is_zero() {
        (&q + &Nat::from_u64(1), t)
    } else {
        (q, t)
    }
}

// `|x|` cut to a multiple of `10^t`, for a finite nonzero `x`: `cut_dec(n, s, t, away)` for
// `(n, s) = exact_dec(x)`, which has `s = min(e, 0)`.
fn cut(x: f64, t: i64, away: bool) -> (Nat, i64) {
    let (m, e) = decompose(x);
    let s = e.min(0);
    // Without the shift, each bound took two tests, `exact_dec`'s `e >= 0` and `cut_dec`'s
    // `t <= s`, for four paths: no digit to cut or a division, each with `e >= 0` or `e < 0`.
    // The shift is a fifth path, so some path takes a third test, and the order gives it to
    // the division, which costs the most anyway:
    // - `t <= s` first, `cut_dec`'s own test: a bound with no digit to cut takes it and
    //   `e >= 0`, two tests, as before;
    // - then `t <= 0`: a bound that the shift cuts takes two tests;
    // - a bound that `cut_dec` divides, with `t > 0`, takes these two and `e >= 0`.
    if t <= s {
        exact_dec(x)
    } else if t <= 0 {
        // min(e, 0) < t <= 0, so e < 0 and e < t. Then n = m * 5^-e and s = e, so
        // n / 10^(t - e) = m * 5^-t / 2^(t - e), without the powers of 5 that `cut_dec` would
        // divide by. 2^(t - e) divides m * 5^-t, as 5^-t is odd, iff it divides m, which is
        // never for t - e >= 64, as 0 < m < 2^53.
        let j = (t - e) as u64;
        let q = &(&Nat::from_u64(m) * &Nat::pow5(-t as u32)) >> j;
        if away && (j >= 64 || m & ((1 << j) - 1) != 0) {
            (&q + &Nat::from_u64(1), t)
        } else {
            (q, t)
        }
    } else {
        // `cut_dec` gets the `s` of the first test rather than the equal one of `exact_dec`, so
        // that the compiler can see that its `t <= s` is false here and drop it.
        cut_dec(exact_dec(x).0, s, t, away)
    }
}

// The precision from which `fixed` and `sci` keep every digit: `s >= -1074` in `exact_dec`,
// and `n` there has at most 767 digits, as `n < 2^1024` if `e >= 0` and
// `n < 2^53 * 5^1074 < 10^767` otherwise. Capping the precision there keeps it in an `i64`.
const ALL_DIGITS: usize = 1100;

/// `|x|` for `{:.p}`: `(d, k)` with `d * 10^k` the magnitude of `x` rounded to a multiple of
/// `10^-p`, toward -∞ for `x` if `up` is false, and toward +∞ otherwise, and `k >= -p`.
pub(super) fn fixed(x: f64, p: usize, up: bool) -> (Nat, i64) {
    cut(x, -(p.min(ALL_DIGITS) as i64), away(x, up))
}

// Whether `m * 2^e >= 10^k`, for `m > 0`.
fn ge_pow10(m: u64, e: i64, k: i64) -> bool {
    let m = Nat::from_u64(m);
    if k >= 0 {
        // 10^k = 5^k * 2^k, so this compares m * 2^(e - k) with 5^k.
        let p = Nat::pow5(k as u32);
        if e >= k {
            (&m << (e - k) as u64) >= p
        } else {
            m >= (&p << (k - e) as u64)
        }
    } else {
        // 10^k < 2^k for k < 0, so m * 2^e >= 2^e > 10^k if e >= k. Otherwise
        // m * 2^e >= 10^k = 2^k / 5^-k iff m * 5^-k >= 2^(k - e), which is iff m * 5^-k has
        // more than k - e bits.
        e >= k || (&m * &Nat::pow5(-k as u32)).bits() > (k - e) as u64
    }
}

// The `k` with `10^k <= m * 2^e < 10^(k + 1)`, for the `(m, e)` of `decompose`, with
// `0 < m < 2^53` and `-1074 <= e <= 971`.
fn lead(m: u64, e: i64) -> i64 {
    // 2^b <= m * 2^e < 2^(b + 1), with -1074 <= b <= 1023.
    let b = e + 63 - i64::from(m.leading_zeros());
    // 315653 / 2^20 is a little below log10(2), and g = floor(b * 315653 / 2^20) (`>>` of an
    // `i64` rounds toward -∞) has 10^g <= 2^b < 10^(g + 1) for each `b` from -1074 to 1023,
    // as `rocq/theories/FormatLead.v` and the test below check. So
    // 10^g <= m * 2^e < 2^(b + 1) < 10^(g + 2), and one comparison tells `k` from g and g + 1.
    let g = (b * 315653) >> 20;
    if ge_pow10(m, e, g + 1) {
        g + 1
    } else {
        g
    }
}

/// `|x|` for `{:.pe}`: `(d, k)` with `d * 10^k` the magnitude of `x` rounded to `p + 1`
/// significant digits, toward -∞ for `x` if `up` is false, and toward +∞ otherwise. `d` has
/// at most `p + 1` digits, or is `10^(p + 1)` if the rounding carries into a new digit.
pub(super) fn sci(x: f64, p: usize, up: bool) -> (Nat, i64) {
    let (m, e) = decompose(x);
    // The exponent of the last of the `p + 1` leading digits of `|x|`.
    let t = lead(m, e) - p.min(ALL_DIGITS) as i64;
    cut(x, t, away(x, up))
}

// `m` cut to a multiple of `2^j` and divided by it, for `j < 64`: rounded toward zero, or away
// from zero if `away`.
fn cut_bin(m: u64, j: u32, away: bool) -> u64 {
    let q = m >> j;
    if away && m & ((1 << j) - 1) != 0 {
        q + 1
    } else {
        q
    }
}

/// `|x|` for `{:x}` with the precision `p`: `(d, k)` with `d * 2^k` the magnitude of `x`
/// rounded toward -∞ for `x` if `up` is false, and toward +∞ otherwise, to as many digits as
/// MPFR's `%Ra` writes:
/// - without a precision, exactly, with `d` the 14 hex digits that make `d * 2^k = |x|` with
///   `16^13 <= d < 16^14` and `k + 52` a multiple of 4;
/// - with `p = 0`, to 4 bits, with `8 <= d <= 16`;
/// - with `p >= 1`, to `p + 1` hex digits, with `k + 52` a multiple of 4: `d` has `p + 1`
///   digits, or is `16^(p + 1)` if the rounding carries into a new digit, for `p < 13`, and is
///   the exact `d` above otherwise.
pub(super) fn hex(x: f64, p: Option<usize>, up: bool) -> (u64, i64) {
    let (m, e) = decompose(x);
    // m * 2^e = m53 * 2^(ex - 52) with 2^52 <= m53 < 2^53 for x != 0: `ex` is the exponent
    // of the leading bit.
    let lz = m.leading_zeros() - 11;
    let m53 = m << lz;
    let ex = e + 52 - i64::from(lz);
    let away = away(x, up);
    if p == Some(0) {
        // The leading 4 bits, a multiple of 2^(ex - 3).
        return (cut_bin(m53, 49, away), ex - 3);
    }
    // The leading hex digit holds the bits of the exponents from `ex` down to
    // 4 * floor(ex / 4), so that it holds 1 to 4 bits and |x| = d14 * 2^(4 * floor(ex / 4) - 52)
    // with 16^13 <= d14 < 16^14.
    let d14 = m53 << ex.rem_euclid(4);
    let k = 4 * ex.div_euclid(4) - 52;
    match p {
        Some(p) if p < 13 => {
            // The leading `p + 1` of the 14 digits.
            let j = 4 * (13 - p as u32);
            (cut_bin(d14, j, away), k + i64::from(j))
        }
        _ => (d14, k),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // 10^k for k >= 0.
    fn pow10(k: i64) -> Nat {
        &Nat::pow5(k as u32) << k as u64
    }

    // floor(log10(m * 2^e)) for m > 0, from the number of decimal digits of the integer
    // `n = m * 2^e * 10^-s`, with `s = min(e, 0)`, as in `exact_dec`.
    fn floor_log10(m: u64, e: i64) -> i64 {
        let m = Nat::from_u64(m);
        let (n, s) = if e >= 0 {
            (&m << e as u64, 0)
        } else {
            (&m * &Nat::pow5(-e as u32), e)
        };
        n.to_dec().len() as i64 + s - 1
    }

    // 2^b for each `b` of an `f64`, with the bits on each side of it, and 10^k for each `k`
    // of an `f64`, as the nearest `f64`, with the bits on each side of that.
    fn near_powers() -> Vec<f64> {
        let mut xs = Vec::new();
        for b in -1074..=1023i64 {
            let bits = if b >= -1022 {
                ((b + 1023) as u64) << 52
            } else {
                1 << (b + 1074)
            };
            xs.extend([bits - 1, bits, bits + 1].map(f64::from_bits));
        }
        for k in -323..=308 {
            let bits = format!("1e{}", k).parse::<f64>().unwrap().to_bits();
            xs.extend([bits - 1, bits, bits + 1].map(f64::from_bits));
        }
        xs.retain(|&x| x != 0.0);
        xs
    }

    // The estimate g of `lead` has 10^g <= 2^b < 10^(g + 1) at each `b` of an `f64`.
    #[test]
    fn lead_estimate() {
        let one = Nat::from_u64(1);
        for b in -1074..=1023i64 {
            let g = (b * 315653) >> 20;
            if b >= 0 {
                let p = &one << b as u64;
                assert!(pow10(g) <= p && p < pow10(g + 1), "b = {}", b);
            } else {
                // 10^g <= 2^b < 10^(g + 1) iff 10^(-g - 1) < 2^-b <= 10^-g.
                let p = &one << -b as u64;
                assert!(pow10(-g - 1) < p && p <= pow10(-g), "b = {}", b);
            }
        }
    }

    // `lead` is floor(log10 |x|), and `ge_pow10` tells whether |x| >= 10^k for the `k` around
    // it, beside the powers of 2 and of 10.
    #[test]
    fn lead_and_ge_pow10() {
        for x in near_powers() {
            let (m, e) = decompose(x);
            let l = floor_log10(m, e);
            assert_eq!(lead(m, e), l, "{:e}", x);
            for k in l - 2..=l + 2 {
                assert_eq!(ge_pow10(m, e, k), k <= l, "{:e}, k = {}", x, k);
            }
        }
    }
}
