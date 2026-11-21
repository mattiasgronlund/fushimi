// Tests of the roots of the dyadic kernel, on every platform, against an exact oracle of their
// own. At an argument where the root is r >= 0, the results lo toward -∞, hi toward +∞ and n to
// nearest are right if lo <= r <= hi, with lo = hi exactly when r is an `f64` and hi the `f64`
// after lo otherwise, and if n is lo or hi as r is below or above their midpoint, the one with
// an even significand when r is the midpoint (`check_root`). The oracle decides each of these
// comparisons in integers, with arithmetic of its own (`Nat`), not with `crate::limbs`, whose
// results it checks: r^3 = |x| for cbrt, whose value at -x is -cbrt x, and r^2 = x^2 + y^2 for
// hypot, so lo, hi and the midpoint compare with r as their cubes or squares compare with those,
// each an integer times a power of two. +∞ stands for 2^1024 there, whose significand is even,
// so that a root from 2^1024 - 2^970, the midpoint of MAX and 2^1024, on has to round to +∞ to
// nearest, as `near_round` in `rocq/theories/NearF64.v` says.
//
// The generators: random arguments, log-uniform and uniform in (-1, 1); every binade of cbrt;
// exact cubes and their neighbours; scaled Pythagorean triples, whose hypotenuses are exact or
// midpoints, and their neighbours; both sides of the cut of hypot at a gap of 27; results at the
// overflow threshold; and subnormal arguments. `src/cr.rs` compares the functions with MPFR.
//
// The fast paths in `f64` (`fast_cbrt_dir`, `fast_cbrt_near`, `fast_hypot` and
// `fast_hypot_near`) give the same `f64`s as the kernel, which `set_fast_path(false)` leaves
// alone, on random sets of their own, and most of their rounding tests pass there
// (`fast_counts`). Their directed rounding tests fail at the exact cubes and the exact results of
// hypot, which `cbrt_exact` and `hypot_exact` then give, and those decline the `f64`s next to
// them. The fast paths leave to the kernel the midpoints of hypot to nearest, the arguments whose
// root rounds to h = 2 in `fast_cbrt`, and the pairs that `hypot_dd` does not take. The rule of
// hypot at a gap of 27 in `fast_hypot`, on exponent fields, holds only where the gap of
// `hypot_odd` is 27 or more.

use super::*;
use crate::dyadic::fast::{fast_counts, reset_fast_counts, set_fast_path};
use crate::dyadic::tests::Rng;
use crate::simd::HAS_FMA;
use std::cmp::Ordering;

// A natural number, as digits in base 2^32 from the least significant, with no zero digit at
// the top, so that 0 has none.
#[derive(Clone, Debug)]
struct Nat(Vec<u32>);

impl Nat {
    fn new(n: u64) -> Nat {
        Nat(vec![n as u32, (n >> 32) as u32]).trimmed()
    }

    fn trimmed(mut self) -> Nat {
        while self.0.last() == Some(&0) {
            self.0.pop();
        }
        self
    }

    fn plus(&self, other: &Nat) -> Nat {
        let digit = |a: &Nat, i: usize| u64::from(a.0.get(i).copied().unwrap_or(0));
        let n = self.0.len().max(other.0.len());
        let (mut r, mut carry) = (Vec::with_capacity(n + 1), 0);
        for i in 0..n {
            let t = digit(self, i) + digit(other, i) + carry;
            r.push(t as u32);
            carry = t >> 32;
        }
        r.push(carry as u32);
        Nat(r).trimmed()
    }

    // Schoolbook multiplication. Each step is at most (2^32 - 1)^2 + 2 (2^32 - 1) = 2^64 - 1.
    fn times(&self, other: &Nat) -> Nat {
        let mut r = vec![0; self.0.len() + other.0.len()];
        for (i, &a) in self.0.iter().enumerate() {
            let mut carry = 0;
            for (j, &b) in other.0.iter().enumerate() {
                let t = u64::from(a) * u64::from(b) + u64::from(r[i + j]) + carry;
                r[i + j] = t as u32;
                carry = t >> 32;
            }
            r[i + other.0.len()] = carry as u32;
        }
        Nat(r).trimmed()
    }

    // self 2^k.
    fn shifted(&self, k: u64) -> Nat {
        let mut r = vec![0; (k / 32) as usize];
        let mut carry = 0;
        for &d in &self.0 {
            let t = u64::from(d) << (k % 32);
            r.push(t as u32 | carry);
            carry = (t >> 32) as u32;
        }
        r.push(carry);
        Nat(r).trimmed()
    }

    fn compare(&self, other: &Nat) -> Ordering {
        let (a, b) = (self.0.iter().rev(), other.0.iter().rev());
        self.0.len().cmp(&other.0.len()).then_with(|| a.cmp(b))
    }
}

// The number m 2^e.
#[derive(Clone, Debug)]
struct Num {
    m: Nat,
    e: i64,
}

impl Num {
    // The value of an `f64` v >= +0 from its bits, and 2^1024 for v = +∞.
    fn of(v: f64) -> Num {
        assert!(v.is_sign_positive() && !v.is_nan(), "{:e}", v);
        if v == f64::INFINITY {
            return Num {
                m: Nat::new(1),
                e: 1024,
            };
        }
        let (field, fraction) = ((v.to_bits() >> 52) as i64, v.to_bits() & ((1 << 52) - 1));
        if field == 0 {
            Num {
                m: Nat::new(fraction),
                e: -1074,
            }
        } else {
            Num {
                m: Nat::new(fraction | (1 << 52)),
                e: field - 1075,
            }
        }
    }

    // The two numbers as integers times 2^e, at the lower of their exponents e.
    fn aligned(&self, other: &Num) -> (Nat, Nat, i64) {
        let e = self.e.min(other.e);
        let a = self.m.shifted((self.e - e) as u64);
        (a, other.m.shifted((other.e - e) as u64), e)
    }

    fn plus(&self, other: &Num) -> Num {
        let (a, b, e) = self.aligned(other);
        Num { m: a.plus(&b), e }
    }

    fn half(self) -> Num {
        Num {
            m: self.m,
            e: self.e - 1,
        }
    }

    fn pow(&self, k: u32) -> Num {
        let mut m = Nat::new(1);
        for _ in 0..k {
            m = m.times(&self.m);
        }
        Num {
            m,
            e: self.e * i64::from(k),
        }
    }

    fn compare(&self, other: &Num) -> Ordering {
        let (a, b, _) = self.aligned(other);
        a.compare(&b)
    }
}

// Checks `lo`, `hi` and `near` as a root r >= 0 rounded toward -∞, toward +∞ and to nearest,
// ties to even, where r^k = `power`, as the header says. Returns whether r is the midpoint of
// lo and hi.
fn check_root(what: &str, k: u32, power: &Num, lo: f64, hi: f64, near: f64) -> bool {
    for v in [lo, hi, near] {
        assert!(v.is_sign_positive() && !v.is_nan(), "{}: {:e}", what, v);
    }
    assert!(lo.is_finite(), "{}: {:e} toward -∞", what, lo);
    let below = Num::of(lo).pow(k).compare(power);
    if lo.to_bits() == hi.to_bits() {
        assert_eq!(
            below,
            Ordering::Equal,
            "{}: {:e} in both directions, but the root is not an f64",
            what,
            lo
        );
        assert_eq!(
            near.to_bits(),
            lo.to_bits(),
            "{}: {:e} to nearest, {:e} in both directions",
            what,
            near,
            lo
        );
        return false;
    }
    assert_eq!(
        below,
        Ordering::Less,
        "{}: {:e} toward -∞ and {:e} toward +∞",
        what,
        lo,
        hi
    );
    // Positive `f64`s that are adjacent, +∞ after MAX included, have adjacent bits.
    assert_eq!(
        hi.to_bits(),
        lo.to_bits() + 1,
        "{}: {:e} and {:e} are not adjacent",
        what,
        lo,
        hi
    );
    // hypot reaches √2 MAX > 2^1024, so +∞ above MAX is checked only by lo < r.
    if hi.is_finite() {
        assert_eq!(
            Num::of(hi).pow(k).compare(power),
            Ordering::Greater,
            "{}: {:e} toward +∞ is not above the root",
            what,
            hi
        );
    }
    let mid = Num::of(lo).plus(&Num::of(hi)).half();
    let (want, tie) = match mid.pow(k).compare(power) {
        Ordering::Less => (hi, false),
        Ordering::Greater => (lo, false),
        // The bits of a positive `f64` end in its significand's, and +∞ has an even one.
        Ordering::Equal => (
            if lo.to_bits().is_multiple_of(2) {
                lo
            } else {
                hi
            },
            true,
        ),
    };
    assert_eq!(
        near.to_bits(),
        want.to_bits(),
        "{}: {:e} to nearest instead of {:e}",
        what,
        near,
        want
    );
    tie
}

// Checks cbrt at `x` in both directions and to nearest: ±∞ and NaN at ±∞ and NaN, the sign of
// `x` otherwise, and the roundings of cbrt |x| as the header says, where -cbrt x = cbrt(-x)
// swaps the directions at x < 0. cbrt has no midpoints (`src/dyadic/root.rs`).
fn check_cbrt(x: f64) {
    let (lo, hi, near) = (cbrt(x, false), cbrt(x, true), cbrt_near(x));
    let what = format!("cbrt({:e})", x);
    if !x.is_finite() {
        for v in [lo, hi, near] {
            let ok = if x.is_nan() { v.is_nan() } else { v == x };
            assert!(ok, "{}: {:e}", what, v);
        }
        return;
    }
    for v in [lo, hi, near] {
        assert_eq!(
            v.is_sign_negative(),
            x.is_sign_negative(),
            "{}: {:e}",
            what,
            v
        );
    }
    let tie = if x.is_sign_negative() {
        check_root(&what, 3, &Num::of(-x), -hi, -lo, -near)
    } else {
        check_root(&what, 3, &Num::of(x), lo, hi, near)
    };
    assert!(!tie, "{}: a midpoint", what);
}

// Checks hypot at (x, y) in both directions and to nearest: +∞ if `x` or `y` is infinite, NaN
// otherwise if one is NaN, and the roundings of √(x^2 + y^2) as the header says. Returns
// whether the root is a midpoint.
fn check_hypot(x: f64, y: f64) -> bool {
    let (lo, hi, near) = (hypot(x, y, false), hypot(x, y, true), hypot_near(x, y));
    let what = format!("hypot({:e}, {:e})", x, y);
    if !x.is_finite() || !y.is_finite() {
        let inf = x.is_infinite() || y.is_infinite();
        for v in [lo, hi, near] {
            let ok = if inf { v == f64::INFINITY } else { v.is_nan() };
            assert!(ok, "{}: {:e}", what, v);
        }
        return false;
    }
    let power = Num::of(x.abs()).pow(2).plus(&Num::of(y.abs()).pow(2));
    check_root(&what, 2, &power, lo, hi, near)
}

// 2^n, for n in [-1074, 1023].
fn pow2(n: i64) -> f64 {
    if n < -1022 {
        f64::from_bits(1 << (n + 1074))
    } else {
        f64::from_bits(u64::try_from(n + 1023).unwrap() << 52)
    }
}

// `x` and the `k` `f64`s on each side of it, for a finite `x`.
fn around(x: f64, k: usize) -> Vec<f64> {
    let (mut a, mut b) = (x, x);
    let mut v = vec![x];
    for _ in 0..k {
        a = f64::next_down(a);
        b = f64::next_up(b);
        v.push(a);
        v.push(b);
    }
    v
}

// A random `f64` log-uniform over (0, MAX]: its bits are uniform.
fn log_uniform(rng: &mut Rng) -> f64 {
    f64::from_bits(rng.below(0x7fef_ffff_ffff_ffff) + 1)
}

// A random `f64` uniform over (-1, 1), a multiple of 2^-53.
fn uniform(rng: &mut Rng) -> f64 {
    (rng.below((1 << 54) - 1) as i64 - ((1 << 53) - 1)) as f64 / 9_007_199_254_740_992.0
}

// -1 or 1 at random.
fn sign(rng: &mut Rng) -> f64 {
    if rng.below(2) == 0 {
        -1.0
    } else {
        1.0
    }
}

// Arguments on which mismatches were found, as `("cbrt", x, "")` or `("hypot", x, y)`, each
// with what it broke and where it was found.
fn regressions() -> Vec<(&'static str, &'static str, &'static str)> {
    vec![]
}

#[test]
fn regressions_hold() {
    for (name, x, y) in regressions() {
        let x: f64 = x.parse().unwrap();
        if name == "cbrt" {
            check_cbrt(x);
        } else {
            check_hypot(x, y.parse().unwrap());
        }
    }
}

// The arithmetic of the oracle against `u128`, and the values it gives to `f64`s.
#[test]
fn oracle() {
    let value = |n: &Nat| {
        assert!(n.0.len() <= 4);
        n.0.iter().rev().fold(0, |a, &d| (a << 32) | u128::from(d))
    };
    let mut rng = Rng(83);
    for _ in 0..10_000 {
        let (a, b) = (rng.next() >> rng.below(64), rng.next() >> rng.below(64));
        let (na, nb) = (Nat::new(a), Nat::new(b));
        assert_eq!(value(&na.plus(&nb)), u128::from(a) + u128::from(b));
        assert_eq!(value(&na.times(&nb)), u128::from(a) * u128::from(b));
        let k = rng.below(65);
        assert_eq!(value(&na.shifted(k)), u128::from(a) << k);
        assert_eq!(na.compare(&nb), a.cmp(&b));
    }
    let num = |m: u64, e: i64| Num { m: Nat::new(m), e };
    for (v, want) in [
        (0.0, num(0, 0)),
        (f64::from_bits(1), num(1, -1074)),
        (f64::MIN_POSITIVE, num(1, -1022)),
        (0.75, num(3, -2)),
        (f64::MAX, num((1 << 53) - 1, 971)),
        (f64::INFINITY, num(1, 1024)),
    ] {
        assert_eq!(Num::of(v).compare(&want), Ordering::Equal, "{:e}", v);
        let below = if v == 0.0 {
            Ordering::Less
        } else {
            Ordering::Greater
        };
        assert_eq!(Num::of(v).compare(&num(1, -1075)), below, "{:e}", v);
    }
    // (1 + 2) / 2 = 1.5, whose cube is 27 / 8.
    let mid = num(1, 0).plus(&num(1, 1)).half();
    assert_eq!(mid.pow(3).compare(&num(27, -3)), Ordering::Equal);
    assert_eq!(mid.pow(3).compare(&num(13, -2)), Ordering::Greater);
}

#[test]
fn smoke() {
    for (x, r) in [(27.0, 3.0), (-8.0, -2.0), (1.0, 1.0), (0.125, 0.5)] {
        assert_eq!(cbrt(x, false), r);
        assert_eq!(cbrt(x, true), r);
        assert_eq!(cbrt_near(x), r);
    }
    assert_eq!(cbrt(2.0, false).to_bits() + 1, cbrt(2.0, true).to_bits());
    // A midpoint: 2^53 + 2^27 + 1, whose tie goes to the even 2^53 + 2^27.
    let (x, y) = (134_217_729.0, 9_007_199_388_958_720.0);
    assert_eq!(hypot(x, y, false), 9_007_199_388_958_720.0);
    assert_eq!(hypot(x, y, true), 9_007_199_388_958_722.0);
    assert_eq!(hypot_near(x, y), 9_007_199_388_958_720.0);
    assert_eq!(hypot(3.0, 4.0, false), 5.0);
    assert_eq!(hypot(3.0, 4.0, true), 5.0);
    let tiny = f64::from_bits(1);
    assert_eq!(hypot(tiny, tiny, false), tiny);
    assert_eq!(hypot(tiny, tiny, true), f64::from_bits(2));
    assert_eq!(hypot_near(tiny, tiny), tiny);
    assert_eq!(hypot(f64::MAX, f64::MAX, false), f64::MAX);
    assert_eq!(hypot(f64::MAX, f64::MAX, true), f64::INFINITY);
    assert_eq!(hypot_near(f64::MAX, f64::MAX), f64::INFINITY);
}

// The zeros, the infinities, NaN and the ends of the finite range, and every pair of them.
#[test]
fn special_values() {
    let special = [
        0.0,
        f64::from_bits(1),
        f64::from_bits((1 << 52) - 1),
        f64::MIN_POSITIVE,
        1.0,
        f64::MAX,
        f64::INFINITY,
        f64::NAN,
    ];
    for &x in &special {
        check_cbrt(x);
        check_cbrt(-x);
        for &y in &special {
            for (x, y) in [(x, y), (-x, y), (x, -y), (-x, -y)] {
                check_hypot(x, y);
            }
        }
    }
    assert_eq!(hypot(-0.0, -0.0, false).to_bits(), 0);
    assert_eq!(hypot_near(-3.0, -0.0), 3.0);
    assert_eq!(hypot(f64::NAN, -f64::INFINITY, false), f64::INFINITY);
}

// Random arguments: log-uniform over (0, MAX] with a random sign, and uniform in (-1, 1).
#[test]
fn random() {
    let mut rng = Rng(83);
    for _ in 0..10_000 {
        let x = log_uniform(&mut rng) * sign(&mut rng);
        check_cbrt(x);
        check_cbrt(uniform(&mut rng));
        let (x, y) = (log_uniform(&mut rng), log_uniform(&mut rng));
        check_hypot(x * sign(&mut rng), y * sign(&mut rng));
        check_hypot(uniform(&mut rng), uniform(&mut rng));
    }
}

// Random pairs with a gap of g in [0, 60] binades: x log-uniform and y with the exponent field
// of x minus g and random bits below it, subnormal if that field is 0.
#[test]
fn random_gaps() {
    let mut rng = Rng(8301);
    for _ in 0..20_000 {
        let x = log_uniform(&mut rng);
        let field = (x.to_bits() >> 52).saturating_sub(rng.below(61));
        let y = f64::from_bits((field << 52) | rng.below(1 << 52));
        let (x, y) = (x * sign(&mut rng), y * sign(&mut rng));
        check_hypot(x, y);
        check_hypot(y, x);
    }
}

// Every binade of cbrt, which takes the exponent modulo 3 apart: at each exponent field, with
// the least and the greatest significand and random ones, at both signs.
#[test]
fn cbrt_every_binade() {
    let mut rng = Rng(8302);
    for field in 0..2047 {
        for fraction in [
            0,
            1,
            (1 << 52) - 1,
            rng.below(1 << 52),
            rng.below(1 << 52),
            rng.below(1 << 52),
        ] {
            let x = f64::from_bits((field << 52) | fraction);
            check_cbrt(x);
            check_cbrt(-x);
        }
    }
}

// The exact cubes x = y^3 of y = r 2^a with r odd and r^3 < 2^53, and x = r^3 2^(3 a) a finite
// `f64`, so that 3 a >= -1074, and the 2 `f64`s on each side of them.
#[test]
fn cbrt_cubes() {
    let mut rng = Rng(8303);
    for _ in 0..5_000 {
        // 208063^3 < 2^53 <= 208064^3.
        let r = 2 * rng.below(104_032) + 1;
        let cube = r * r * r;
        let bits = i64::from(64 - cube.leading_zeros());
        // The top bit of x is 2^(bits - 1 + 3 a), at most 2^1023.
        let a = -358 + rng.below(u64::try_from((1024 - bits) / 3 + 359).unwrap()) as i64;
        let (x, y) = (cube as f64 * pow2(3 * a), r as f64 * pow2(a));
        for s in [-1.0, 1.0] {
            let x = s * x;
            assert_eq!(cbrt(x, false), s * y, "cbrt({:e})", x);
            assert_eq!(cbrt(x, true), s * y, "cbrt({:e})", x);
            for x in around(x, 2) {
                check_cbrt(x);
            }
        }
    }
}

// Whether the integer `v` < 2^54 is an `f64`.
fn is_f64(v: u64) -> bool {
    v < 1 << 53 || v.is_multiple_of(2)
}

// Scaled Pythagorean triples: legs t (m^2 - n^2) and 2 t m n and hypotenuse c = t (m^2 + n^2)
// for m > n > 0 and t = 1 or 3, the legs `f64`s and c < 2^54, scaled by 2^k with k in
// [-1074, 970] (and so often subnormal legs) and the `f64` on each side of each leg. c 2^k is
// the exact result if c is an `f64`, and otherwise c is odd in [2^53, 2^54), so that m and n
// have opposite parities, and c 2^k is the midpoint of (c - 1) 2^k toward -∞ and (c + 1) 2^k
// toward +∞, with an even significand (c ± 1) / 2 to nearest: (c - 1) / 2 at t = 1, as
// m^2 + n^2 is then 1 modulo 4, and (c + 1) / 2 at t = 3. The triples are drawn from four
// shapes: m in [2^26, 2^27) and n below it, mostly midpoints at gaps of a few binades; m = n + d
// with d odd below 2^20 and n in [2^26, 2^26.5), midpoints whose short leg (2 n + d) d gives
// gaps up to 26, as in `smoke`; m below 2^25 + 2, under a random power of two, exact results;
// and t = 3 with m in [3 2^24, 5 2^24), midpoints whose ties go up.
#[test]
fn hypot_triples() {
    let mut rng = Rng(8304);
    let (mut exact, mut midpoints, mut ups) = (0, 0, 0);
    while exact + midpoints < 6_000 {
        let (m, n, t) = match rng.below(4) {
            0 => {
                let m = (1 << 26) + rng.below(1 << 26);
                (m, 1 + rng.below(m - 1), 1)
            }
            1 => {
                let (n, bits) = ((1 << 26) + rng.below(27_797_401), rng.below(20));
                (n + 2 * rng.below(1 << bits) + 1, n, 1)
            }
            2 => {
                let bits = rng.below(26);
                let m = 2 + rng.below(1 << bits);
                (m, 1 + rng.below(m - 1), 1)
            }
            _ => {
                let m = (3 << 24) + rng.below(1 << 25);
                (m, 1 + rng.below(m - 1), 3)
            }
        };
        let (a, b, c) = (t * (m * m - n * n), 2 * t * m * n, t * (m * m + n * n));
        if !(c < 1 << 54 && is_f64(a) && is_f64(b)) {
            continue;
        }
        let k = match rng.below(4) {
            0 => -1074 + rng.below(64) as i64,
            1 => 970 - rng.below(64) as i64,
            _ => -1074 + rng.below(2045) as i64,
        };
        let (mut x, mut y) = (a as f64 * pow2(k), b as f64 * pow2(k));
        if rng.below(2) == 0 {
            std::mem::swap(&mut x, &mut y);
        }
        let (x, y) = (x * sign(&mut rng), y * sign(&mut rng));
        let what = format!("hypot({:e}, {:e})", x, y);
        let tie = check_hypot(x, y);
        let (lo, hi, near) = (hypot(x, y, false), hypot(x, y, true), hypot_near(x, y));
        if is_f64(c) {
            exact += 1;
            let r = c as f64 * pow2(k);
            assert!(!tie && lo == r && hi == r, "{}", what);
        } else {
            midpoints += 1;
            let (down, up) = ((c - 1) as f64 * pow2(k), (c + 1) as f64 * pow2(k));
            let even = if (c - 1) % 4 == 0 {
                down
            } else {
                ups += 1;
                up
            };
            assert!(tie && lo == down && hi == up && near == even, "{}", what);
        }
        for x in around(x, 1) {
            for y in around(y, 1) {
                check_hypot(x, y);
            }
        }
    }
    assert!(
        exact > 1_000 && midpoints > 2_000 && ups > 100,
        "{} {} {}",
        exact,
        midpoints,
        ups
    );
}

// The cut of hypot (`hypot_odd`): pairs of |x| >= |y| whose gap, the binade of x minus that of
// y, is g = 26, 27 and 28, and the `f64` on each side of each, with random signs. y = x 2^-g;
// random significands; y as near the next binade as it gets, after a power of two x, where
// hypot(x, y) - x is nearest to half an ulp of x; and subnormal y.
#[test]
fn hypot_cut() {
    let mut rng = Rng(8305);
    for g in 26..=28 {
        for _ in 0..1_000 {
            let field = g + 1 + rng.below(2046 - g);
            let fractions = [0, (1 << 52) - 1, rng.below(1 << 52)];
            let fx = fractions[rng.below(3) as usize];
            let fy = [fx, fractions[rng.below(3) as usize]][rng.below(2) as usize];
            let x = f64::from_bits((field << 52) | fx);
            let y = f64::from_bits(((field - g) << 52) | fy);
            let e = field as i64 - 1023;
            let tiny = f64::from_bits(1 + rng.below((1 << 52) - 1));
            let pairs = [
                (x, x * pow2(-(g as i64))),
                (x, y),
                (pow2(e), f64::next_down(pow2(e + 1 - g as i64))),
                (tiny * pow2(g as i64), tiny),
            ];
            for (x, y) in pairs {
                for x in around(x * sign(&mut rng), 1) {
                    for y in around(y * sign(&mut rng), 1) {
                        check_hypot(x, y);
                        check_hypot(y, x);
                    }
                }
            }
        }
    }
}

// Results at the overflow threshold: hypot(t, t) for t near MAX / √2, and hypot(x, y) for x at
// MAX and the two `f64`s below it and y near 2^997.5, 2^997 and 2^998, whose results cross
// 2^1024 - 2^970, where nearest turns from MAX to +∞, and MAX, where the directions turn.
#[test]
fn hypot_overflow() {
    for x in around(f64::MAX / std::f64::consts::SQRT_2, 3) {
        for y in around(f64::MAX / std::f64::consts::SQRT_2, 3) {
            check_hypot(x, y);
        }
    }
    let mut ys = around(std::f64::consts::SQRT_2 * pow2(997), 4);
    let nears: Vec<f64> = ys.iter().map(|&y| hypot_near(f64::MAX, y)).collect();
    assert!(nears.contains(&f64::MAX) && nears.contains(&f64::INFINITY));
    ys.extend(around(pow2(997), 2));
    ys.extend(around(pow2(998), 2));
    ys.extend([1.0, f64::MAX / 2.0, f64::next_down(f64::MAX), f64::MAX]);
    for x in [
        f64::MAX,
        f64::next_down(f64::MAX),
        f64::next_down(f64::next_down(f64::MAX)),
    ] {
        for &y in &ys {
            for (x, y) in [(x, y), (y, x), (-x, y), (x, -y)] {
                check_hypot(x, y);
            }
        }
    }
}

// Subnormal arguments: all pairs of i 2^-1074 and j 2^-1074 for i, j <= 40, random pairs below
// 2^-1020, and the cube roots of i 2^-1074 for i <= 1000 and of random subnormals.
#[test]
fn subnormals() {
    for i in 0..=40 {
        for j in 0..=40 {
            check_hypot(f64::from_bits(i), f64::from_bits(j));
        }
    }
    for i in 0..=1_000 {
        check_cbrt(f64::from_bits(i));
        check_cbrt(-f64::from_bits(i));
    }
    let mut rng = Rng(8306);
    for _ in 0..5_000 {
        let x = f64::from_bits(rng.below(1 << 54)) * sign(&mut rng);
        let y = f64::from_bits(rng.below(1 << 54)) * sign(&mut rng);
        check_hypot(x, y);
        check_cbrt(f64::from_bits(rng.below(1 << 52)) * sign(&mut rng));
    }
}

// The roundings of cbrt at `x`: toward -∞, toward +∞ and to nearest.
fn cbrt3(x: f64) -> [f64; 3] {
    [cbrt(x, false), cbrt(x, true), cbrt_near(x)]
}

// The roundings of hypot at (x, y), as `cbrt3`.
fn hypot3(x: f64, y: f64) -> [f64; 3] {
    [hypot(x, y, false), hypot(x, y, true), hypot_near(x, y)]
}

// Checks that `fast`, with the fast path, and `kernel`, without it, are the same `f64`s.
fn assert_same(what: &str, fast: [f64; 3], kernel: [f64; 3]) {
    assert!(
        fast.iter()
            .zip(&kernel)
            .all(|(a, b)| a.to_bits() == b.to_bits()),
        "{}: {:?} with the fast path != {:?} without it",
        what,
        fast,
        kernel
    );
}

// cbrt gives the same `f64`s at `x`, in both directions and to nearest, with the fast path as
// without it, and they are right, as `check_cbrt` checks them. `check_cbrt` runs without the fast
// path, so that each call adds the three rounding tests of `cbrt3` to `fast_counts`, no more.
fn check_fast_cbrt(x: f64) {
    let fast = cbrt3(x);
    set_fast_path(false);
    let kernel = cbrt3(x);
    check_cbrt(x);
    set_fast_path(true);
    assert_same(&format!("cbrt({:e})", x), fast, kernel);
}

// `check_fast_cbrt` for hypot at (x, y).
fn check_fast_hypot(x: f64, y: f64) {
    let fast = hypot3(x, y);
    set_fast_path(false);
    let kernel = hypot3(x, y);
    check_hypot(x, y);
    set_fast_path(true);
    assert_same(&format!("hypot({:e}, {:e})", x, y), fast, kernel);
}

// The binade of a finite nonzero `v`, floor(log2 |v|), from the exponent of `Dyadic::from_f64`,
// as `hypot_odd` takes it, up to the constant 63.
fn binade(v: f64) -> i64 {
    Dyadic::<1>::from_f64(v).exp
}

// The exponent field of an `f64`.
fn field(v: f64) -> i64 {
    ((v.to_bits() >> 52) & 0x7ff) as i64
}

// big = max(|x|, |y|) and small = min(|x|, |y|), as `fast_hypot` orders them, and whether it
// takes them by its rule for a gap of 27 or more: their exponent fields differ by 27 or more.
fn far_pair(x: f64, y: f64) -> (f64, f64, bool) {
    let (big, small) = if x.abs() >= y.abs() {
        (x.abs(), y.abs())
    } else {
        (y.abs(), x.abs())
    };
    (big, small, field(big) - field(small) >= 27)
}

// A named set of random arguments of cbrt, and one of pairs of hypot with whether the fast path
// takes most of them.
type CbrtSet = (&'static str, fn(&mut Rng) -> f64);
type HypotSet = (&'static str, fn(&mut Rng) -> (f64, f64), bool);

// The random arguments of cbrt of `fast_cbrt_agrees_with_kernel`.
fn cbrt_sets() -> [CbrtSet; 3] {
    [
        ("log-uniform", |rng| log_uniform(rng) * sign(rng)),
        ("uniform", uniform),
        ("subnormal", |rng| {
            f64::from_bits(rng.below(1 << 52)) * sign(rng)
        }),
    ]
}

// The random pairs of hypot of `fast_hypot_agrees_with_kernel`.
fn hypot_sets() -> [HypotSet; 6] {
    [
        ("uniform", |rng| (uniform(rng), uniform(rng)), true),
        (
            "log-uniform",
            |rng| (log_uniform(rng) * sign(rng), log_uniform(rng) * sign(rng)),
            true,
        ),
        (
            "gaps 0-40",
            |rng| gap_pair(rng, f64::from_bits(1), 40),
            true,
        ),
        (
            "gaps 0-26",
            |rng| gap_pair(rng, f64::from_bits(1), 26),
            true,
        ),
        (
            "big at least 2^1022",
            |rng| gap_pair(rng, pow2(1022), 40),
            false,
        ),
        (
            "subnormal",
            |rng| {
                let x = f64::from_bits(rng.below(1 << 52)) * sign(rng);
                (x, f64::from_bits(rng.below(1 << 52)) * sign(rng))
            },
            false,
        ),
    ]
}

// A pair with a gap of g in [0, `max`] binades, as in `random_gaps`, but from an x whose bits are
// uniform from those of `least` to those of MAX, in a random order and with random signs.
fn gap_pair(rng: &mut Rng, least: f64, max: u64) -> (f64, f64) {
    let x = f64::from_bits(least.to_bits() + rng.below(0x7ff0_0000_0000_0000 - least.to_bits()));
    let field = (x.to_bits() >> 52).saturating_sub(rng.below(max + 1));
    let y = f64::from_bits((field << 52) | rng.below(1 << 52));
    let (x, y) = (x * sign(rng), y * sign(rng));
    if rng.below(2) == 0 {
        (x, y)
    } else {
        (y, x)
    }
}

// cbrt with the fast path agrees with the kernel on random arguments: log-uniform over (0, MAX]
// and subnormal, each with a random sign, and uniform in (-1, 1). `fast_cbrt` takes every one of
// them (its check of the residual does not fail), and the rounding tests fail only where l is
// within `ERR_CBRT` = 2^-65 of 0 (toward ±∞) or of half the gap at h (to nearest), for about 2^-12
// of the arguments each.
#[test]
fn fast_cbrt_agrees_with_kernel() {
    let mut rng = Rng(106);
    for (name, arg) in cbrt_sets() {
        reset_fast_counts();
        for _ in 0..10_000 {
            let x = arg(&mut rng);
            assert!(
                x == 0.0 || fast_cbrt::<HAS_FMA>(x).is_some(),
                "fast_cbrt({:e})",
                x
            );
            check_fast_cbrt(x);
        }
        let (passed, failed) = fast_counts();
        assert!(
            passed > 500 * failed && passed > 29_000,
            "cbrt, {}: {} passed, {} failed",
            name,
            passed,
            failed
        );
    }
}

// hypot with the fast path agrees with the kernel on random pairs: uniform in (-1, 1),
// log-uniform over (0, MAX] with random signs, and with gaps of 0 to 40 and of 0 to 26 binades,
// which the fast path takes; and two that `hypot_dd` declines unless the gap is 27 or more (at a
// big of 2^1022 or more), or always (two subnormals). On each set, every pair goes to the rule
// for a gap of 27 or more (a pass without a rounding test), to a decline of `hypot_dd` (a failure
// without one) or to three rounding tests, which fail only where l is within `ERR_HYPOT` = 2^-98
// of 0 or of half the gap at h, or where h is 1/2.
#[test]
fn fast_hypot_agrees_with_kernel() {
    let mut rng = Rng(1060);
    for (name, pair, taken) in hypot_sets() {
        reset_fast_counts();
        let (mut nonzero, mut far, mut declined) = (0, 0, 0);
        for _ in 0..5_000 {
            let (x, y) = pair(&mut rng);
            if x != 0.0 && y != 0.0 {
                nonzero += 1;
                let (big, small, is_far) = far_pair(x, y);
                if is_far {
                    far += 1;
                } else if hypot_dd::<HAS_FMA>(big, small).is_none() {
                    declined += 1;
                }
            }
            check_fast_hypot(x, y);
        }
        let (passed, failed) = fast_counts();
        let what = format!(
            "hypot, {}: {} passed, {} failed, {} far, {} declined of {}",
            name, passed, failed, far, declined, nonzero
        );
        // Three rounding tests for each pair that goes neither to the rule nor to a decline.
        assert_eq!(passed + failed, 3 * (nonzero - far - declined), "{}", what);
        let (hits, misses) = (passed + 3 * far, failed + 3 * declined);
        if taken {
            assert!(
                hits > 100 * misses && passed > 1000 * failed && hits > 14_000,
                "{}",
                what
            );
        } else {
            assert!(passed + failed == 0 && declined > 0, "{}", what);
        }
    }
}

// cbrt at `x` as `cbrt3` gives it, by the copy of each entry without an FMA in its products, by
// the copy with one (`level_entry!`), and by the entries, which call one of the two.
fn cbrt_copies(x: f64) -> [[f64; 3]; 3] {
    [
        [
            cbrt_with::<false>(x, false),
            cbrt_with::<false>(x, true),
            cbrt_near_with::<false>(x),
        ],
        [
            cbrt_with::<true>(x, false),
            cbrt_with::<true>(x, true),
            cbrt_near_with::<true>(x),
        ],
        cbrt3(x),
    ]
}

// `cbrt_copies` for hypot at (x, y).
fn hypot_copies(x: f64, y: f64) -> [[f64; 3]; 3] {
    [
        [
            hypot_dir_with::<false, false>(x, y),
            hypot_dir_with::<false, true>(x, y),
            hypot_near_with::<false>(x, y),
        ],
        [
            hypot_dir_with::<true, false>(x, y),
            hypot_dir_with::<true, true>(x, y),
            hypot_near_with::<true>(x, y),
        ],
        hypot3(x, y),
    ]
}

// Checks that the three rows of `copies` are the same `f64`s.
fn assert_copies_agree(what: &str, copies: [[f64; 3]; 3]) {
    let bits = copies.map(|row| row.map(f64::to_bits));
    assert!(
        bits[0] == bits[1] && bits[1] == bits[2],
        "{what}: {:?} without an FMA, {:?} with one, {:?} by the entries",
        copies[0],
        copies[1],
        copies[2]
    );
}

// The copies of cbrt and hypot without an FMA and with one, and the entries, give the same `f64`s,
// bit for bit, in both directions and to nearest, on the random arguments of
// `fast_cbrt_agrees_with_kernel` and `fast_hypot_agrees_with_kernel` and on `regressions()`.
// `rocq/theories/FastCbrt.v` and `rocq/theories/FastHypot.v` prove it of the fast paths
// (`fast_cbrt_dir_fma`, `fast_hypot_dir_fma` and the others); this test checks the code as
// compiled, where the entries call the copy built with the target feature `fma` in a build with
// the dispatch, on a CPU that has it.
#[test]
fn copies_agree() {
    let mut rng = Rng(1062);
    for (_, arg) in cbrt_sets() {
        for _ in 0..10_000 {
            let x = arg(&mut rng);
            assert_copies_agree(&format!("cbrt({x:e})"), cbrt_copies(x));
        }
    }
    for (_, pair, _) in hypot_sets() {
        for _ in 0..5_000 {
            let (x, y) = pair(&mut rng);
            assert_copies_agree(&format!("hypot({x:e}, {y:e})"), hypot_copies(x, y));
        }
    }
    for (name, x, y) in regressions() {
        let x: f64 = x.parse().unwrap();
        if name == "cbrt" {
            assert_copies_agree(&format!("cbrt({x:e})"), cbrt_copies(x));
        } else {
            let y: f64 = y.parse().unwrap();
            assert_copies_agree(&format!("hypot({x:e}, {y:e})"), hypot_copies(x, y));
        }
    }
}

// The odd r of the exact cubes (r 2^a)^3 of `fast_cbrt_takes_cubes` and
// `fast_cbrt_declines_next_to_cubes`: small ones, 208_063, the largest r with r^3 < 2^53, and
// random odd ones up to it, as in `cbrt_cubes`.
fn cube_roots() -> Vec<u64> {
    let mut rng = Rng(10601);
    let mut rs = vec![1, 3, 5, 7, 9, 11, 13, 15, 255, 1001, 208_063];
    rs.extend((0..200).map(|_| 2 * rng.below(104_032) + 1));
    rs
}

// The exact cubes x = y^3 of y = r 2^a of `cube_roots` at every a, at both signs: the fast paths
// give y in both directions and to nearest. The directed rounding tests fail there, as l is
// within `ERR_CBRT` of 0, so `cbrt_exact` gives |y|, whose sign `fast_cbrt_dir` restores.
#[test]
fn fast_cbrt_takes_cubes() {
    for r in cube_roots() {
        let cube = r * r * r;
        let bits = i64::from(64 - cube.leading_zeros());
        // The top bit of x is 2^(bits - 1 + 3 a), at most 2^1023, and x is at least 2^-1074.
        for a in -358..=(1024 - bits) / 3 {
            let (x, y) = (cube as f64 * pow2(3 * a), r as f64 * pow2(a));
            for s in [-1.0, 1.0] {
                let (x, y) = (s * x, s * y);
                let what = format!("cbrt({:e})", x);
                reset_fast_counts();
                assert_eq!(
                    fast_cbrt_dir::<HAS_FMA>(x, false).map(f64::to_bits),
                    Some(y.to_bits()),
                    "{} toward -∞",
                    what
                );
                assert_eq!(
                    fast_cbrt_dir::<HAS_FMA>(x, true).map(f64::to_bits),
                    Some(y.to_bits()),
                    "{} toward +∞",
                    what
                );
                assert_eq!(fast_counts(), (0, 2), "{}", what);
                assert_eq!(
                    fast_cbrt_near::<HAS_FMA>(x).map(f64::to_bits),
                    Some(y.to_bits()),
                    "{} to nearest",
                    what
                );
            }
        }
    }
}

// `cbrt_exact` at a finite nonzero `x`, with the (h, e) that `fast_cbrt` gives there, against the
// kernel: it gives |cbrt x| where the kernel's roundings toward -∞ and +∞ agree, as cbrt x is
// then an `f64`, and `None` elsewhere. Where the directed rounding tests fail, `fast_cbrt_dir`
// gives that value with the sign of `x`. Checks the fast paths at `x` with `check_fast_cbrt`
// too. Returns whether `cbrt_exact` declined and whether the directed tests failed, or `None`
// where `fast_cbrt` does.
fn check_cbrt_exact(x: f64) -> Option<(bool, bool)> {
    check_fast_cbrt(x);
    let (h, _, e) = fast_cbrt::<HAS_FMA>(x)?;
    set_fast_path(false);
    let (lo, hi) = (cbrt(x, false), cbrt(x, true));
    set_fast_path(true);
    let want = (lo == hi).then_some(lo.abs());
    let what = format!("cbrt({:e})", x);
    assert_eq!(
        cbrt_exact(x, h, e).map(f64::to_bits),
        want.map(f64::to_bits),
        "cbrt_exact({:e}, {:e}, {}) for {}",
        x,
        h,
        e,
        what
    );
    reset_fast_counts();
    let dir = [
        fast_cbrt_dir::<HAS_FMA>(x, false),
        fast_cbrt_dir::<HAS_FMA>(x, true),
    ];
    let (_, failed) = fast_counts();
    if failed > 0 {
        let want = want.map(|c| if x < 0.0 { -c } else { c });
        assert_eq!(dir, [want; 2], "{}", what);
    }
    Some((want.is_none(), failed > 0))
}

// The `f64`s next to the exact cubes x = (r 2^a)^3 of `fast_cbrt_takes_cubes`, at both signs, for
// a sample of the a there: -358 to -356 and a random a from -358 to -341, where x is subnormal
// for cubes below 2^(-1022 - 3 a), the two highest a, and eight random ones. `cbrt_exact`
// declines each of them (`check_cbrt_exact`), and the kernel gives the results. The directed
// rounding tests fail where h = 2, below a normal x = 2^(3 a) (`fast_cbrt_near_two`): h = 2
// passes the test of the 35 low bits in `cbrt_exact`, but the odd part of x, 2^53 - 1, is not 1.
#[test]
fn fast_cbrt_declines_next_to_cubes() {
    let mut rng = Rng(10603);
    let (mut declined, mut failed, mut checked) = (0, 0, 0);
    for r in cube_roots() {
        let cube = r * r * r;
        let bits = i64::from(64 - cube.leading_zeros());
        let top = (1024 - bits) / 3;
        let span = |lo: i64, hi: i64| u64::try_from(hi - lo + 1).unwrap();
        let mut aa = vec![-358, -357, -356, top - 1, top];
        aa.push(-358 + rng.below(span(-358, -341)) as i64);
        aa.extend((0..8).map(|_| -358 + rng.below(span(-358, top)) as i64));
        for a in aa {
            let x = cube as f64 * pow2(3 * a);
            for x in [x, -x] {
                for x in [f64::next_down(x), f64::next_up(x)] {
                    if x == 0.0 {
                        continue;
                    }
                    if let Some((d, f)) = check_cbrt_exact(x) {
                        checked += 1;
                        declined += usize::from(d);
                        failed += usize::from(f);
                    }
                }
            }
        }
    }
    assert!(
        declined == checked && failed > 0 && checked > 5_000,
        "{} declined, {} failed, {} checked",
        declined,
        failed,
        checked
    );
}

// Arguments next to 8 2^(3 a), for every a, at both signs: where cbrt x 2^-e is next to 2, the fast
// path declines or gives the `f64` of `cbrt_odd`. At the `f64` below a normal 8 2^(3 a), the root
// is 2 (1 - 2^-53 / 3 + ...) 2^a, within a third of an ulp of 2^(a + 1), so h = 2, which the
// rounding tests decline as outside (1/2, 2).
#[test]
fn fast_cbrt_near_two() {
    let mut twos = 0;
    for a in -358..=340 {
        let p = pow2(3 * a + 3);
        for x in around(p, 4) {
            for x in [x, -x] {
                let odd = cbrt_odd(x);
                for up in [false, true] {
                    if let Some(r) = fast_cbrt_dir::<HAS_FMA>(x, up) {
                        let want = odd.to_f64(up);
                        assert_eq!(r.to_bits(), want.to_bits(), "cbrt({:e}, {})", x, up);
                    }
                }
                if let Some(r) = fast_cbrt_near::<HAS_FMA>(x) {
                    let want = odd.to_f64_near();
                    assert_eq!(r.to_bits(), want.to_bits(), "cbrt_near({:e})", x);
                }
            }
        }
        if p >= pow2(-1021) {
            twos += 1;
            let x = f64::next_down(p);
            let h = fast_cbrt::<HAS_FMA>(x).map(|(h, _, _)| h);
            assert_eq!(h, Some(2.0), "fast_cbrt({:e})", x);
            let fast = [
                fast_cbrt_dir::<HAS_FMA>(x, false),
                fast_cbrt_dir::<HAS_FMA>(x, true),
                fast_cbrt_near::<HAS_FMA>(x),
            ];
            assert_eq!(fast, [None; 3], "cbrt({:e})", x);
        }
    }
    assert!(twos > 600, "{}", twos);
}

// hypot(3 2^k, 4 2^k) = 5 2^k, an exact result, for every k, at all signs and in both orders:
// where `hypot_dd` takes the pair, for big = 4 2^k from 2^-1022 to 2^1021, the fast paths give
// 5 2^k in both directions and to nearest, the directed ones by `hypot_exact`, as their rounding
// tests fail with l within `ERR_HYPOT` of 0, and elsewhere they decline it with no test.
#[test]
fn fast_hypot_takes_345() {
    for k in -1074..=1021 {
        let (x, y, c) = (3.0 * pow2(k), 4.0 * pow2(k), 5.0 * pow2(k));
        let (want, tests) = if (-1024..=1019).contains(&k) {
            (Some(c), (0, 2))
        } else {
            (None, (0, 0))
        };
        for (x, y) in [(x, y), (-y, x), (y, -x), (-x, -y)] {
            let what = format!("hypot({:e}, {:e})", x, y);
            reset_fast_counts();
            assert_eq!(
                fast_hypot::<HAS_FMA>(x, y, false),
                want,
                "{} toward -∞",
                what
            );
            assert_eq!(
                fast_hypot::<HAS_FMA>(x, y, true),
                want,
                "{} toward +∞",
                what
            );
            assert_eq!(fast_counts(), tests, "{}", what);
            assert_eq!(
                fast_hypot_near::<HAS_FMA>(x, y),
                want,
                "{} to nearest",
                what
            );
        }
    }
}

// The legs a and b of a Pythagorean triple, `f64`s, under a random power of two 2^k at which
// `hypot_dd` takes the pair, big from 2^-1022 to below 2^1022: k at either end of that range or
// in it. Returns (x, y, k) with the legs in a random order and with random signs.
fn dd_scaled(rng: &mut Rng, a: u64, b: u64) -> (f64, f64, i64) {
    // big = max(a, b) 2^k with 2^(bits - 1) <= max(a, b) < 2^bits, so 2^-1022 <= big < 2^1022
    // for k in [-1021 - bits, 1022 - bits]. The legs are exact at each k from -1074 on.
    let bits = i64::from(64 - a.max(b).leading_zeros());
    let (lo, hi) = ((-1021 - bits).max(-1074), 1022 - bits);
    let k = match rng.below(4) {
        0 => lo,
        1 => hi,
        _ => lo + rng.below(u64::try_from(hi - lo + 1).unwrap()) as i64,
    };
    let (mut x, mut y) = (a as f64 * pow2(k), b as f64 * pow2(k));
    if rng.below(2) == 0 {
        std::mem::swap(&mut x, &mut y);
    }
    (x * sign(rng), y * sign(rng), k)
}

// A scaled Pythagorean triple of `fast_hypot_takes_triples`, as (x, y, c, k) with
// hypot(x, y) = c 2^k by `dd_scaled`, or `None` where the legs are not `f64`s or c is 2^54 or
// more: legs m^2 - n^2 and 2 m n and c = m^2 + n^2, for m below 2^25 + 2 or m = n + d with d odd
// below 2^20 and n in [2^26, 2^26.5), half of the draws each.
fn dd_triple(rng: &mut Rng) -> Option<(f64, f64, u64, i64)> {
    let (m, n) = if rng.below(2) == 0 {
        let bits = rng.below(26);
        let m = 2 + rng.below(1 << bits);
        (m, 1 + rng.below(m - 1))
    } else {
        let (n, bits) = ((1 << 26) + rng.below(27_797_401), rng.below(20));
        (n + 2 * rng.below(1 << bits) + 1, n)
    };
    let (a, b, c) = (m * m - n * n, 2 * m * n, m * m + n * n);
    if !(c < 1 << 54 && is_f64(a) && is_f64(b)) {
        return None;
    }
    let (x, y, k) = dd_scaled(rng, a, b);
    Some((x, y, c, k))
}

// Scaled Pythagorean triples, as in `hypot_triples`, under a power of two 2^k at which `hypot_dd`
// takes the pair (`dd_triple`). Exact results, from m below 2^25 + 2: the fast paths give c 2^k
// in both directions and to nearest, the directed ones by `hypot_exact`, as their rounding tests
// fail with l within `ERR_HYPOT` of 0. Midpoints, from m = n + d with d odd below 2^20 and n in
// [2^26, 2^26.5), at gaps up to 26: the one to nearest declines them, as its test is strict, and
// the directed ones give (c - 1) 2^k and (c + 1) 2^k, as the kernel does. The midpoint of `smoke`
// first.
#[test]
fn fast_hypot_takes_triples() {
    let (x, y) = (134_217_729.0, 9_007_199_388_958_720.0);
    assert_eq!(fast_hypot_near::<HAS_FMA>(x, y), None);
    assert_eq!(
        fast_hypot::<HAS_FMA>(x, y, false),
        Some(9_007_199_388_958_720.0)
    );
    assert_eq!(
        fast_hypot::<HAS_FMA>(x, y, true),
        Some(9_007_199_388_958_722.0)
    );
    let mut rng = Rng(10602);
    let (mut exact, mut midpoints) = (0, 0);
    while exact + midpoints < 4_000 {
        let Some((x, y, c, k)) = dd_triple(&mut rng) else {
            continue;
        };
        let what = format!("hypot({:e}, {:e})", x, y);
        reset_fast_counts();
        let dir = [
            fast_hypot::<HAS_FMA>(x, y, false),
            fast_hypot::<HAS_FMA>(x, y, true),
        ];
        let tests = fast_counts();
        let near = fast_hypot_near::<HAS_FMA>(x, y);
        if is_f64(c) {
            exact += 1;
            let r = c as f64 * pow2(k);
            assert!(
                dir == [Some(r); 2] && tests == (0, 2) && near == Some(r),
                "{}: {:?} {:?} {:?}",
                what,
                dir,
                tests,
                near
            );
        } else {
            midpoints += 1;
            let (down, up) = ((c - 1) as f64 * pow2(k), (c + 1) as f64 * pow2(k));
            let want = [Some(down), Some(up)];
            assert!(
                dir == want && near.is_none(),
                "{}: {:?} {:?}",
                what,
                dir,
                near
            );
        }
    }
    assert!(
        exact > 1_000 && midpoints > 1_000,
        "{} {}",
        exact,
        midpoints
    );
}

// `hypot_exact` at finite nonzero `x` and `y`, with the (h, e) that `hypot_dd` gives where
// `fast_hypot` calls it, against the kernel: it gives hypot(x, y) where the kernel's roundings
// toward -∞ and +∞ agree, as hypot(x, y) is then an `f64`, and `None` elsewhere. Where the
// directed rounding tests fail, `fast_hypot` gives that value. Checks the fast paths at (x, y)
// with `check_fast_hypot` too. Returns whether `hypot_exact` declined and whether the directed
// tests failed, or `None` where `fast_hypot` takes the pair by its rule for a gap of 27 or more
// or `hypot_dd` declines it.
fn check_hypot_exact(x: f64, y: f64) -> Option<(bool, bool)> {
    check_fast_hypot(x, y);
    let (big, small, far) = far_pair(x, y);
    if far || small == 0.0 {
        return None;
    }
    let (h, _, e) = hypot_dd::<HAS_FMA>(big, small)?;
    set_fast_path(false);
    let (lo, hi) = (hypot(x, y, false), hypot(x, y, true));
    set_fast_path(true);
    let want = (lo == hi).then_some(lo);
    let what = format!("hypot({:e}, {:e})", x, y);
    assert_eq!(
        hypot_exact(big, small, h, e),
        want,
        "hypot_exact({:e}, {:e}, {:e}, {}) for {}",
        big,
        small,
        h,
        e,
        what
    );
    reset_fast_counts();
    let dir = [
        fast_hypot::<HAS_FMA>(x, y, false),
        fast_hypot::<HAS_FMA>(x, y, true),
    ];
    let (_, failed) = fast_counts();
    if failed > 0 {
        assert_eq!(dir, [want; 2], "{}", what);
    }
    Some((want.is_none(), failed > 0))
}

// The pairs next to the exact results of `fast_hypot_takes_triples`, with one leg moved to the
// `f64` on either side of it, for 500 of its exact triples from a seed of their own, and for
// four whose short leg is 24 or 25 binades below the long one, each under 16 powers of two
// (`dd_scaled`). `hypot_exact` declines each of them (`check_hypot_exact`), and the kernel gives
// the results. Moving the short leg b of those four by an ulp moves the result c by about
// b ulp(b) / c, about 2^-100 c or less, so that where b stays normal the directed rounding tests
// fail, as l is then within `ERR_HYPOT` = 2^-98 of 0, and `hypot_exact`, called with an h that
// scales to c, declines, as c^2 is the sum of the squares of the old legs.
#[test]
fn fast_hypot_declines_next_to_triples() {
    let mut rng = Rng(10604);
    let mut triples = vec![];
    while triples.len() < 500 {
        if let Some((x, y, c, _)) = dd_triple(&mut rng) {
            if is_f64(c) {
                triples.push((x, y));
            }
        }
    }
    // (m, n) = (2^25 + 1, 1), (2^26 - 1, 1), (2^26 + 1, 1) and (2^26 + 1, 2): legs m^2 - n^2 and
    // 2 m n, both `f64`s, and c = m^2 + n^2 below 2^53.
    for (m, n) in [
        (33_554_433, 1),
        (67_108_863, 1),
        (67_108_865, 1),
        (67_108_865, 2),
    ] {
        let (a, b, c): (u64, u64, u64) = (m * m - n * n, 2 * m * n, m * m + n * n);
        assert!(is_f64(a) && is_f64(b) && c < 1 << 53, "{} {}", m, n);
        for _ in 0..16 {
            let (x, y, _) = dd_scaled(&mut rng, a, b);
            triples.push((x, y));
        }
    }
    let (mut declined, mut failed, mut checked) = (0, 0, 0);
    for (x, y) in triples {
        let pairs = [
            (f64::next_down(x), y),
            (f64::next_up(x), y),
            (x, f64::next_down(y)),
            (x, f64::next_up(y)),
        ];
        for (x, y) in pairs {
            if let Some((d, f)) = check_hypot_exact(x, y) {
                checked += 1;
                declined += usize::from(d);
                failed += usize::from(f);
            }
        }
    }
    assert!(
        declined == checked && failed > 100 && checked > 2_000,
        "{} declined, {} failed, {} checked",
        declined,
        failed,
        checked
    );
}

// `cbrt_exact` and `hypot_exact` on their own: they give c = h 2^e where c^3 = |x| and
// c^2 = big^2 + small^2, for any normal h and e in [-1021, 1022] with that c (`hypot_exact` for
// any (h, e) that `scale` takes to c), and `None` where c is another number. `fast_cbrt` gives
// h in [1, 2) and e with c = h 2^e, here 27 = (1.5 2^1)^3, and `hypot_dd` e as the exponent
// field of big minus 1022, here 5 = 0.625 2^3 at big = 4.
#[test]
fn exact_arms() {
    let hl = |v: Option<(f64, f64, i64)>| v.map(|(h, _, e)| (h, e));
    let tiny = 27.0 * pow2(-1074);
    assert_eq!(hl(fast_cbrt::<HAS_FMA>(27.0)), Some((1.5, 1)));
    assert_eq!(hl(fast_cbrt::<HAS_FMA>(-27.0)), Some((1.5, 1)));
    assert_eq!(hl(fast_cbrt::<HAS_FMA>(tiny)), Some((1.5, -357)));
    let (h8, e8) = hl(fast_cbrt::<HAS_FMA>(f64::next_down(8.0))).unwrap();
    assert_eq!(h8, 2.0);
    for (x, h, e, want) in [
        (27.0, 1.5, 1, Some(3.0)),
        (-27.0, 1.5, 1, Some(3.0)),
        (8.0, 1.0, 1, Some(2.0)),
        (1.0, 1.0, 0, Some(1.0)),
        (0.125, 1.0, -1, Some(0.5)),
        (tiny, 1.5, -357, Some(3.0 * pow2(-358))),
        (-tiny, 0.75, -356, Some(3.0 * pow2(-358))),
        // c = 1.5, whose cube is 27 / 8.
        (27.0, 1.5, 0, None),
        // The 35 low bits of the significand of h are not all zeros.
        (27.0, f64::next_up(1.5), 1, None),
        (27.0, f64::next_down(1.5), 1, None),
        // 28 = 7 2^2, whose odd part is not 3^3.
        (28.0, 1.5, 1, None),
        // 54 = 27 2, whose odd part is 3^3, but not its exponent 3 (-1 + 1).
        (54.0, 1.5, 1, None),
        // h = 2 at the `f64` below 8 (`fast_cbrt_near_two`), whose odd part is 2^53 - 1.
        (f64::next_down(8.0), h8, e8, None),
    ] {
        assert_eq!(
            cbrt_exact(x, h, e).map(f64::to_bits),
            want.map(f64::to_bits),
            "cbrt_exact({:e}, {:e}, {})",
            x,
            h,
            e
        );
    }
    assert_eq!(hl(hypot_dd::<HAS_FMA>(4.0, 3.0)), Some((0.625, 3)));
    let (h1, e1) = hl(hypot_dd::<HAS_FMA>(1.0, 1.0)).unwrap();
    let (big, small) = (9_007_199_388_958_720.0, 134_217_729.0);
    let (hm, em) = hl(hypot_dd::<HAS_FMA>(big, small)).unwrap();
    for (big, small, h, e, want) in [
        (4.0, 3.0, 0.625, 3, Some(5.0)),
        (4.0, 3.0, 1.25, 2, Some(5.0)),
        (12.0, 5.0, 0.8125, 4, Some(13.0)),
        // 2^-1022 and 3 2^-1024, which is subnormal.
        (
            pow2(-1022),
            3.0 * pow2(-1024),
            0.625,
            -1021,
            Some(5.0 * pow2(-1024)),
        ),
        // c next to 5.
        (4.0, 3.0, f64::next_up(0.625), 3, None),
        (4.0, 3.0, f64::next_down(0.625), 3, None),
        // c = 2, below big.
        (4.0, 3.0, 0.25, 3, None),
        // c = 4 and 6, whose lowest bits are above that of 3.
        (4.0, 3.0, 0.5, 3, None),
        (4.0, 3.0, 0.75, 3, None),
        // c = +∞, whose exponent 1024 is above that of big.
        (f64::MAX, f64::MAX, 1.0, 1024, None),
        // √2 rounded, and the midpoint of `smoke` rounded to an `f64` by `hypot_dd`.
        (1.0, 1.0, h1, e1, None),
        (big, small, hm, em, None),
    ] {
        assert_eq!(
            hypot_exact(big, small, h, e),
            want,
            "hypot_exact({:e}, {:e}, {:e}, {})",
            big,
            small,
            h,
            e
        );
    }
}

// `hypot_dd` takes big from 2^-1022 to below 2^1022, and declines big of 2^1022 or more and
// subnormal big, whatever small is.
#[test]
fn hypot_dd_range() {
    for (big, taken) in [
        (f64::MAX, false),
        (pow2(1023), false),
        (f64::next_up(pow2(1022)), false),
        (pow2(1022), false),
        (f64::next_down(pow2(1022)), true),
        (1.0, true),
        (f64::next_up(f64::MIN_POSITIVE), true),
        (f64::MIN_POSITIVE, true),
        (f64::next_down(f64::MIN_POSITIVE), false),
        (pow2(-1050), false),
        (pow2(-1074), false),
    ] {
        for small in [big, f64::next_down(big), big * 0.5, big * pow2(-26)] {
            if small > 0.0 {
                assert_eq!(
                    hypot_dd::<HAS_FMA>(big, small).is_some(),
                    taken,
                    "hypot_dd({:e}, {:e})",
                    big,
                    small
                );
            }
        }
    }
}

// The rule of `fast_hypot` for a gap of 27 or more, on exponent fields, holds only where the gap
// g of `hypot_odd` is 27 or more, so that the result is big rounded down or to nearest and the
// `f64` after it rounded up. g is the difference of the fields where both are normal, and at
// least that where small is subnormal, whose binade is then below that of field 1. Checked on the
// pairs big >= small of the ends 2^n and next_down(2^n) of every binade and MAX, where small is
// subnormal or at most 40 binades below big. The rule has taken a pair where `fast_hypot` gives a
// result without a rounding test; there `hypot_odd` gives the same `f64`s.
#[test]
fn fast_hypot_gap_rule() {
    let mut ends = vec![f64::MAX];
    for n in -1073..=1023 {
        ends.push(pow2(n));
        ends.push(f64::next_down(pow2(n)));
    }
    let ends: Vec<(f64, i64)> = ends.into_iter().map(|v| (v, binade(v))).collect();
    let (mut far, mut subnormal_far) = (0, 0);
    for &(big, eb) in &ends {
        for &(small, es) in &ends {
            let g = eb - es;
            let sub = small < f64::MIN_POSITIVE;
            if small > big || !(sub || g <= 40) {
                continue;
            }
            reset_fast_counts();
            let fast = [
                fast_hypot::<HAS_FMA>(big, small, false),
                fast_hypot::<HAS_FMA>(big, small, true),
                fast_hypot_near::<HAS_FMA>(big, small),
            ];
            let tests = fast_counts();
            let what = format!("hypot({:e}, {:e}), g = {}", big, small, g);
            let rule = field(big) - field(small) >= 27;
            assert_eq!(far_pair(big, small).2, rule, "{}", what);
            if !sub {
                assert_eq!(rule, g >= 27, "{}", what);
            }
            if rule {
                far += 1;
                subnormal_far += usize::from(sub);
                assert!(g >= 27 && tests == (0, 0), "{}: {:?}", what, tests);
                let odd = hypot_odd(big, small);
                let want = [Some(odd.to_f64(false)), Some(odd.to_f64(true)), Some(big)];
                assert_eq!(fast, want, "{}", what);
                assert_eq!(fast[1], Some(f64::next_up(big)), "{}", what);
                assert_eq!(odd.to_f64_near(), big, "{}", what);
            } else if hypot_dd::<HAS_FMA>(big, small).is_some() {
                assert_eq!(tests.0 + tests.1, 3, "{}", what);
            } else {
                assert!(
                    tests == (0, 0) && fast == [None; 3],
                    "{}: {:?}",
                    what,
                    tests
                );
            }
        }
    }
    assert!(
        far > 50_000 && subnormal_far > 10_000,
        "{} {}",
        far,
        subnormal_far
    );
}
