// Tests of `pown_small_dir` and `pown_small_near` of `pow.rs`, x^n for 1 <= |n| <= `SMALL_MAX`
// by binary powering in double-double, with an FMA and without one (Dekker's product), at the
// arguments that `pown_pos` and `pown_pos_near` pass them (`reaches`). Where they return an
// `f64`, it has to be MPFR's rounding of x^n toward -∞, toward +∞ or to nearest, which
// `pown_rd`, `pown_ru` and `pown_rn` of `src/mpfr_calls/mpfr.rs` compute, on 64-bit Linux and
// macOS, where the tests have MPFR. Every argument also goes through `agree_pown`. The x are
// random normal ones, x near 1, powers of 2 and the `f64`s next to them, and x next to
// 2^(k / n) for 2^k = 2^-1075, 2^-1074, 2^-1022 and 2^1024, whose x^n are next to the midpoint
// of 0 and the least subnormal, the least subnormal, the least normal and the overflow.

use super::*;

// Whether `pown_pos` and `pown_pos_near` pass (x, n) to `pown_small_dir` and `pown_small_near`,
// for a finite x > 0 in [2^g, 2^(g + 1)) and n != 0: past their rules, which settle x^n where
// its bound below, 2^(g n) for n > 0 and 2^((g + 1) n) for n < 0, is 2^1024 or above, and where
// its bound above is 2^-1075 or below.
fn reaches(x: f64, n: i32) -> bool {
    let (g, n) = (expo(x), i64::from(n));
    let (lo, hi) = if n > 0 {
        (g * n, (g + 1) * n)
    } else {
        ((g + 1) * n, g * n)
    };
    lo < 1024 && hi > -1075
}

// The sets of `cases`.
const SETS: [&str; 4] = ["random", "near 1", "2^e", "2^(k / n)"];

// The arguments of the tests, as the header says, each with the index of its set in `SETS`, for
// every n with 1 <= |n| <= `SMALL_MAX`, and normal x only, as `pown_small` gives `None` at a
// subnormal x (`small_copies_agree`). The random x and the powers of 2 have exponents g with
// |g n| up to 1076, so that x^n is in range or just past it.
fn cases() -> Vec<(usize, f64, i32)> {
    let mut rng = Rng(896);
    let mut cases = vec![];
    for a in 1..=i32::try_from(SMALL_MAX).unwrap() {
        let (lo, hi) = ((-1076 / i64::from(a)).max(-1022), 1076 / i64::from(a));
        for n in [a, -a] {
            let mut xs = vec![];
            for _ in 0..3000 {
                xs.push((0, log_uniform(&mut rng, lo, hi.min(1023))));
            }
            for _ in 0..1000 {
                xs.push((1, near_one(&mut rng)));
                let e = lo + rng.below(u64::try_from(hi.min(1023) - lo + 1).unwrap()) as i64;
                xs.extend(around(pow2(e), 1).into_iter().map(|x| (2, x)));
            }
            // x next to 2^(k / n), and x = 2^(k / n) (1 ± 2^-j) for j up to 52, whose x^n is
            // about 2^k (1 ± n 2^-j).
            for k in [-1075.0, -1074.0, -1022.0, 1024.0] {
                let x = (k / f64::from(n)).exp2();
                xs.extend(around(x, 32).into_iter().map(|x| (3, x)));
                for _ in 0..200 {
                    let j = 1 + rng.below(52) as i64;
                    xs.push((3, x * (1.0 + sign(&mut rng) * pow2(-j))));
                }
            }
            let normal = |&(_, x): &(usize, f64)| (f64::MIN_POSITIVE..f64::INFINITY).contains(&x);
            cases.extend(xs.into_iter().filter(normal).map(|(s, x)| (s, x, n)));
        }
    }
    cases
}

// `agree_pown` holds at every argument of `cases`, and some of the rounding tests that it counts
// pass in every set. The test prints how many passed and failed in each.
#[test]
fn small_powers_agree() {
    let mut counts = [(0, 0); SETS.len()];
    for (s, x, n) in cases() {
        let (p, f) = agree_pown(x, n);
        counts[s].0 += p;
        counts[s].1 += f;
    }
    for (set, (passed, failed)) in SETS.iter().zip(counts) {
        eprintln!("small powers, {set}: {passed} rounding tests passed, {failed} failed");
        assert!(passed > 0, "small powers, {set}: no rounding test passed");
    }
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
mod mpfr {
    use super::*;
    use crate::mpfr_calls::mpfr::{pown_rd, pown_rn, pown_ru};

    // Checks that the `f64`s that `pown_small_dir` toward -∞ and toward +∞ and `pown_small_near`
    // gave at (x, n), with an FMA if `FMA` and without one otherwise, where they gave one, are
    // MPFR's roundings of x^n, and returns which of the three they gave.
    fn check<const FMA: bool>(x: f64, n: i32) -> [bool; 3] {
        let g = expo(x);
        let got = [
            pown_small_dir::<FMA>(x, n, g, false),
            pown_small_dir::<FMA>(x, n, g, true),
            pown_small_near::<FMA>(x, n, g),
        ];
        let want = [pown_rd(x, n), pown_ru(x, n), pown_rn(x, n)];
        for ((v, w), rnd) in got
            .iter()
            .zip(want)
            .zip(["toward -∞", "toward +∞", "to nearest"])
        {
            if let Some(v) = v {
                assert!(
                    v.to_bits() == w.to_bits(),
                    "pown_small::<{FMA}>({x:e}, {n}) {rnd}: {v:e} != MPFR's {w:e}"
                );
            }
        }
        got.map(|v| v.is_some())
    }

    // The roundings of `pown_small_dir` and `pown_small_near`, with an FMA and without one, are
    // MPFR's wherever they give one, at the arguments of `cases` that `reaches`, and they give
    // some in every set and direction. Their tests fail where x^n is within about 2^-67 of
    // where the rounding changes. In the directed roundings, that is at x^1 = x, at the exact
    // x^n of x = 2^e, and at x = 2^e (1 + d) for d = 2^-52, and for d = -2^-53 but at an odd
    // n < 0, as (1 + d)^n is within C(9, 2) d^2 < 2^-98 of 1 + n d, an `f64` there. To nearest,
    // it is at d = -2^-53 and an odd n < 0, where 1 + n d is a midpoint. Of the random x, all
    // but about one in sixteen are given in the directed roundings, those at n = 1, and all but
    // a few to nearest. The test prints how many it checked and how many were given.
    #[test]
    fn small_powers_agree_with_mpfr() {
        let mut given = [[0; 4]; SETS.len()];
        for (s, x, n) in cases().into_iter().filter(|&(_, x, n)| reaches(x, n)) {
            for got in [check::<true>(x, n), check::<false>(x, n)] {
                given[s][0] += 1;
                for (count, &v) in given[s][1..].iter_mut().zip(&got) {
                    *count += usize::from(v);
                }
            }
        }
        for (set, [tried, down, up, near]) in SETS.iter().zip(given) {
            eprintln!(
                "small powers, {set}: of {tried}, given {down} toward -∞, {up} toward +∞ and \
                 {near} to nearest"
            );
            assert!(down > 0 && up > 0 && near > 0, "small powers, {set}");
        }
        let [tried, down, up, near] = given[0];
        assert!(
            10 * down.min(up) >= 9 * tried && 100 * near >= 99 * tried,
            "small powers, random: of {tried}, given {down}, {up} and {near}"
        );
    }
}
