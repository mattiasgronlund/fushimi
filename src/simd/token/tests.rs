// Tests of the tokens: every `*_with` operation of `Interval` at each level that the CPU has,
// called directly and inside the level's `vectorize`, and through `dispatch`, against the
// operation that takes no token. These operations return the tightest results
// (`src/_docs/conformance.md`), so every level must return the same interval, and `==` on
// `Interval` is the spec. The backend functions that each level's copies compile are compared
// with the portable backend's in `src/simd/differential_tests.rs`.

use super::*;
use crate::{classify::IntervalClass, Interval};
use std::any::type_name;

// 2^e, for an e in the range of the exponents of normal numbers.
fn pow2(e: i32) -> f64 {
    f64::from_bits(((1023 + e) as u64) << 52)
}

// The bounds of the intervals, with their negatives: the zeros, the smallest subnormal and
// normal numbers, 2^-968 (the backends' `mul_ru` round products below it apart from their fast
// path), 1/3, 1, 1.5 and 3 (whose products and quotients are exact or not), 2^512 (whose
// square overflows), `f64::MAX` and infinity.
fn bounds() -> Vec<f64> {
    let positive = [
        0.0,
        f64::from_bits(1),
        f64::MIN_POSITIVE,
        pow2(-968),
        1.0 / 3.0,
        1.0,
        1.5,
        3.0,
        pow2(512),
        f64::MAX,
        f64::INFINITY,
    ];
    positive.iter().flat_map(|&a| [a, -a]).collect()
}

// `EMPTY` and every interval of two bounds. Both zeros are bounds, so the zero bounds of the
// representation take both signs.
fn intervals() -> Vec<Interval> {
    let bounds = bounds();
    let mut xs = vec![Interval::EMPTY];
    for &a in &bounds {
        for &b in &bounds {
            if let Ok(x) = Interval::try_from((a, b)) {
                xs.push(x);
            }
        }
    }
    xs
}

// The addends of `mul_add`: `EMPTY` (which `mul_add` returns before it classifies its other
// arguments), unbounded, zero, exact, tiny, inexact and huge bounds.
fn addends() -> Vec<Interval> {
    let tiny = f64::from_bits(1);
    [
        (f64::NEG_INFINITY, f64::INFINITY),
        (0.0, 0.0),
        (1.0, 1.0),
        (-tiny, tiny),
        (-1.0 / 3.0, 3.0),
        (-f64::MAX, f64::MAX),
    ]
    .iter()
    .map(|&x| Interval::try_from(x).unwrap())
    .chain([Interval::EMPTY])
    .collect()
}

#[derive(Clone, Copy, Debug)]
enum Case {
    Add(Interval, Interval),
    Sub(Interval, Interval),
    Mul(Interval, Interval),
    Div(Interval, Interval),
    MulAdd(Interval, Interval, Interval),
    Recip(Interval),
    Sqr(Interval),
    Sqrt(Interval),
}

impl Case {
    // The result of the operation that takes no token.
    fn expected(&self) -> Interval {
        match *self {
            Case::Add(x, y) => x + y,
            Case::Sub(x, y) => x - y,
            Case::Mul(x, y) => x * y,
            Case::Div(x, y) => x / y,
            Case::MulAdd(x, y, z) => x.mul_add(y, z),
            Case::Recip(x) => x.recip(),
            Case::Sqr(x) => x.sqr(),
            Case::Sqrt(x) => x.sqrt(),
        }
    }

    // The result of the operation at the level `s`. `#[inline(always)]`, so that inside a region
    // the operation takes the region's target features.
    #[inline(always)]
    fn with<S: Simd>(&self, s: S) -> Interval {
        match *self {
            Case::Add(x, y) => x.add_with(s, y),
            Case::Sub(x, y) => x.sub_with(s, y),
            Case::Mul(x, y) => x.mul_with(s, y),
            Case::Div(x, y) => x.div_with(s, y),
            Case::MulAdd(x, y, z) => x.mul_add_with(s, y, z),
            Case::Recip(x) => x.recip_with(s),
            Case::Sqr(x) => x.sqr_with(s),
            Case::Sqrt(x) => x.sqrt_with(s),
        }
    }
}

// The cases whose first argument is `x`, with every interval as the second argument and every
// addend as the third. All the cases at once would be about 700,000.
fn cases(x: Interval, xs: &[Interval], addends: &[Interval]) -> Vec<Case> {
    let mut cases = vec![Case::Recip(x), Case::Sqr(x), Case::Sqrt(x)];
    for &y in xs {
        cases.extend([
            Case::Add(x, y),
            Case::Sub(x, y),
            Case::Mul(x, y),
            Case::Div(x, y),
        ]);
        cases.extend(addends.iter().map(|&z| Case::MulAdd(x, y, z)));
    }
    cases
}

// Calls `f` with the cases of each first argument and their expected results, which are
// computed here, outside any region.
fn for_each_x(mut f: impl FnMut(&[Case], &[Interval])) {
    let xs = intervals();
    let addends = addends();
    for &x in &xs {
        let cases = cases(x, &xs, &addends);
        let expected = cases.iter().map(Case::expected).collect::<Vec<_>>();
        f(&cases, &expected);
    }
}

// The results of the cases at the level `s`. A loop of its own rather than `collect`, whose
// generic internals LLVM can leave out of a region that inlines `run`.
#[inline(always)]
fn run<S: Simd>(s: S, cases: &[Case]) -> Vec<Interval> {
    let mut results = Vec::with_capacity(cases.len());
    for c in cases {
        results.push(c.with(s));
    }
    results
}

// Panics with the cases whose result `got` differs from the expected one.
fn check(how: &str, cases: &[Case], expected: &[Interval], got: &[Interval]) {
    let mismatches = cases
        .iter()
        .zip(expected)
        .zip(got)
        .filter(|((_, e), g)| e != g)
        .map(|((c, e), g)| format!("{c:?}: {g:?}, expected {e:?}"))
        .collect::<Vec<_>>();
    assert!(
        mismatches.is_empty(),
        "{how}: {} mismatches, the first:\n{}",
        mismatches.len(),
        mismatches[..mismatches.len().min(20)].join("\n")
    );
}

// Checks every case at the level `s`, called directly and inside `s.vectorize`.
fn check_token<S: Simd>(s: S) {
    let name = type_name::<S>();
    for_each_x(|cases, expected| {
        check(&format!("{name}, direct"), cases, expected, &run(s, cases));
        // Without `#[inline(always)]`, LLVM can leave the closure out of the region, where it
        // runs without the region's target features, as it did with the loop of `det3/mixed`
        // in `bench/benches/intervals.rs`.
        let got = s.vectorize(
            #[inline(always)]
            || run(s, cases),
        );
        check(&format!("{name}, vectorize"), cases, expected, &got);
    });
}

#[test]
fn intervals_have_every_class() {
    use IntervalClass::*;
    let classes = intervals().iter().map(|x| x.classify()).collect::<Vec<_>>();
    for class in [E, M, N0, N1, P0, P1, Z] {
        assert!(
            classes.contains(&class),
            "no interval of the class {class:?}"
        );
    }
}

#[test]
fn baseline() {
    check_token(Baseline);
}

#[cfg(target_arch = "x86_64")]
#[test]
fn v2() {
    match V2::try_new() {
        Some(s) => check_token(s),
        None => eprintln!("skipped: the CPU does not have the target features of `V2`"),
    }
}

#[cfg(target_arch = "x86_64")]
#[test]
fn v3() {
    match V3::try_new() {
        Some(s) => check_token(s),
        None => eprintln!("skipped: the CPU does not have the target features of `V3`"),
    }
}

// The cases, run by `dispatch` at its level.
struct Run<'a>(&'a [Case]);

impl WithLevel for Run<'_> {
    type Output = Vec<Interval>;

    #[inline(always)]
    fn with_level<S: Simd>(self, s: S) -> Vec<Interval> {
        run(s, self.0)
    }
}

// The name of the token that `dispatch` passes.
struct Level;

impl WithLevel for Level {
    type Output = &'static str;

    fn with_level<S: Simd>(self, _: S) -> &'static str {
        type_name::<S>()
    }
}

#[test]
fn dispatch_picks_the_highest_level() {
    #[allow(unused_mut)] // Only x86-64 has levels above `Baseline`.
    let mut expected = type_name::<Baseline>();
    #[cfg(target_arch = "x86_64")]
    if V3::try_new().is_some() {
        expected = type_name::<V3>();
    } else if V2::try_new().is_some() {
        expected = type_name::<V2>();
    }
    assert_eq!(dispatch(Level), expected);
}

#[test]
fn dispatch_runs_every_case() {
    for_each_x(|cases, expected| {
        check("dispatch", cases, expected, &dispatch(Run(cases)));
    });
}
