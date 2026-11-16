// Tests of the tokens: every `*_with` operation of `Interval` and of `DecInterval` at each
// level that the CPU has, called directly and inside the level's `vectorize`, and through
// `dispatch`, against the operation that takes no token. These operations return the tightest
// results (`src/_docs/conformance.md`), so every level must return the same interval, and with
// it the same decoration, which the operations of `DecInterval` compute from their arguments
// and that interval. `==` on `Interval` is the spec. `==` on `DecInterval` is not: it ignores
// the decorations and is false if either side is NaI, so the results of `DecInterval` are
// compared by `interval()` and `decoration()`. The backend functions that each level's copies
// compile are compared with the portable backend's in `src/simd/differential_tests.rs`.

use super::*;
use crate::{classify::IntervalClass, DecInterval, Decoration, Interval};
use std::{any::type_name, collections::HashSet, fmt::Debug};

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

// The decorations that `set_dec` keeps for a nonempty bounded interval, apart from `ill`.
const DECORATIONS: [Decoration; 4] = [
    Decoration::Com,
    Decoration::Dac,
    Decoration::Def,
    Decoration::Trv,
];

// Each interval of `intervals()` with each decoration that `set_dec` keeps for it, and NaI.
// `set_dec` makes an unbounded interval `dac` in place of `com`, and `EMPTY` `trv` whatever the
// decoration, so the duplicates of each interval are next to each other.
fn dec_intervals() -> Vec<DecInterval> {
    let mut xs = Vec::new();
    for x in intervals() {
        let mut ys = DECORATIONS.map(|d| DecInterval::set_dec(x, d)).to_vec();
        ys.dedup_by_key(|y| (y.interval(), y.decoration()));
        xs.extend(ys);
    }
    xs.push(DecInterval::NAI);
    xs
}

// `x` with the decoration `DECORATIONS[n % 4]` through `set_dec`, or NaI if `x` is `None`.
fn decorate(x: Option<Interval>, n: usize) -> DecInterval {
    x.map_or(DecInterval::NAI, |x| {
        DecInterval::set_dec(x, DECORATIONS[n % DECORATIONS.len()])
    })
}

// A case of an operation of `Interval` or of `DecInterval`: the operation and its arguments.
trait TestCase: Copy + Debug {
    // The result of the operation.
    type Output: Debug;

    // Calls `f` with the cases of each first argument in turn.
    fn for_each_first(f: impl FnMut(&[Self]));

    // The result of the operation that takes no token.
    fn expected(&self) -> Self::Output;

    // The result of the operation at the level `s`. Each impl is `#[inline(always)]`, so that
    // inside a region the operation takes the region's target features.
    fn with<S: Simd>(&self, s: S) -> Self::Output;

    // Whether `x` and `y` are the same result.
    fn same(x: &Self::Output, y: &Self::Output) -> bool;
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

impl TestCase for Case {
    type Output = Interval;

    fn for_each_first(mut f: impl FnMut(&[Case])) {
        let xs = intervals();
        let addends = addends();
        for &x in &xs {
            f(&cases(x, &xs, &addends));
        }
    }

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

    fn same(x: &Interval, y: &Interval) -> bool {
        x == y
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

#[derive(Clone, Copy, Debug)]
enum DecCase {
    Add(DecInterval, DecInterval),
    Sub(DecInterval, DecInterval),
    Mul(DecInterval, DecInterval),
    Div(DecInterval, DecInterval),
    MulAdd(DecInterval, DecInterval, DecInterval),
    Recip(DecInterval),
    Sqr(DecInterval),
    Sqrt(DecInterval),
}

impl TestCase for DecCase {
    type Output = DecInterval;

    fn for_each_first(mut f: impl FnMut(&[DecCase])) {
        let xs = dec_intervals();
        let ys = intervals();
        let addends = addends();
        for (i, &x) in xs.iter().enumerate() {
            f(&dec_cases(i, x, &xs, &ys, &addends));
        }
    }

    fn expected(&self) -> DecInterval {
        match *self {
            DecCase::Add(x, y) => x + y,
            DecCase::Sub(x, y) => x - y,
            DecCase::Mul(x, y) => x * y,
            DecCase::Div(x, y) => x / y,
            DecCase::MulAdd(x, y, z) => x.mul_add(y, z),
            DecCase::Recip(x) => x.recip(),
            DecCase::Sqr(x) => x.sqr(),
            DecCase::Sqrt(x) => x.sqrt(),
        }
    }

    #[inline(always)]
    fn with<S: Simd>(&self, s: S) -> DecInterval {
        match *self {
            DecCase::Add(x, y) => x.add_with(s, y),
            DecCase::Sub(x, y) => x.sub_with(s, y),
            DecCase::Mul(x, y) => x.mul_with(s, y),
            DecCase::Div(x, y) => x.div_with(s, y),
            DecCase::MulAdd(x, y, z) => x.mul_add_with(s, y, z),
            DecCase::Recip(x) => x.recip_with(s),
            DecCase::Sqr(x) => x.sqr_with(s),
            DecCase::Sqrt(x) => x.sqrt_with(s),
        }
    }

    // Not `x == y`, which ignores the decorations and is false if either side is NaI.
    fn same(x: &DecInterval, y: &DecInterval) -> bool {
        (x.interval(), x.decoration()) == (y.interval(), y.decoration())
    }
}

// The cases whose first argument is `x`, the `i`th of `xs`, with each of `xs` as the second
// argument of the binary operations. Every decoration of the second and third arguments of
// `mul_add` would make about 23,000,000 cases, so its second argument is each of `ys` and NaI,
// and its third each of `addends` and NaI, with decorations that cycle with `i` and their
// indices: as `i` runs through 16 values in a row, each pair of an interval of `ys` and an
// addend is passed to `set_dec` with each pair of `DECORATIONS`. All the cases at once would be
// about 5,700,000.
fn dec_cases(
    i: usize,
    x: DecInterval,
    xs: &[DecInterval],
    ys: &[Interval],
    addends: &[Interval],
) -> Vec<DecCase> {
    let mut cases = vec![DecCase::Recip(x), DecCase::Sqr(x), DecCase::Sqrt(x)];
    for &y in xs {
        cases.extend([
            DecCase::Add(x, y),
            DecCase::Sub(x, y),
            DecCase::Mul(x, y),
            DecCase::Div(x, y),
        ]);
    }
    for (j, y) in ys.iter().copied().map(Some).chain([None]).enumerate() {
        let y = decorate(y, i + j);
        for (k, z) in addends.iter().copied().map(Some).chain([None]).enumerate() {
            cases.push(DecCase::MulAdd(x, y, decorate(z, i / 4 + j + k)));
        }
    }
    cases
}

// Calls `f` with the cases of each first argument and their expected results, which are
// computed here, outside any region.
fn for_each_x<C: TestCase>(mut f: impl FnMut(&[C], &[C::Output])) {
    C::for_each_first(|cases| {
        let expected = cases.iter().map(C::expected).collect::<Vec<_>>();
        f(cases, &expected);
    });
}

// The results of the cases at the level `s`. A loop of its own rather than `collect`, whose
// generic internals LLVM can leave out of a region that inlines `run`.
#[inline(always)]
fn run<C: TestCase, S: Simd>(s: S, cases: &[C]) -> Vec<C::Output> {
    let mut results = Vec::with_capacity(cases.len());
    for c in cases {
        results.push(c.with(s));
    }
    results
}

// Panics with the cases whose result `got` differs from the expected one.
fn check<C: TestCase>(how: &str, cases: &[C], expected: &[C::Output], got: &[C::Output]) {
    let mismatches = cases
        .iter()
        .zip(expected)
        .zip(got)
        .filter(|((_, e), g)| !C::same(e, g))
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
fn check_token<C: TestCase, S: Simd>(s: S) {
    let name = type_name::<S>();
    for_each_x::<C>(|cases, expected| {
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

// Checks every case at `V2`, if the CPU has its target features.
#[cfg(target_arch = "x86_64")]
fn check_v2<C: TestCase>() {
    match V2::try_new() {
        Some(s) => check_token::<C, _>(s),
        None => eprintln!("skipped: the CPU does not have the target features of `V2`"),
    }
}

// Checks every case at `V3`, if the CPU has its target features.
#[cfg(target_arch = "x86_64")]
fn check_v3<C: TestCase>() {
    match V3::try_new() {
        Some(s) => check_token::<C, _>(s),
        None => eprintln!("skipped: the CPU does not have the target features of `V3`"),
    }
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
fn dec_cases_have_every_decoration_in_each_position() {
    // The operations, the positions of their arguments and the decorations found there.
    let mut found = HashSet::new();
    let mut record = |op: &'static str, args: &[DecInterval]| {
        for (position, x) in args.iter().enumerate() {
            found.insert((op, position, x.decoration()));
        }
    };
    DecCase::for_each_first(|cases| {
        for c in cases {
            match *c {
                DecCase::Add(x, y) => record("add", &[x, y]),
                DecCase::Sub(x, y) => record("sub", &[x, y]),
                DecCase::Mul(x, y) => record("mul", &[x, y]),
                DecCase::Div(x, y) => record("div", &[x, y]),
                DecCase::MulAdd(x, y, z) => record("mul_add", &[x, y, z]),
                DecCase::Recip(x) => record("recip", &[x]),
                DecCase::Sqr(x) => record("sqr", &[x]),
                DecCase::Sqrt(x) => record("sqrt", &[x]),
            }
        }
    });
    let arities = [
        ("add", 2),
        ("sub", 2),
        ("mul", 2),
        ("div", 2),
        ("mul_add", 3),
        ("recip", 1),
        ("sqr", 1),
        ("sqrt", 1),
    ];
    for (op, arity) in arities {
        for position in 0..arity {
            for d in DECORATIONS.iter().copied().chain([Decoration::Ill]) {
                assert!(
                    found.contains(&(op, position, d)),
                    "no argument {position} of `{op}` with the decoration {d:?}"
                );
            }
        }
    }
}

#[test]
fn baseline() {
    check_token::<Case, _>(Baseline);
}

#[test]
fn dec_baseline() {
    check_token::<DecCase, _>(Baseline);
}

#[cfg(target_arch = "x86_64")]
#[test]
fn v2() {
    check_v2::<Case>();
}

#[cfg(target_arch = "x86_64")]
#[test]
fn dec_v2() {
    check_v2::<DecCase>();
}

#[cfg(target_arch = "x86_64")]
#[test]
fn v3() {
    check_v3::<Case>();
}

#[cfg(target_arch = "x86_64")]
#[test]
fn dec_v3() {
    check_v3::<DecCase>();
}

// The cases, run by `dispatch` at its level.
struct Run<'a, C>(&'a [C]);

impl<C: TestCase> WithLevel for Run<'_, C> {
    type Output = Vec<C::Output>;

    #[inline(always)]
    fn with_level<S: Simd>(self, s: S) -> Vec<C::Output> {
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

// Checks every case through `dispatch`.
fn check_dispatch<C: TestCase>() {
    for_each_x::<C>(|cases, expected| {
        check("dispatch", cases, expected, &dispatch(Run(cases)));
    });
}

#[test]
fn dispatch_runs_every_case() {
    check_dispatch::<Case>();
}

#[test]
fn dec_dispatch_runs_every_case() {
    check_dispatch::<DecCase>();
}
