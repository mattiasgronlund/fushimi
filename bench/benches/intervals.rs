// Throughput of interval operations with the selected backend, on N intervals of
// each sign class: P (positive), N (negative) and M (containing zero).
//
// The series under `token/` and `token-v3/` run the loops of `add`, `mul`, `mul_tiny`,
// `div` and `unary` with the operations of the token API (`fushimi::simd`). Each batch
// of N enters the region of a level, a function compiled with the target features of
// that level, once: `token/` through `dispatch`, at the highest level that the CPU
// has, and `token-v3/` (x86-64 only) through `vectorize` of a `V3`.

use criterion::measurement::WallTime;
use criterion::{
    criterion_group, criterion_main, BenchmarkGroup, BenchmarkId, Criterion, Throughput,
};
#[cfg(target_arch = "x86_64")]
use fushimi::simd::V3;
use fushimi::simd::{dispatch, Simd, WithLevel};
use fushimi::Interval;
use std::hint::black_box;

const N: usize = 1024;

// 2^-1010 (biased exponent 1023 - 1010 = 13). The product of an interval scaled by
// it and one in [1, 3) lies below 2^-968, where the FMA backend's multiplication
// leaves its fast path, but is still normal.
const TINY: f64 = f64::from_bits(13 << 52);

// The classes of the operands of the binary series.
const ADD_CLASSES: [&str; 3] = ["PP", "PM", "MM"];
const ALL_CLASSES: [&str; 9] = ["PP", "PN", "PM", "NP", "NN", "NM", "MP", "MN", "MM"];
// x / y for y ∌ 0; division by an interval containing zero is also included.
const DIV_CLASSES: [&str; 5] = ["PP", "PN", "MP", "NN", "PM"];
// The classes of x, y and z of `x.mul_add(y, z)`.
const MUL_ADD_CLASSES: [&str; 3] = ["PPP", "PNM", "MMM"];

// Deterministic values in [1, 2).
fn values(seed: u64, n: usize) -> Vec<f64> {
    let mut s = seed;
    (0..n)
        .map(|_| {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            1.0 + (s >> 11) as f64 / (1u64 << 53) as f64
        })
        .collect()
}

// Intervals with endpoints in [1, 3) times `scale`, a power of two, so that the
// scaling is exact.
fn intervals(class: char, seed: u64, scale: f64) -> Vec<Interval> {
    values(seed, 2 * N)
        .chunks(2)
        .map(|c| {
            let (a, b) = (c[0].min(c[1]), c[0].max(c[1]) + 1.0);
            let (a, b) = (a * scale, b * scale);
            let (a, b) = match class {
                'P' => (a, b),
                'N' => (-b, -a),
                'M' => (-a, b),
                _ => unreachable!(),
            };
            Interval::try_from((a, b)).unwrap()
        })
        .collect()
}

// The operands of the class `cl` of a binary series. The first operand of each pair
// is scaled by `x_scale`, the second is not.
fn binary_operands(cl: &str, x_scale: f64) -> (Vec<Interval>, Vec<Interval>) {
    let mut it = cl.chars();
    let x = intervals(it.next().unwrap(), 1, x_scale);
    let y = intervals(it.next().unwrap(), 2, 1.0);
    (x, y)
}

// The operands of the class `cl` of a ternary series: those of `binary_operands`, and a
// third operand with seed 3, which is not scaled.
fn ternary_operands(cl: &str, x_scale: f64) -> (Vec<Interval>, Vec<Interval>, Vec<Interval>) {
    let mut it = cl.chars();
    let x = intervals(it.next().unwrap(), 1, x_scale);
    let y = intervals(it.next().unwrap(), 2, 1.0);
    let z = intervals(it.next().unwrap(), 3, 1.0);
    (x, y, z)
}

// The operands of the unary series: those in P and those in M.
fn unary_operands() -> (Vec<Interval>, Vec<Interval>) {
    (intervals('P', 3, 1.0), intervals('M', 4, 1.0))
}

// Matrices with a third of the entries in M and the rest in P.
fn matrices(p: &[Interval], m: &[Interval]) -> Vec<[Interval; 9]> {
    (0..N)
        .map(|i| {
            let mut e = [Interval::EMPTY; 9];
            for (j, e) in e.iter_mut().enumerate() {
                let src = if (i + j) % 3 == 0 { m } else { p };
                *e = src[(i * 9 + j) % N];
            }
            e
        })
        .collect()
}

fn bench_binary(
    c: &mut Criterion,
    name: &str,
    f: fn(Interval, Interval) -> Interval,
    classes: &[&str],
    x_scale: f64,
) {
    let mut g = c.benchmark_group(name);
    g.throughput(Throughput::Elements(N as u64));
    for cl in classes {
        let (x, y) = binary_operands(cl, x_scale);
        g.bench_function(BenchmarkId::from_parameter(cl), |b| {
            let mut out = vec![Interval::EMPTY; N];
            b.iter(|| {
                for i in 0..N {
                    out[i] = f(black_box(x[i]), black_box(y[i]));
                }
                black_box(&out);
            })
        });
    }
    g.finish();
}

fn bench_ternary(
    c: &mut Criterion,
    name: &str,
    f: fn(Interval, Interval, Interval) -> Interval,
    classes: &[&str],
    x_scale: f64,
) {
    let mut g = c.benchmark_group(name);
    g.throughput(Throughput::Elements(N as u64));
    for cl in classes {
        let (x, y, z) = ternary_operands(cl, x_scale);
        g.bench_function(BenchmarkId::from_parameter(cl), |b| {
            let mut out = vec![Interval::EMPTY; N];
            b.iter(|| {
                for i in 0..N {
                    out[i] = f(black_box(x[i]), black_box(y[i]), black_box(z[i]));
                }
                black_box(&out);
            })
        });
    }
    g.finish();
}

// An arbitrary polynomial of degree 8 with point coefficients.
const HORNER: [f64; 9] = [1.0, -0.5, 0.25, -0.125, 0.0625, 0.75, -1.5, 3.0, -2.0];

fn horner(x: Interval) -> Interval {
    let mut acc = Interval::try_from((HORNER[8], HORNER[8])).unwrap();
    for &c in HORNER[..8].iter().rev() {
        acc = acc * x + Interval::try_from((c, c)).unwrap();
    }
    acc
}

// `horner` with `mul_add` in place of `acc * x + c`.
fn horner_mul_add(x: Interval) -> Interval {
    let mut acc = Interval::try_from((HORNER[8], HORNER[8])).unwrap();
    for &c in HORNER[..8].iter().rev() {
        acc = acc.mul_add(x, Interval::try_from((c, c)).unwrap());
    }
    acc
}

fn det3(m: &[Interval; 9]) -> Interval {
    m[0] * (m[4] * m[8] - m[5] * m[7]) - m[1] * (m[3] * m[8] - m[5] * m[6])
        + m[2] * (m[3] * m[7] - m[4] * m[6])
}

fn intervals_bench(c: &mut Criterion) {
    bench_binary(c, "add", |x, y| x + y, &ADD_CLASSES, 1.0);
    bench_binary(c, "sub", |x, y| x - y, &ADD_CLASSES, 1.0);
    bench_binary(c, "mul", |x, y| x * y, &ALL_CLASSES, 1.0);
    // Products between 2^-1010 and 2^-1006 (see `TINY`). Most of the products in
    // operations recorded from rcad, a CAD kernel, were below 2^-968 too.
    bench_binary(c, "mul_tiny", |x, y| x * y, &ALL_CLASSES, TINY);
    bench_binary(c, "div", |x, y| x / y, &DIV_CLASSES, 1.0);
    bench_ternary(c, "mul_add", Interval::mul_add, &MUL_ADD_CLASSES, 1.0);
    // The products of the endpoints of x and y are those of `mul_tiny`, below 2^-968,
    // where `mul_add_ru` leaves its fast path in the backends that compute it with
    // error-free transformations.
    bench_ternary(c, "mul_add_tiny", Interval::mul_add, &MUL_ADD_CLASSES, TINY);

    let mut g = c.benchmark_group("unary");
    g.throughput(Throughput::Elements(N as u64));
    let (p, m) = unary_operands();
    type Unary = fn(Interval) -> Interval;
    // sqrt/M is the case that does not use the vector square root: an interval
    // containing zero needs the square root of one endpoint only.
    let unary: [(&str, Unary, &[Interval]); 6] = [
        ("sqrt/P", Interval::sqrt, &p),
        ("sqrt/M", Interval::sqrt, &m),
        ("horner8/P", horner, &p),
        ("horner8/M", horner, &m),
        ("horner8_mul_add/P", horner_mul_add, &p),
        ("horner8_mul_add/M", horner_mul_add, &m),
    ];
    for (name, f, x) in unary {
        g.bench_function(name, |b| {
            let mut out = vec![Interval::EMPTY; N];
            b.iter(|| {
                for i in 0..N {
                    out[i] = f(black_box(x[i]));
                }
                black_box(&out);
            })
        });
    }
    let ms = matrices(&p, &m);
    g.bench_function("det3/mixed", |b| {
        let mut out = vec![Interval::EMPTY; N];
        b.iter(|| {
            for i in 0..N {
                out[i] = det3(black_box(&ms[i]));
            }
            black_box(&out);
        })
    });
    g.finish();
}

// The series of the token API. Each loop below is that of `bench_binary` or of the
// group `unary`, with the operations `*_with` at the level `s`. Its `with_level` and
// the functions that it calls here are `#[inline(always)]`, so that the whole loop is
// inlined into the region that `Region::run` enters.

// A binary operation of the token API, at any level.
trait BinaryWith: Copy {
    fn call<S: Simd>(self, s: S, x: Interval, y: Interval) -> Interval;
}

// A unary operation of the token API, at any level.
trait UnaryWith: Copy {
    fn call<S: Simd>(self, s: S, x: Interval) -> Interval;
}

// Defines the unit struct `$t`, whose `$tr::call` returns `$e`.
macro_rules! op_with {
    ($t:ident: $tr:ident, |$s:ident, $($a:ident),+| $e:expr) => {
        #[derive(Clone, Copy)]
        struct $t;

        impl $tr for $t {
            #[inline(always)]
            fn call<S: Simd>(self, $s: S, $($a: Interval),+) -> Interval {
                $e
            }
        }
    };
}

op_with!(AddWith: BinaryWith, |s, x, y| x.add_with(s, y));
op_with!(MulWith: BinaryWith, |s, x, y| x.mul_with(s, y));
op_with!(DivWith: BinaryWith, |s, x, y| x.div_with(s, y));
op_with!(SqrtWith: UnaryWith, |s, x| x.sqrt_with(s));
op_with!(HornerWith: UnaryWith, |s, x| horner_with(s, x));
op_with!(HornerMulAddWith: UnaryWith, |s, x| horner_mul_add_with(s, x));

// `horner` at the level `s`.
#[inline(always)]
fn horner_with<S: Simd>(s: S, x: Interval) -> Interval {
    let mut acc = Interval::try_from((HORNER[8], HORNER[8])).unwrap();
    for &c in HORNER[..8].iter().rev() {
        acc = acc
            .mul_with(s, x)
            .add_with(s, Interval::try_from((c, c)).unwrap());
    }
    acc
}

// `horner_mul_add` at the level `s`.
#[inline(always)]
fn horner_mul_add_with<S: Simd>(s: S, x: Interval) -> Interval {
    let mut acc = Interval::try_from((HORNER[8], HORNER[8])).unwrap();
    for &c in HORNER[..8].iter().rev() {
        acc = acc.mul_add_with(s, x, Interval::try_from((c, c)).unwrap());
    }
    acc
}

// `det3` at the level `s`: the same operations on the same operands.
#[inline(always)]
fn det3_with<S: Simd>(s: S, m: &[Interval; 9]) -> Interval {
    let minor0 = m[4].mul_with(s, m[8]).sub_with(s, m[5].mul_with(s, m[7]));
    let minor1 = m[3].mul_with(s, m[8]).sub_with(s, m[5].mul_with(s, m[6]));
    let minor2 = m[3].mul_with(s, m[7]).sub_with(s, m[4].mul_with(s, m[6]));
    let a = m[0].mul_with(s, minor0);
    let b = m[1].mul_with(s, minor1);
    let c = m[2].mul_with(s, minor2);
    a.sub_with(s, b).add_with(s, c)
}

// The loop of `bench_binary` with `f`.
struct BinaryLoop<'a, F> {
    f: F,
    x: &'a [Interval],
    y: &'a [Interval],
    out: &'a mut [Interval],
}

impl<F: BinaryWith> WithLevel for BinaryLoop<'_, F> {
    type Output = ();

    #[inline(always)]
    fn with_level<S: Simd>(self, s: S) {
        for i in 0..N {
            self.out[i] = self.f.call(s, black_box(self.x[i]), black_box(self.y[i]));
        }
    }
}

// The loop of a unary series with `f`.
struct UnaryLoop<'a, F> {
    f: F,
    x: &'a [Interval],
    out: &'a mut [Interval],
}

impl<F: UnaryWith> WithLevel for UnaryLoop<'_, F> {
    type Output = ();

    #[inline(always)]
    fn with_level<S: Simd>(self, s: S) {
        for i in 0..N {
            self.out[i] = self.f.call(s, black_box(self.x[i]));
        }
    }
}

// The loop of `det3/mixed`.
struct Det3Loop<'a> {
    ms: &'a [[Interval; 9]],
    out: &'a mut [Interval],
}

impl WithLevel for Det3Loop<'_> {
    type Output = ();

    #[inline(always)]
    fn with_level<S: Simd>(self, s: S) {
        for i in 0..N {
            self.out[i] = det3_with(s, black_box(&self.ms[i]));
        }
    }
}

// How the series of the token API enter the region of a level that runs their loop.
trait Region: Copy {
    fn run<W: WithLevel>(self, w: W) -> W::Output;
}

// Through `dispatch`, at the highest level that the CPU has (`token/`).
#[derive(Clone, Copy)]
struct Dispatch;

impl Region for Dispatch {
    #[inline(always)]
    fn run<W: WithLevel>(self, w: W) -> W::Output {
        dispatch(w)
    }
}

// Through `vectorize` of a `V3` that `V3::try_new` returned (`token-v3/`). Without
// `#[inline(always)]` on the closure, LLVM left the closure of `det3/mixed`, the
// largest loop, out of the region in a plain x86-64 build: the region jumped to it,
// and it ran without the target features of `V3`.
#[cfg(target_arch = "x86_64")]
impl Region for V3 {
    #[inline(always)]
    fn run<W: WithLevel>(self, w: W) -> W::Output {
        self.vectorize(
            #[inline(always)]
            || w.with_level(self),
        )
    }
}

fn bench_binary_with(
    c: &mut Criterion,
    r: impl Region,
    name: &str,
    f: impl BinaryWith,
    classes: &[&str],
    x_scale: f64,
) {
    let mut g = c.benchmark_group(name);
    g.throughput(Throughput::Elements(N as u64));
    for cl in classes {
        let (x, y) = binary_operands(cl, x_scale);
        g.bench_function(BenchmarkId::from_parameter(cl), |b| {
            let mut out = vec![Interval::EMPTY; N];
            b.iter(|| {
                r.run(BinaryLoop {
                    f,
                    x: &x,
                    y: &y,
                    out: &mut out,
                });
                black_box(&out);
            })
        });
    }
    g.finish();
}

fn bench_unary_with(
    g: &mut BenchmarkGroup<'_, WallTime>,
    r: impl Region,
    name: &str,
    f: impl UnaryWith,
    x: &[Interval],
) {
    g.bench_function(name, |b| {
        let mut out = vec![Interval::EMPTY; N];
        b.iter(|| {
            r.run(UnaryLoop {
                f,
                x,
                out: &mut out,
            });
            black_box(&out);
        })
    });
}

// The series of `intervals_bench` that the token API has, but `sub`, under `prefix/`,
// with the same operands. `horner8/*` multiplies and adds with `mul_with` and
// `add_with`, and `horner8_mul_add/*` with `mul_add_with`.
fn token_series(c: &mut Criterion, r: impl Region, prefix: &str) {
    let name = |series: &str| format!("{prefix}/{series}");
    bench_binary_with(c, r, &name("add"), AddWith, &ADD_CLASSES, 1.0);
    bench_binary_with(c, r, &name("mul"), MulWith, &ALL_CLASSES, 1.0);
    bench_binary_with(c, r, &name("mul_tiny"), MulWith, &ALL_CLASSES, TINY);
    bench_binary_with(c, r, &name("div"), DivWith, &DIV_CLASSES, 1.0);

    let mut g = c.benchmark_group(name("unary"));
    g.throughput(Throughput::Elements(N as u64));
    let (p, m) = unary_operands();
    bench_unary_with(&mut g, r, "sqrt/P", SqrtWith, &p);
    bench_unary_with(&mut g, r, "sqrt/M", SqrtWith, &m);
    bench_unary_with(&mut g, r, "horner8/P", HornerWith, &p);
    bench_unary_with(&mut g, r, "horner8/M", HornerWith, &m);
    bench_unary_with(&mut g, r, "horner8_mul_add/P", HornerMulAddWith, &p);
    bench_unary_with(&mut g, r, "horner8_mul_add/M", HornerMulAddWith, &m);
    let ms = matrices(&p, &m);
    g.bench_function("det3/mixed", |b| {
        let mut out = vec![Interval::EMPTY; N];
        b.iter(|| {
            r.run(Det3Loop {
                ms: &ms,
                out: &mut out,
            });
            black_box(&out);
        })
    });
    g.finish();
}

fn token_bench(c: &mut Criterion) {
    token_series(c, Dispatch, "token");
    #[cfg(target_arch = "x86_64")]
    match V3::try_new() {
        Some(v3) => token_series(c, v3, "token-v3"),
        None => eprintln!("Skipped the series token-v3/*: `V3::try_new()` returned `None`."),
    }
}

criterion_group!(benches, intervals_bench, token_bench);
criterion_main!(benches);
