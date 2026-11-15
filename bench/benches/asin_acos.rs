// Throughput of `asin` and `acos` on two sets of arguments: the correctly rounded functions
// of `inari::cr` in the three roundings, `Interval::asin` and `Interval::acos` of the point
// intervals [x, x], and, as a reference, `f64::asin` and `f64::acos`, which call the C
// library of the platform. The sets:
// - "sc": the 42,020 arguments of acos that solidcore recorded, in the order of the file
//   that the environment variable `INARI_ACOS_ARGS` names, a tab-separated file with the
//   bits of the argument in hexadecimal in its third column;
// - "cal": 4,096 arguments uniform in [-1, 1), from SplitMix64 seeded with 7.
// An iteration calls the function once on each argument of a set:
// `INARI_ACOS_ARGS=<file> cargo bench --bench asin_acos`.

use criterion::{
    criterion_group, criterion_main, BenchmarkId, Criterion, SamplingMode, Throughput,
};
use inari::{cr, Interval};
use std::hint::black_box;

const CAL: usize = 4096;

// SplitMix64, as `Rng` in src/dyadic/tests.rs, for deterministic inputs.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    // In [0, 1).
    fn unit(&mut self) -> f64 {
        (self.next() % (1 << 53)) as f64 / (1u64 << 53) as f64
    }
}

// The arguments of "sc", in file order.
fn solidcore() -> Vec<f64> {
    let path = std::env::var("INARI_ACOS_ARGS")
        .expect("INARI_ACOS_ARGS must name the file of solidcore's arguments of acos");
    let text = std::fs::read_to_string(&path).expect(&path);
    let xs: Vec<f64> = text
        .lines()
        .filter(|l| !l.is_empty())
        .map(|l| {
            let bits = l.split('\t').nth(2).expect(l);
            f64::from_bits(u64::from_str_radix(bits, 16).expect(l))
        })
        .collect();
    assert!(!xs.is_empty(), "no arguments in {path}");
    xs
}

// The arguments of "cal".
fn calibration() -> Vec<f64> {
    let mut rng = Rng(7);
    (0..CAL).map(|_| -1.0 + 2.0 * rng.unit()).collect()
}

// A set of arguments and its name.
type Set<T> = (&'static str, Vec<T>);

// The group `name`: `f` on each set. `f` is a function item, not a function pointer, so the
// loop calls it directly.
fn group<T: Copy, R>(c: &mut Criterion, name: &str, sets: &[Set<T>], f: impl Fn(T) -> R) {
    let mut g = c.benchmark_group(name);
    // An iteration of "sc" makes 42,020 calls, so at 25 ns a call or more, criterion's
    // default, linear sampling, which runs it 1 + 2 + ... + 100 = 5,050 times at least, would
    // take more than the default 5 s of measurement. Flat sampling runs it the same number of
    // times per sample.
    g.sampling_mode(SamplingMode::Flat);
    for (set, xs) in sets {
        g.throughput(Throughput::Elements(xs.len() as u64));
        g.bench_function(BenchmarkId::from_parameter(set), |b| {
            b.iter(|| {
                for &x in xs {
                    black_box(f(black_box(x)));
                }
            })
        });
    }
    g.finish();
}

fn asin_acos_bench(c: &mut Criterion) {
    let points = [("sc", solidcore()), ("cal", calibration())];
    let intervals: Vec<Set<Interval>> = points
        .iter()
        .map(|(set, xs)| {
            let iv = xs.iter().map(|&x| Interval::try_from((x, x)).unwrap());
            (*set, iv.collect())
        })
        .collect();
    group(c, "asin_rn", &points, cr::asin_rn);
    group(c, "asin_rd", &points, cr::asin_rd);
    group(c, "asin_ru", &points, cr::asin_ru);
    group(c, "interval_asin", &intervals, Interval::asin);
    group(c, "libm_asin", &points, f64::asin);
    group(c, "acos_rn", &points, cr::acos_rn);
    group(c, "acos_rd", &points, cr::acos_rd);
    group(c, "acos_ru", &points, cr::acos_ru);
    group(c, "interval_acos", &intervals, Interval::acos);
    group(c, "libm_acos", &points, f64::acos);
}

criterion_group!(benches, asin_acos_bench);
criterion_main!(benches);
