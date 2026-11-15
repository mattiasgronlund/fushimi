// Throughput and latency of the rounding primitives of the selected backend.
//
// Throughput: N independent operations. Latency: a chain of N operations, each of
// which depends on the result of the previous one. All inputs are normal numbers
// of moderate magnitude, so the generic backend always takes its fast paths.

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use inari::__bench::*;
use std::hint::black_box;

const N: usize = 1024;

// Deterministic values in ±[1, 2).
fn values(seed: u64, n: usize) -> Vec<f64> {
    let mut s = seed;
    (0..n)
        .map(|_| {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let x = 1.0 + (s >> 11) as f64 / (1u64 << 53) as f64;
            if s & 1 == 0 {
                x
            } else {
                -x
            }
        })
        .collect()
}

fn vectors(seed: u64) -> Vec<F64X2> {
    values(seed, 2 * N)
        .chunks(2)
        .map(|c| constant(c[0], c[1]))
        .collect()
}

fn bench_binary(c: &mut Criterion, name: &str, f: fn(F64X2, F64X2) -> F64X2, k: F64X2) {
    let x = vectors(1);
    let y = vectors(2);
    let mut g = c.benchmark_group(name);
    g.throughput(Throughput::Elements(N as u64));
    g.bench_function(BenchmarkId::new("throughput", N), |b| {
        let mut out = vec![constant(0.0, 0.0); N];
        b.iter(|| {
            for i in 0..N {
                out[i] = f(black_box(x[i]), black_box(y[i]));
            }
            black_box(&out);
        })
    });
    g.bench_function(BenchmarkId::new("latency", N), |b| {
        b.iter(|| {
            let mut acc = constant(1.0, 1.5);
            for _ in 0..N {
                acc = f(acc, black_box(k));
            }
            black_box(acc)
        })
    });
    g.finish();
}

fn primitives(c: &mut Criterion) {
    // The constants of the latency chains keep the values bounded.
    bench_binary(c, "add_ru", add_ru, constant(1e-3, 1e-3));
    bench_binary(c, "mul_ru", mul_ru, constant(1.0 - 1e-6, 1.0 + 1e-6));
    bench_binary(c, "div_ru", div_ru, constant(1.0 + 1e-6, 1.0 - 1e-6));

    let (x, y, z) = (vectors(1), vectors(2), vectors(3));
    let mut g = c.benchmark_group("mul_add_ru");
    g.throughput(Throughput::Elements(N as u64));
    g.bench_function(BenchmarkId::new("throughput", N), |b| {
        let mut out = vec![constant(0.0, 0.0); N];
        b.iter(|| {
            for i in 0..N {
                out[i] = mul_add_ru(black_box(x[i]), black_box(y[i]), black_box(z[i]));
            }
            black_box(&out);
        })
    });
    // Both lanes converge to l / (1 - k) = 4, a float: the 125th result of lane 0
    // and the 76th of lane 1 are 4, and every later step is exact (0.75 * 4 + 1 =
    // 0.625 * 4 + 1.5 = 4). Both lanes are exact in 930 of the 1024 steps, and
    // round up (RU > RN) in only 33 and 32. Each call starts again at [1, 1.5], so
    // a backend that branches on the rounding error sees the same outcomes in
    // every call, nearly all of them the same way.
    g.bench_function(BenchmarkId::new("latency", N), |b| {
        let (k, l) = (constant(0.75, 0.625), constant(1.0, 1.5));
        b.iter(|| {
            let mut acc = constant(1.0, 1.5);
            for _ in 0..N {
                acc = mul_add_ru(acc, black_box(k), black_box(l));
            }
            black_box(acc)
        })
    });
    // acc = acc² + c rounded up, with c = -1.9 in both lanes, a chaotic map: the
    // mean of ln |2 acc| along the orbit, its Lyapunov exponent, is about 0.55.
    // acc is carried from one call to the next, so the calls follow one orbit,
    // which enters a cycle of 37964025 steps after about 1.7e7 steps (lane 0) and
    // 5.7e7 (lane 1). Along it |acc| stays in [3e-8, 1.9], so every step takes
    // the fast path, and only one step in each pass of the cycle is exact. About
    // half of the steps round up, and the last 16 outcomes do not help to predict
    // the next. The result is negative in about 63 % of the steps, and its
    // history predicts its sign little better than that bias. So where a backend
    // branches on the rounding error or on the sign of the result, as generic's
    // `mul_add1_ru_fast` and `step_up` do in their source, the branch is
    // mispredicted often. The steps square acc (a = b), and a compiler may merge
    // the checks of a and b, so a step can take fewer instructions than with
    // three distinct inputs. The start is not a short dyadic: from 0.5 the first
    // step would be exact, as 0.5² - 1.9 is a float.
    g.bench_function(BenchmarkId::new("latency_inexact", N), |b| {
        let c = constant(-1.9, -1.9);
        let mut acc = constant(0.3, -0.7);
        b.iter(|| {
            // The loop runs on a copy whose address is never taken, so that the
            // chain needs no store or load of it. black_box(x) at each step would
            // add both.
            let mut x = acc;
            for _ in 0..N {
                x = mul_add_ru(x, x, black_box(c));
            }
            acc = x;
            black_box(x)
        })
    });
    g.finish();

    let x: Vec<f64> = values(4, N).iter().map(|x| x.abs()).collect();
    let mut g = c.benchmark_group("sqrt1_ru");
    g.throughput(Throughput::Elements(N as u64));
    g.bench_function(BenchmarkId::new("throughput", N), |b| {
        let mut out = vec![0.0; N];
        b.iter(|| {
            for i in 0..N {
                out[i] = sqrt1_ru(black_box(x[i]));
            }
            black_box(&out);
        })
    });
    g.bench_function(BenchmarkId::new("latency", N), |b| {
        b.iter(|| {
            let mut acc = 3.0;
            for _ in 0..N {
                // √(acc + 3) stays in [1, 3).
                acc = sqrt1_ru(acc + black_box(3.0));
            }
            black_box(acc)
        })
    });
    g.finish();
}

criterion_group!(benches, primitives);
criterion_main!(benches);
