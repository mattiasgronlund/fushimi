# 🦊 fushimi

[![crates.io](https://img.shields.io/crates/v/fushimi.svg)](https://crates.io/crates/fushimi)
[![docs](https://img.shields.io/docsrs/fushimi)](https://docs.rs/fushimi)
[![rustc 1.85+](https://img.shields.io/badge/rustc-1.85%2B-lightgrey)](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0/)

**fushimi** is a Rust implementation of [interval arithmetic](https://en.wikipedia.org/wiki/Interval_arithmetic), a fork of [inari](https://github.com/unageek/inari) by Masashi Mizuno.

It [conforms](src/_docs/conformance.md) to [IEEE Std 1788.1-2017](https://doi.org/10.1109/IEEESTD.2018.8277144). It also implements a subset of [IEEE Std 1788-2015](https://doi.org/10.1109/IEEESTD.2015.7140721).

To use it, add it to the dependencies in your `Cargo.toml`:

```toml
[dependencies]
fushimi = "0.1"
```

## Supported Platforms

The following CPUs are supported and continuously tested:

- **x86-64**

  Haswell-based and newer processors are supported by a backend that needs AVX and FMA (`fma`). Nehalem-based and newer ones are supported by a separate backend that uses only SSE instructions (`sse42`), which is selected at compile time when the target CPU lacks AVX or FMA. A third backend (`avx512f`) uses the embedded rounding of AVX-512F, and is selected when the target CPU has AVX-512F and Rust is 1.89 or later; earlier stable versions do not report `avx512f` to `cfg(target_feature)`, so they select `fma` instead. CI tests `avx512f`, as the build's backend and at the token `V4` of `fushimi::simd` (with the feature `avx512`), only when its runner has AVX-512F. No backend for x86-64 changes the rounding mode; the SSE-only one is slower because it has to emulate the fused multiply-add, most of all for `sqrt`, `mul_add` and division (see [BENCHMARKS.md](BENCHMARKS.md)).

  To get one of these backends for the operations of intervals without a token, you need to specify the target CPU when building a crate that depends on fushimi. A build for a target CPU without SSE4.2, such as `x86-64`, the default for `x86_64-unknown-linux-gnu`, uses the portable backend for them (see below), except that, unless `force-generic` is enabled, the function with which `x * y`, `abs` and some other operations classify an interval, by comparing its bounds with zero, is the one of the x86-64 backends, which needs only SSE2. The operations that take a token of `fushimi::simd` can run `sse42`, `fma` and `avx512f` in a build for a target CPU without their features too, on a CPU that has the target features of the token (see [Building for Several x86-64 Levels](#building-for-several-x86-64-levels)). In a build for a target CPU without FMA, such as `x86-64` or `nehalem`, unless `force-generic` is enabled, the multi-precision kernel of the elementary functions checks at run time whether the CPU has FMA (see [Building for Several x86-64 Levels](#building-for-several-x86-64-levels)). One way to specify the target CPU is by using a [configuration file](https://doc.rust-lang.org/cargo/reference/config.html) in your project (see [example](https://github.com/unageek/graphest/blob/main/.cargo/config.toml); you may want to change `native` to `haswell`, or to `nehalem` for even wider compatibility, if you are going to distribute binaries).

- **AArch64 (ARM64)**

  The backend for AArch64 (`aarch64`) uses NEON (Advanced SIMD) instructions, which Rust's AArch64 targets for Linux and macOS enable, so it needs no `RUSTFLAGS` or target features. Like `fma` on x86-64, it does not change the rounding mode: it computes the directed roundings with error-free transformations and the fused multiply-add, and leaves the inputs that fail its checks to the portable backend (see below).

Other architectures, such as 32-bit x86 (`i686`), WebAssembly (`wasm32`) and RISC-V (`riscv64`), are supported by a portable backend (experimental). It only relies on floating-point arithmetic in the default rounding mode, and requires no target features, but it is slower than the backends for x86-64 and AArch64. It uses fused multiply-add instructions where the target has them. On WebAssembly, building with `RUSTFLAGS='-Ctarget-feature=+simd128'` selects a faster variant that uses 128-bit SIMD instructions.

Every backend assumes the default floating-point environment: rounding to nearest, with ties to even, and subnormal numbers not flushed to zero.

Interval literals, formatting and the elementary functions need neither GMP nor MPFR, nor a Cargo feature: fushimi computes them with code of its own, a multi-precision kernel for the elementary functions. CI tests x86-64 Linux, x86-64 Windows with MSVC (`x86_64-pc-windows-msvc`), AArch64 macOS, AArch64 Linux (`aarch64-unknown-linux-gnu`) under QEMU's user-mode emulation, where it runs only the unit tests, 32-bit x86 Linux (`i686-unknown-linux-gnu`) and WebAssembly (`wasm32-wasip1`, with and without `simd128`), and only builds for `wasm32-unknown-unknown` and `riscv64gc-unknown-linux-gnu`. On 64-bit Linux and macOS, the tests also compare fushimi's results with MPFR's, through the dev-dependencies `rug` and [`gmp-mpfr-sys`](https://crates.io/crates/gmp-mpfr-sys); on the other targets, they run without these comparisons.

## Building for Several x86-64 Levels

For the operations of intervals without a token, such as `x + y`, fushimi picks its x86-64 backend at compile time, from the target features that `cfg(target_feature)` reports for the target CPU, not by detecting the CPU at run time. As target CPUs, the microarchitecture levels of the [x86-64 psABI](https://gitlab.com/x86-psABIs/x86-64-ABI) select these backends: `x86-64`, the default for `x86_64-unknown-linux-gnu`, selects none of them, so that these operations use the portable backend, except, unless `force-generic` is enabled, for the function that classifies an interval (see above); `x86-64-v2` selects `sse42`; `x86-64-v3` selects `fma`, as `haswell` does; and `x86-64-v4` selects `avx512f` with Rust 1.89 or later, and `fma` with earlier stable versions (see above).

Apart from the tokens below, the one part of fushimi that detects the CPU at run time is the multi-precision kernel with which the elementary functions and those of `fushimi::cr` are computed, and only in a build for a target CPU without FMA, such as `x86-64` and `x86-64-v2`, unless `force-generic` is enabled. There each function of the kernel runs its fast path in a copy compiled with the target feature `fma` on a CPU that has FMA, and in a copy that computes the exact errors of its products with Dekker's algorithm on any other. The two return the same results: the Rocq proofs show that the fast paths of the kernel return the same with and without an FMA. The kernel detects FMA on its first call and keeps the answer, which each later call tests. CI builds for `x86-64` and for `nehalem`, which has the features of `x86-64-v2`, and tests both copies of the kernel in each, but does not build for the other levels by name.

The module `fushimi::simd` runs interval arithmetic at a level of the CPU detected at run time. Its tokens are `Baseline`, on every target, which gives the build's backend, and on x86-64 `V2`, `V3` and, with the feature `avx512` (see [Cargo Features](#cargo-features)), `V4`. `V2::try_new`, `V3::try_new` and `V4::try_new` return a token if the CPU has each target feature that `V2`, `V3` or `V4` lists, and `None` otherwise, and the `vectorize` of the token calls a closure inside a function that enables these features and no others (the region). The lists leave out `cmpxchg16b` and LAHF-SAHF, which the levels `x86-64-v2`, `x86-64-v3` and `x86-64-v4` also have, and which a token neither checks nor enables; those of `V3` and `V4` also leave out OSXSAVE, which std checks as part of `avx`. The methods `add_with`, `sub_with`, `mul_with`, `div_with`, `mul_add_with`, `recip_with`, `sqr_with` and `sqrt_with` of `Interval` and `DecInterval` take a token and run the backend that it gives: at `V2`, the `sse42` backend in a build for a target CPU without SSE4.2, such as `x86-64`; at `V3`, the `fma` backend in a build for a target CPU that has neither AVX-512F nor both AVX and FMA, such as `x86-64` or `x86-64-v2`, where the slow paths that it takes from the portable backend run without the FMA, as those of the build's backend do; and at `V4`, the `avx512f` backend in a build for a target CPU without AVX-512F, such as `x86-64`, `x86-64-v2`, `x86-64-v3` or `haswell`. In other builds, and in every build with `force-generic`, `V2`, `V3` and `V4` give the build's backend, as `Baseline` does. The function `dispatch` runs an implementation of the trait `WithLevel` at the highest of `V4`, `V3`, `V2` and `Baseline` that the CPU has, inside the `vectorize` of that token; without the feature `avx512`, the highest is `V3`. On x86-64, `try_new` and `dispatch` check the target features of the CPU at each call, so call them around a loop, not inside it. The code of `with_level`, or of a closure passed to `vectorize`, gets the target features of the level only where the compiler inlines it into the region, so mark `with_level`, a closure that is more than a few operations and the functions between them and the operations `#[inline(always)]`; code that is not inlined into the region computes the same results, but can be slower. Every token gives the same intervals, since these operations return the tightest results, and the same decorations, since those of `DecInterval` compute them from the arguments and these intervals alone; only the speed differs. The operations of `Interval` and `DecInterval` without a token, such as `x + y`, run the build's backend.

To give each CPU the code for its level without your users having to compile anything, build the whole program once per level, and pick one of the builds when it starts:

```bash
for level in x86-64 x86-64-v2 x86-64-v3 x86-64-v4; do
    RUSTFLAGS="-Ctarget-cpu=$level" cargo build --release --target x86_64-unknown-linux-gnu --target-dir target/$level
done
```

Each build lands in `target/<level>/x86_64-unknown-linux-gnu/release/`. The separate `--target-dir`s keep the builds from overwriting one another, and `--target` keeps `RUSTFLAGS` away from build scripts and procedural macros, which run on the build machine (see [`build.rustflags`](https://doc.rust-lang.org/cargo/reference/config.html#buildrustflags)): without it, a build for `x86-64-v4` on a machine without AVX-512 can die with SIGILL in one of them.

For a program, a small launcher, itself built for `x86-64`, can run the build for the highest level the CPU has. It must test the whole level as the psABI defines it, not only the features that select fushimi's backend, because a build for a level lets the compiler use any feature of the level in any code it compiles. In Rust 1.96, `std::is_x86_feature_detected!` has a name for each feature that `x86-64-v2`, `x86-64-v3` and `x86-64-v4` add to `x86-64` but LAHF-SAHF and OSXSAVE (LAHF-SAHF is bit 0 of ECX of CPUID leaf 0x8000_0001, which `core::arch::x86_64::__cpuid` returns); it tests OSXSAVE as part of AVX, and for AVX and AVX-512 it also tests that the operating system has enabled them.

For a shared library (a `cdylib`) on Linux with glibc 2.33 or later, the dynamic loader can do the picking. Install the builds for `x86-64-v2`, `x86-64-v3` and `x86-64-v4` in the subdirectories `glibc-hwcaps/x86-64-v2/`, `glibc-hwcaps/x86-64-v3/` and `glibc-hwcaps/x86-64-v4/` of the directory the library is found in, and the loader loads the copy for the highest level the CPU supports (see [ld.so(8)](https://man7.org/linux/man-pages/man8/ld.so.8.html), "glibc Hardware capabilities"). It does so in the directories of `LD_LIBRARY_PATH`, `RUNPATH` and `RPATH`, and for `dlopen` of a name without a slash; a name with a slash is a path, and the loader loads that file. The default directories, such as `/usr/lib`, or `/usr/lib/x86_64-linux-gnu` on Debian and Ubuntu, are searched the same way, and for a library installed in one of them, `/etc/ld.so.cache`, which `ldconfig` writes, prefers the copies in `glibc-hwcaps/` (ld.so(8), steps (4) and (5)). Glibc before 2.33, a CPU that has none of the levels in `glibc-hwcaps/`, and a program that loads the library by its path in that directory get the copy in the directory itself, which must therefore be the lowest level you ship. This is glibc's mechanism: musl, macOS and Windows do not have it.

## Correctly Rounded Functions

The module `fushimi::cr` has the elementary functions of intervals other than `cbrt` and `hypot` as functions of an `f64` (of two for `atan2` and `pow`, and of an `f64` and an `i32` for `powi`), each rounded to nearest with ties to even (`_rn`), toward -∞ (`_rd`) and toward +∞ (`_ru`), computed with the same kernel:

```rust
use fushimi::cr;
assert_eq!(cr::exp_rn(0.0), 1.0);
assert!(cr::sin_rd(1.0) < cr::sin_ru(1.0));
assert_eq!(cr::pow_rn(-2.0, 3.0), -8.0);
```

They are correctly rounded wherever a rule or Ziv's strategy, with enclosures of up to 4,096 bits, settles the argument. At an argument that reaches that cap, they return the rounding of a bound of the last enclosure, which is not known to be correctly rounded, but none of the hard-to-round arguments that CORE-MATH lists for these functions reaches it. The documentation of the module gives their values at the zeros, at the infinities and outside the domains, which are MPFR's, and those of `pow` at x < 0. Tests on 64-bit Linux and macOS compare them with MPFR in all three roundings.

The module also has `cbrt`, `hypot` (of two `f64`s) and `sqrt` in the same three roundings. `cbrt` and `hypot` compute an exact integer cube or square root where a fast path in `f64` does not decide the rounding, without Ziv's strategy and so with no cap, `sqrt_rn` is `f64::sqrt`, and `sqrt_rd` and `sqrt_ru` are those of the backend of the interval arithmetic. The Rocq proofs show these correctly rounded at every finite argument (x >= 0 for `sqrt`), `sqrt_rd` and `sqrt_ru` as the portable backend computes them, and tests compare them with MPFR too. `Interval::cbrt` and `Interval::hypot` compute their bounds with the functions of the kernel that `cbrt_rd`, `cbrt_ru`, `hypot_rd` and `hypot_ru` call.

## Cargo Features

- `force-generic` - Uses the portable backend (see above) on x86-64, AArch64 and WebAssembly with `simd128` too, and at every token of `fushimi::simd`. It is slower. On x86-64 it also keeps the multi-precision kernel from detecting the CPU at run time (see [Building for Several x86-64 Levels](#building-for-several-x86-64-levels)): the kernel then uses FMA instructions only where the target CPU has FMA.
- `avx512` - Adds the token `V4` (AVX-512) to `fushimi::simd`; needs Rust 1.89.

## [Changelog](CHANGELOG.md)

## Building the Documentation Locally

```bash
RUSTDOCFLAGS="--cfg docsrs --html-in-header /path/to/fushimi/src/_docs/header.html" cargo doc --open
```

Ensure that the absolute path to [`header.html`](src/_docs/header.html) is specified.

## Related Project

- [Graphest](https://github.com/unageek/graphest) - A faithful graphing calculator.

## References

- IEEE Std 1788-2015 - IEEE Standard for Interval Arithmetic. [DOI: 10.1109/IEEESTD.2015.7140721](https://doi.org/10.1109/IEEESTD.2015.7140721)
- IEEE Std 1788.1-2017 - IEEE Standard for Interval Arithmetic (Simplified). [DOI: 10.1109/IEEESTD.2018.8277144](https://doi.org/10.1109/IEEESTD.2018.8277144)
