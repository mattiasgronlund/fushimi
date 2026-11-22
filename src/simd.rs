//! Interval arithmetic at a level of the CPU detected at run time.
//!
//! Without a token, interval arithmetic such as `x + y` runs the backend that fushimi picks when
//! it is compiled, from the target of the build, its target features and the feature
//! `force-generic`. The `*_with` operations of [`Interval`](crate::Interval) and
//! [`DecInterval`](crate::DecInterval), such as [`Interval::add_with`](crate::Interval::add_with)
//! and [`DecInterval::add_with`](crate::DecInterval::add_with), take a token of a level, a value
//! of a type that implements [`Simd`], and run the backend that the token gives: [`Baseline`], on
//! every target, gives the build's, and on x86-64, `V2`, `V3` and `V4`, whose `try_new` checks
//! that the CPU has their target features, give the `sse42`, the `fma` and the `avx512f` backend
//! in the builds that the last paragraph names. Every token gives the same intervals, since these
//! operations return the tightest results (see
//! [Conformance to the standard](crate::_docs::conformance)), and the same decorations, since
//! those of `DecInterval` compute them from the arguments and these intervals alone; only the
//! speed differs.
//!
//! To run a loop at the highest level of a token that the CPU has, implement [`WithLevel`] for
//! a type whose [`with_level`](WithLevel::with_level) runs the loop, and call [`dispatch`] once,
//! around the loop. To run it at the level of a token, call the token's
//! [`vectorize`](Simd::vectorize). The code gets the target features of the level only where the
//! compiler inlines it into the region that `vectorize` enters, so mark `with_level`, a large
//! closure and the functions between them and the operations `#[inline(always)]`. The compiler
//! may also keep a short loop of operations in the region as a loop: in a crate built for
//! `x86-64` or for Haswell in Cargo's default release profile with rustc 1.98, it did not unroll
//! a loop of eight steps in the region of `V3` that evaluated a polynomial of degree 8 by
//! Horner's rule, each step making a coefficient from a constant `f64` with `Interval::try_from`
//! and calling [`Interval::mul_with`](crate::Interval::mul_with) and
//! [`Interval::add_with`](crate::Interval::add_with), or
//! [`Interval::mul_add_with`](crate::Interval::mul_add_with). Writing out the eight steps by hand
//! ran 16 fewer conditional branches per evaluation, the loop's 8 and the 8 tests of `try_from`,
//! which the compiler then made at compile time, and 78 to 180 fewer instructions, on the
//! arguments counted with cachegrind.
//!
//! On x86-64, unless the feature `force-generic` is on, `V2` gives the `sse42` backend in a build
//! without the target feature `sse4.2`, such as one for `x86-64`, the default of
//! `x86_64-unknown-linux-gnu`, `V3` gives the `fma` backend in a build that has neither the
//! target feature `avx512f` nor both `avx` and `fma`, such as one for `x86-64` or `x86-64-v2`,
//! where the slow paths that it takes from the portable backend run without the FMA, as those of
//! the build's backend do, and `V4` gives the `avx512f` backend in a build without the target
//! feature `avx512f`, such as one for `x86-64`, `x86-64-v2`, `x86-64-v3` or `haswell`. In other
//! builds, each gives the build's backend, that of [`Baseline`], as `V2` and `V3` do in a build
//! for `x86-64-v3` or `haswell`, and all three in one for `x86-64-v4`.

// A SIMD vector [x0; x1] stored in a register is usually depicted as:
//
//   +----------------+----------------+
//   |       x1       |       x0       |
//   +----------------+----------------+
//   |127           64|63             0|
//
//   r[63:0] = x0, r[127:64] = x1.

mod token;
pub(crate) use token::CrateBaseline;
pub use token::{dispatch, Baseline, Simd, WithLevel};
#[cfg(target_arch = "x86_64")]
pub use token::{V2, V3, V4};

cfg_if::cfg_if! {
    if #[cfg(docsrs)] {
        mod unimplemented;
        pub(crate) use unimplemented::*;

        // The generic backend provides `round_up_exact`, which `src/parse.rs` and
        // `src/dyadic.rs` call, and `two_prod_err` and `HAS_FMA`, which the fast paths of
        // `src/dyadic` use. The entries of the kernel use `HAS_FMA` only in a build without
        // `cfg(fushimi_kernel_dispatch)` (`src/dyadic/level.rs`), and its tests in every build.
        #[allow(dead_code)] // Only these and the functions that they call are used.
        mod generic;
        pub(crate) use generic::{round_up_exact, two_prod_err};
        #[cfg(any(test, not(fushimi_kernel_dispatch)))]
        pub(crate) use generic::HAS_FMA;
    } else if #[cfg(feature = "force-generic")] {
        mod generic;
        pub(crate) use generic::*;
    } else if #[cfg(target_arch = "aarch64")] {
        mod aarch64;
        pub(crate) use aarch64::*;

        // The generic backend provides the slow paths and the scalar operations of
        // `aarch64`, and is tested against it. `src/parse.rs` and `src/dyadic.rs` call its
        // `round_up_exact`, and the fast paths of `src/dyadic` its `two_prod_err` and
        // `HAS_FMA`.
        //
        // Only part of it is used: the functions that `aarch64` calls (`add_ru`, `div_ru`,
        // `mul_add_ru`, `mul_ru`, `sqrt_rd_ru`, `sqrt1_rd`, `sqrt1_ru` and `sub1_ru`) and the
        // functions these call, among them `round_up_exact`, `pow2` and `two_prod_err`; the
        // tests also use `round_ties_even` and `sub_ru`.
        #[allow(dead_code)]
        mod generic;
        pub(crate) use generic::{round_up_exact, two_prod_err, HAS_FMA};
        #[cfg(test)]
        mod differential_tests;
    } else if #[cfg(all(target_arch = "x86_64", target_feature = "sse4.2"))] {
        // Plain `x86-64`, without `sse4.2`, takes the portable backend below. On every x86-64
        // target without `fma`, among them `x86-64-v2`, which takes this backend, the kernel
        // picks the copy of its entries that uses an FMA at run time (`src/dyadic/level.rs`).
        mod x86_64;
        pub(crate) use x86_64::*;

        // The generic backend provides the slow paths and the scalar operations of
        // `fma` and `sse42`, and is tested against whichever backend the target
        // selects. `src/parse.rs` and `src/dyadic.rs` call its `round_up_exact`, and the fast
        // paths of `src/dyadic` its `two_prod_err` and `HAS_FMA`, the latter only in a build
        // without `cfg(fushimi_kernel_dispatch)` (`src/dyadic/level.rs`) or in the tests.
        //
        // Only part of it is used. Under `fma` and `sse42`: the functions that they call
        // (`add_ru`, `div_ru`, `mul_add_ru`, `mul_ru`, `sqrt_rd_ru`, `sqrt1_rd`, `sqrt1_ru`
        // and `sub1_ru`) and the functions these call, among them `round_up_exact`, `pow2`
        // and `two_prod_err`; the tests also use `round_ties_even` and `sub_ru`. Under
        // `avx512f`: only `round_up_exact`, `pow2`, `two_prod_err` and `split`; the tests use
        // `add_ru`, `sub_ru`, `sub1_ru`, `round_ties_even`, `round_up_exact`, the `*_impl`
        // functions and the functions these call.
        #[allow(dead_code)]
        mod generic;
        pub(crate) use generic::{round_up_exact, two_prod_err};
        #[cfg(any(test, not(fushimi_kernel_dispatch)))]
        pub(crate) use generic::HAS_FMA;
        #[cfg(test)]
        mod differential_tests;
    } else if #[cfg(all(target_arch = "wasm32", target_feature = "simd128"))] {
        mod wasm32;
        pub(crate) use wasm32::*;

        // The generic backend provides the slow paths and the scalar operations of
        // `wasm32`, and is tested against it. `src/parse.rs` and `src/dyadic.rs` call its
        // `round_up_exact`, and the fast paths of `src/dyadic` its `two_prod_err` and
        // `HAS_FMA`.
        //
        // Only part of it is used: the functions that `wasm32` calls (`add_ru`, `div_ru`,
        // `mul_add_ru`, `mul_ru`, `sqrt_rd_ru`, `sqrt1_rd`, `sqrt1_ru` and `sub1_ru`) and the
        // functions these call, among them `round_up_exact` and `pow2`, and `two_prod_err`
        // and `split`; the tests also use `round_ties_even` and `sub_ru`.
        #[allow(dead_code)]
        mod generic;
        pub(crate) use generic::{round_up_exact, two_prod_err, HAS_FMA};
        #[cfg(test)]
        mod differential_tests;
    } else if #[cfg(target_arch = "x86_64")] {
        // Plain `x86-64`, without `sse4.2`, takes the portable backend. The `sse42`, `fma` and
        // `avx512f` backends are compiled only as those of the tokens `V2`, `V3` and `V4`
        // (`src/simd/token.rs`).
        // The `classify_bits` of `Baseline` calls that of `x86_64` in place of that of
        // `src/classify.rs`: its intrinsics are of SSE and SSE2, which every x86-64 CPU has.
        mod generic;
        pub(crate) use generic::*;

        // Only what the tokens' copies and the `classify_bits` of `Baseline` call is used; the
        // tests also use the `sqrt1_rd_mxcsr` and `sqrt1_ru_mxcsr` of `sse42`.
        #[allow(dead_code, unused_imports)]
        mod x86_64;
        #[cfg(test)]
        mod differential_tests;
    } else {
        mod generic;
        pub(crate) use generic::*;
    }
}
