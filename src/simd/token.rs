// The tokens of the levels of the CPU, and the backend that each one gives the `*_with`
// operations of `Interval` and `DecInterval` (`src/arith.rs` and `src/basic.rs`) in each build.
//
// A token of a level above `Baseline` exists only once its `try_new` has detected each target
// feature in its list, which is what makes it safe to call the functions compiled with those
// features: its `vectorize` region and its copies of the backend functions below. The list
// leaves out `cmpxchg16b` and LAHF-SAHF, features of the psABI levels that the source of the
// backends does not use, and OSXSAVE, which std checks as part of `avx`.
//
// The backend of a token is that of the build, unless the token's level is above the build's:
//
//   build                        Baseline     V2              V3            V4
//   docsrs, force-generic,       the build's  the build's     the build's   the build's
//     avx512f, other
//     architectures
//   avx + fma (x86-64-v3)        fma          fma             fma           avx512f (copies)
//   sse4.2 (x86-64-v2)           sse42        sse42           fma (copies)  avx512f (copies)
//   plain x86-64                 generic      sse42 (copies)  fma (copies)  avx512f (copies)
//
// In the row of plain `x86-64`, every method of `Baseline` but `classify_bits` calls the portable
// backend; `classify_bits`, as at `V2`, `V3` and `V4`, is that of `src/simd/x86_64.rs`, which uses
// only SSE and SSE2 (see `Baseline` below).
//
// A copy is a function with the level's target features that calls the backend function, which
// is `#[inline(always)]` in such a build, so that the copy compiles it with those features. The
// functions of `avx512f`, the backend of `V4`, are `#[inline]` instead, with the target feature
// `avx512f` (see `src/simd/x86_64/avx512f.rs`), and LLVM inlined them into the copies (objdump,
// row 138). The thin layers of `src/simd/x86_64.rs` and its submodules are `#[inline(always)]` in
// every build, so that they take the target features of their caller.

use super::F64X2;
use std::fmt::Debug;

mod sealed {
    use crate::simd::F64X2;

    // The functions of the backend that the `*_with` operations of `Interval` and `DecInterval`
    // call (those of `DecInterval` through those of `Interval`), with `classify_bits`, which
    // `Interval::classify_with` and `classify2_with` (`src/classify.rs`) call for them. Each
    // method computes what the function of the same name computes in the backend that the token
    // gives (the table above), and `classify_bits` what `crate::classify::classify_bits` computes
    // with the `bitmask`, `ge`, `le` and `splat` of that backend. Where that backend is one of
    // `src/simd/x86_64.rs`, and for `Baseline` and `CrateBaseline` in an x86-64 build without
    // `force-generic` whose backend is the portable one (one without `sse4.2`, such as for plain
    // `x86-64`), `classify_bits` is the one of `src/simd/x86_64.rs`, which computes the same class
    // code on every argument: it makes the same comparisons of the lanes with zero, and packs
    // their results into the same bits. `classify_bits` takes `x` by reference, as
    // `crate::classify::classify_bits` does, for the reason given there.
    // `src/simd/generic.rs` says what its functions compute. The other backends need not compute
    // the same on every argument: where an argument is a NaN, or the arguments are zeros of
    // opposite signs, `max` of `src/simd/x86_64.rs` (`_mm_max_pd`) can return another value than
    // `max` of `src/simd/generic.rs`. A user can call the methods through the bound `S: Simd`,
    // but cannot name the trait. They are `#[doc(hidden)]`, the convention for items outside a
    // crate's API, and the docs of `Simd` say that they are inari's internals.
    pub trait Backend {
        #[doc(hidden)]
        fn add_ru(self, x: F64X2, y: F64X2) -> F64X2;
        #[doc(hidden)]
        fn classify_bits(self, x: &F64X2) -> u8;
        #[doc(hidden)]
        fn div_ru(self, x: F64X2, y: F64X2) -> F64X2;
        #[doc(hidden)]
        fn max(self, x: F64X2, y: F64X2) -> F64X2;
        #[doc(hidden)]
        fn mul_add_ru(self, x: F64X2, y: F64X2, z: F64X2) -> F64X2;
        #[doc(hidden)]
        fn mul_ru(self, x: F64X2, y: F64X2) -> F64X2;
        #[doc(hidden)]
        fn neg0(self, x: F64X2) -> F64X2;
        #[doc(hidden)]
        fn shuffle02(self, x: F64X2, y: F64X2) -> F64X2;
        #[doc(hidden)]
        fn shuffle03(self, x: F64X2, y: F64X2) -> F64X2;
        #[doc(hidden)]
        fn shuffle13(self, x: F64X2, y: F64X2) -> F64X2;
        #[doc(hidden)]
        fn splat(self, x: f64) -> F64X2;
        #[doc(hidden)]
        fn sqrt_rd_ru(self, x: F64X2) -> F64X2;
        #[doc(hidden)]
        fn sqrt1_ru(self, x: f64) -> f64;
        #[doc(hidden)]
        fn swap(self, x: F64X2) -> F64X2;
    }
}

/// A token of a level of the CPU: it gives the backend that the `*_with` operations of
/// [`Interval`](crate::Interval) and [`DecInterval`](crate::DecInterval) run, such as
/// [`Interval::add_with`](crate::Interval::add_with), and the target features of its
/// [`vectorize`](Simd::vectorize).
///
/// The tokens are [`Baseline`], on every target, and on x86-64 `V2`, `V3` and `V4`, whose
/// `try_new` returns one only on a CPU that has their target features. Only inari implements
/// `Simd`. The methods of its supertrait `Backend` are inari's internals: the type of the vectors
/// that they take and return differs by build (`[f64; 2]` in a build for `x86-64`, `__m128d` in
/// one for `haswell` without the feature `force-generic`), so a call that compiles in one build
/// need not compile in another, and they can change in any release. Every token gives the same
/// intervals, since these operations return the tightest results (see
/// [Conformance to the standard](crate::_docs::conformance)), and the same decorations, since those
/// of `DecInterval` compute them from the arguments and these intervals alone; only the speed
/// differs.
///
/// A function generic over `S: Simd` runs the operations at the level of the token that it is
/// given:
///
/// ```
/// use inari::{simd::{Baseline, Simd}, *};
///
/// // `#[inline(always)]`, so that it is compiled with the target features of the region of
/// // `vectorize` that calls it.
/// #[inline(always)]
/// fn dot<S: Simd>(s: S, xs: &[Interval], ys: &[Interval]) -> Interval {
///     xs.iter()
///         .zip(ys)
///         .fold(const_interval!(0.0, 0.0), |acc, (&x, &y)| x.mul_add_with(s, y, acc))
/// }
///
/// let xs = [const_interval!(1.0, 2.0), const_interval!(-1.0, 1.0)];
/// let ys = [const_interval!(3.0, 3.0), const_interval!(2.0, 4.0)];
/// let d = const_interval!(-1.0, 10.0);
/// assert_eq!(Baseline.vectorize(|| dot(Baseline, &xs, &ys)), d);
/// #[cfg(target_arch = "x86_64")]
/// {
///     if let Some(s) = inari::simd::V3::try_new() {
///         assert_eq!(s.vectorize(#[inline(always)] || dot(s, &xs, &ys)), d);
///     }
/// }
/// ```
pub trait Simd: sealed::Backend + Copy + Debug + Send + Sync + 'static {
    /// Calls `f` inside a function compiled with the target features of this level (the
    /// region), and returns what `f` returns.
    ///
    /// The code of `f` gets those features only where the compiler inlines it into the region.
    /// The `*_with` operations of [`Interval`](crate::Interval) and
    /// [`DecInterval`](crate::DecInterval) are `#[inline(always)]`, so they are inlined into their
    /// caller. Mark a closure that is more than a few operations `#[inline(always)]`, and the
    /// functions between it and the operations too. Code that is not inlined into the region
    /// computes the same results, but can be slower. For [`Baseline`], `vectorize` only calls `f`.
    ///
    /// ```
    /// use inari::{simd::{Baseline, Simd}, *};
    ///
    /// let xs = [const_interval!(1.0, 2.0), const_interval!(-0.5, 0.5), const_interval!(3.0, 3.0)];
    /// let zero = const_interval!(0.0, 0.0);
    /// let s = Baseline;
    /// let sum = s.vectorize(|| xs.iter().fold(zero, |acc, &x| acc.add_with(s, x)));
    /// assert_eq!(sum, const_interval!(3.5, 5.5));
    /// #[cfg(target_arch = "x86_64")]
    /// {
    ///     if let Some(s) = inari::simd::V2::try_new() {
    ///         let sum_v2 = s.vectorize(
    ///             #[inline(always)]
    ///             || xs.iter().fold(zero, |acc, &x| acc.add_with(s, x)),
    ///         );
    ///         assert_eq!(sum_v2, sum);
    ///     }
    /// }
    /// ```
    fn vectorize<F: FnOnce() -> R, R>(self, f: F) -> R;
}

/// The token of the level of the build's target CPU: its backend is the build's, which the
/// operations of [`Interval`](crate::Interval) and [`DecInterval`](crate::DecInterval) without a
/// token run (for an `Interval` `x`, `x + y` is `x.add_with(Baseline, y)`).
///
/// It exists on every target.
///
/// ```
/// use inari::{simd::{Baseline, Simd}, *};
///
/// let x = const_interval!(1.0, 2.0);
/// let y = const_interval!(-3.0, 0.5);
/// assert_eq!(x.add_with(Baseline, y), x + y);
/// assert_eq!(Baseline.vectorize(|| x.sub_with(Baseline, y)), x - y);
/// ```
#[derive(Clone, Copy, Debug, Default)]
pub struct Baseline;

impl Simd for Baseline {
    #[inline(always)]
    fn vectorize<F: FnOnce() -> R, R>(self, f: F) -> R {
        f()
    }
}

/// A computation at any level, which [`dispatch`] runs at the highest level of a token that the
/// CPU has.
///
/// ```
/// use inari::{simd::{dispatch, Simd, WithLevel}, *};
///
/// // The sum of the intervals.
/// struct Sum<'a>(&'a [Interval]);
///
/// impl WithLevel for Sum<'_> {
///     type Output = Interval;
///
///     #[inline(always)]
///     fn with_level<S: Simd>(self, s: S) -> Interval {
///         let zero = const_interval!(0.0, 0.0);
///         self.0.iter().fold(zero, |acc, &x| acc.add_with(s, x))
///     }
/// }
///
/// let xs = [const_interval!(1.0, 2.0), const_interval!(-0.5, 0.5), const_interval!(3.0, 3.0)];
/// assert_eq!(dispatch(Sum(&xs)), const_interval!(3.5, 5.5));
/// ```
pub trait WithLevel {
    /// The result of the computation, which [`dispatch`] returns.
    ///
    /// ```
    /// use inari::{simd::{dispatch, Simd, WithLevel}, *};
    ///
    /// // The sums of the intervals of two slices, element by element.
    /// struct AddAll<'a>(&'a [Interval], &'a [Interval]);
    ///
    /// impl WithLevel for AddAll<'_> {
    ///     type Output = Vec<Interval>;
    ///
    ///     #[inline(always)]
    ///     fn with_level<S: Simd>(self, s: S) -> Vec<Interval> {
    ///         self.0.iter().zip(self.1).map(|(&x, &y)| x.add_with(s, y)).collect()
    ///     }
    /// }
    ///
    /// let xs = [const_interval!(1.0, 2.0), const_interval!(-0.5, 0.5)];
    /// let ys = [const_interval!(3.0, 3.0), const_interval!(1.0, 1.5)];
    /// let sums = [const_interval!(4.0, 5.0), const_interval!(0.5, 2.0)];
    /// assert_eq!(dispatch(AddAll(&xs, &ys)), sums);
    /// ```
    type Output;

    /// Runs the computation with the operations at the level of `s`.
    ///
    /// [`dispatch`] calls it inside the [`vectorize`](Simd::vectorize) of `s`. Mark it
    /// `#[inline(always)]`: its code gets the target features of the level only where the
    /// compiler inlines it into that region. Called on its own, it runs outside any region.
    ///
    /// ```
    /// use inari::{simd::{dispatch, Baseline, Simd, WithLevel}, *};
    ///
    /// // `Sum` as in the example of `WithLevel`.
    /// # struct Sum<'a>(&'a [Interval]);
    /// #
    /// # impl WithLevel for Sum<'_> {
    /// #     type Output = Interval;
    /// #
    /// #     #[inline(always)]
    /// #     fn with_level<S: Simd>(self, s: S) -> Interval {
    /// #         let zero = const_interval!(0.0, 0.0);
    /// #         self.0.iter().fold(zero, |acc, &x| acc.add_with(s, x))
    /// #     }
    /// # }
    /// let xs = [const_interval!(1.0, 2.0), const_interval!(-0.5, 0.5), const_interval!(3.0, 3.0)];
    /// // The same interval at every level.
    /// assert_eq!(Sum(&xs).with_level(Baseline), dispatch(Sum(&xs)));
    /// ```
    fn with_level<S: Simd>(self, s: S) -> Self::Output;
}

/// Runs `w` at the highest level of `V4`, `V3`, `V2` and [`Baseline`] that the CPU has, inside
/// that level's [`vectorize`](Simd::vectorize), and returns what `w` returns.
///
/// On targets other than x86-64, the level is `Baseline`. On x86-64, each call checks the
/// target features of the CPU (std caches what it detects) and enters a region, so call
/// `dispatch` around a loop, not inside it. Mark [`WithLevel::with_level`] `#[inline(always)]`,
/// as its code gets the target features of the level only where the compiler inlines it into
/// the region.
///
/// ```
/// use inari::{simd::{dispatch, Simd, WithLevel}, *};
///
/// // The sum of the intervals.
/// struct Sum<'a>(&'a [Interval]);
///
/// impl WithLevel for Sum<'_> {
///     type Output = Interval;
///
///     #[inline(always)]
///     fn with_level<S: Simd>(self, s: S) -> Interval {
///         let zero = const_interval!(0.0, 0.0);
///         self.0.iter().fold(zero, |acc, &x| acc.add_with(s, x))
///     }
/// }
///
/// let xs = [const_interval!(1.0, 2.0), const_interval!(-0.5, 0.5), const_interval!(3.0, 3.0)];
/// // One call for the whole loop.
/// assert_eq!(dispatch(Sum(&xs)), const_interval!(3.5, 5.5));
/// ```
pub fn dispatch<W: WithLevel>(w: W) -> W::Output {
    #[cfg(target_arch = "x86_64")]
    {
        // Without `#[inline(always)]` on the closures, LLVM left a large `with_level` out of
        // the regions in a plain `x86-64` build: the region jumped to the closure, which ran
        // without the target features of the level.
        if let Some(s) = V4::try_new() {
            return s.vectorize(
                #[inline(always)]
                || w.with_level(s),
            );
        }
        if let Some(s) = V3::try_new() {
            return s.vectorize(
                #[inline(always)]
                || w.with_level(s),
            );
        }
        if let Some(s) = V2::try_new() {
            return s.vectorize(
                #[inline(always)]
                || w.with_level(s),
            );
        }
    }
    Baseline.vectorize(|| w.with_level(Baseline))
}

// The build's backend, which the operations of `Interval` and `DecInterval` that have a `*_with`
// form call through `Baseline` (or through `CrateBaseline` below, whose backend is the same) when
// they take no token (for an `Interval` `x`, `x + y` is `x.add_with(CrateBaseline, y)`). The
// `classify_bits` of `Baseline` is that of `src/simd/x86_64.rs` in every x86-64 build without
// `force-generic` and `docsrs`, also where the build's backend is the portable one (see
// `classify_bits` below).
//
// A function that a user's crate can inline or instantiate, such as `add_with`, can call only
// functions that the crate exports. So `add_ru`, `div_ru` and `mul_ru`, which the crate's
// operations call out of line (only `mul_ru` where the `aarch64` backend is the build's, see below,
// and none of them on wasm32 with `simd128`), are called here from methods without `#[inline]`,
// which the crate exports in their place (where the portable backend is the build's on x86-64,
// `#[inline(always)]` methods call the copies of `div_ru` and `mul_ru` with Rust's ABI instead, see
// `div_ru` below, where the `aarch64` backend is the build's, the copies of `add_ru`, `div_ru` and
// `mul_ru` with the ABI `C`, and where the `fma` or `sse42` backend is, forwarders to `add_ru`,
// `div_ru` and `mul_ru`, see below for both; in all three, the crate's operations call `div_ru`
// and `mul_ru` themselves, directly or through `CrateBaseline` below). LLVM inlines these small
// methods into the crate's operations, which then call the backend functions as before, except
// that with one codegen unit, where the portable backend is the build's on aarch64, it inlined
// `mul_ru` into its method instead. Where the portable, `sse42` or `fma` backend is the build's,
// the backend functions are `#[inline(never)]` (except the portable ones on aarch64, see below),
// as otherwise LLVM would inline each into the method that calls it. Making the methods
// `#[inline(always)]` there (with that of `mul_add_ru` where `sse42` is the backend, see below),
// so that a user's crate calls the backend functions without them, made the crate export the
// backend functions, and its own operations then called them through the global offset table.
// Where `fma` or `sse42` is the backend, that cost 2 to 4 more instructions per `Interval::mul`,
// and per `Interval::mul_add` where `sse42` is, and none per `Interval::add` or `Interval::div`,
// whereas a user's loop of `*_with` calls that run the build's backend ran 14 to 16 fewer
// instructions per `add_with`, `mul_with` or `div_with` (29 to 31 for a `mul_with` of two
// intervals that have 0 in their interiors), but 3 to 5 more per `div_with` by an interval that
// has 0 in its interior (cachegrind, in Cargo's default release profile, row 143). Where the
// portable backend is, it cost up to 6 more instructions per call in a build for `x86-64` (21
// with one codegen unit; cachegrind, row 136). So there the methods call the copies, and where
// the `fma` or `sse42` backend is, the forwarders, which the crate's operations do not call.
//
// Where the `aarch64` backend is the build's, only `mul_ru` and its copy `mul_ru_c_abi` are
// `#[inline(never)]`: there LLVM inlines `add_ru` and `div_ru`, or their copies, into the crate's
// operations, which then take fewer instructions (counted under QEMU), whereas inlining `mul_ru`
// gives `Interval::mul` a stack frame and more instructions. Where the portable backend is the
// build's on aarch64 (with `force-generic`), none of the three is: there the attribute kept LLVM,
// in a build with fat LTO, from inlining them into a user's loops, and a harness built as the
// benchmarks are (fat LTO, one codegen unit) ran 14 to 22 more instructions per `add_ru`, `div_ru`
// or `mul_ru` of `src/__bench.rs`, and 93 more per 3x3 determinant of intervals, with it than
// without it (counted under QEMU, row 146). Nor does being out of line keep an ABI that passes
// their vectors in registers there, as the ABI `sysv64` does for the portable `div_ru` and `mul_ru`
// on x86-64: they take Rust's ABI, which passed them by pointer in Cargo's default release profile.
// `sqrt_rd_ru` has one caller in the crate's operations, which inlines it, and is
// `#[inline(always)]` where the portable, `sse42`, `fma` or `aarch64` backend is the build's, as
// is `mul_add_ru` where `fma` or `aarch64` is. Where `sse42` is the backend, the crate calls
// `mul_add_ru` out of line, as `add_ru`. The portable `mul_add_ru`, which is also the slow path
// of those of `fma`, `sse42` and `aarch64`, has no `#[inline]`: where it is the build's backend,
// `#[inline(always)]` cost `Interval::mul_add` 1 to 3 more instructions per call in a build for
// `x86-64` in Cargo's default release profile, and none with one codegen unit (cachegrind, row
// 136). Nor has its copy with the ABI `sysv64`, `mul_add_ru_sysv64` (see below). (`src/__bench.rs`,
// compiled only with the feature `__bench`, for the benchmarks, also calls `mul_add_ru`.)
//
// Where the `aarch64` backend is the build's, the methods `add_ru`, `div_ru` and `mul_ru` of
// `Baseline` are `#[inline(always)]` and call the copies of these functions with the ABI `C`,
// `add_ru_c_abi`, `div_ru_c_abi` and `mul_ru_c_abi`, which the crate exports, so that a user's
// crate calls them without the methods in between, with each vector and the result in a register
// (see below), whereas `CrateBaseline` calls `div_ru` and `mul_ru`. `x + y` and `x - y` of
// intervals call `add_ru_c_abi` through `CrateBaseline`, whose `add_ru` calls the method of
// `Baseline`, and LLVM inlined it into them in Cargo's default release profile. In a crate that
// links inari, built for `aarch64-unknown-linux-gnu` in that profile and counted under QEMU, a loop
// of `*_with` calls at `Baseline` then ran 7 fewer instructions per `add_with` or `sub_with`, 8
// fewer per `div_with` by a positive or a negative interval and per `recip_with` of one, 20 to 22
// fewer per `mul_with` (39 for a `mul_with` of two intervals that have 0 in their interiors) and 19
// fewer per `sqr_with` than with methods without `#[inline]` that called `add_ru`, `div_ru` and
// `mul_ru`, and each operation without a token that was counted ran as many or fewer: 12 to 14
// fewer per `Interval::mul` (8 for two intervals that have 0 in their interiors), 5 to 13 fewer per
// `Interval::sqr`, 8 to 12 fewer per `DecInterval::mul` and 4 to 6 fewer per `DecInterval::sqr`
// (row 155). Making `mul_ru` itself take the ABI `C`, with these methods `#[inline(always)]` or
// not, cost `Interval::mul` 9 or 10 more instructions per call for eight of the nine combinations
// of signs counted, built as the benchmarks are (fat LTO, one codegen unit, the feature `__bench`),
// where the copies cost none (row 155).
//
// The out-of-line `add_ru`, `div_ru` and `mul_ru` of the `fma` and `sse42` backends (and
// `mul_add_ru` of `sse42`) take the ABI `sysv64`, as do the out-of-line copies of vector
// functions that `V2` and `V3` have below. It passes and returns each `__m128d` in an `xmm`
// register on every x86-64 target, whether the crate exports the function or not, where Rust's
// ABI passes it by pointer. The lint `improper_ctypes_definitions` flags `__m128d`, whose layout
// Rust does not specify for C, but only Rust code calls these functions. `-unwind` lets a panic
// unwind through them, as through a function of Rust's ABI. Where the portable backend is the
// build's on x86-64, its `div_ru` and `mul_ru` take the ABI `sysv64` too, which passes and returns
// each `[f64; 2]` in two `xmm` registers, and `CrateBaseline` below calls them, whereas the methods
// of `Baseline` call their copies with Rust's ABI, `div_ru_rust_abi` and `mul_ru_rust_abi`. The
// lint flags `[f64; 2]` too ("passing raw arrays by value is not FFI-safe"). For `mul_add_ru` it
// is the other way round: the method of `Baseline` calls its copy with the ABI `sysv64`,
// `mul_add_ru_sysv64`, so a user's crate passes it the three vectors in six `xmm` registers, and
// `CrateBaseline` calls `mul_add_ru`, which takes Rust's ABI (see `mul_add_ru` of `CrateBaseline`
// below). The portable `add_ru` takes Rust's ABI: in a build for `x86-64`, it took each `[f64; 2]`
// by pointer in Cargo's default release profile, and in registers with one codegen unit, as LLVM
// may change the ABI of a function that only code in its codegen unit can call, and it returned its
// result through memory in both. (The portable `mul_add_ru`, which a user's crate can call on the
// slow path of the copy of `mul_add_ru` that `V3` has, took them by pointer in both.) Where the
// `aarch64` backend is the build's, its `add_ru`, `div_ru` and `mul_ru` take Rust's ABI too, and
// in Cargo's default release profile `mul_ru` took its vectors in registers (by pointer with the
// feature `__bench`) and returned its result through memory, and the methods of `Baseline` that
// called them, without `#[inline]`, took their vectors by pointer and returned their results
// through memory. Their copies `add_ru_c_abi`, `div_ru_c_abi` and `mul_ru_c_abi` take the ABI `C`,
// which passes and returns each `float64x2_t` in a register, and the lint flags `float64x2_t` too
// ("this struct has unspecified layout").
//
// The other functions that a `*_with` method of `Interval` or `DecInterval` reaches, and that
// rustc would not by itself inline into a user's crate on some target, are marked for it, apart
// from the backend functions that round upward or downward (`sqrt1_ru` as well as those above,
// and the copies of `V2`, `V3` and `V4` below, of which those that a build for their level inlines
// are `#[inline]`) and the functions that they call: `add_rn`, `all`, `and`, `bitmask`, `eq`, `ge`,
// `gt`, `le`, `lt`, `max`, `or` and `sub_rn` on aarch64, with the helpers of `aarch64/lanewise.rs`
// and `aarch64/fma.rs` that `mul_add_ru` and `sqrt_rd_ru` call on their fast paths, and the thin
// layers of `wasm32.rs` that a `*_with` method reaches are `#[inline(always)]`, as is
// `classify_bits` of `src/simd/x86_64.rs`, and
// `classify_bits` of `src/classify.rs`, `Interval::classify_with`, `classify2_with`, `inf_raw`,
// `sup_raw`, `with_infsup_raw`, `zero`, `is_empty`, `contains`, `is_common_interval` and
// `DecInterval::set_dec_impl` are `#[inline]`.
// So a `*_with` method instantiated in a user's crate calls out of line only functions that round
// upward or downward, and functions that they call (seen with rustc 1.96 in Cargo's default release
// profile when the `*_with` methods of `DecInterval` were added: at `Baseline` in builds for
// aarch64, riscv64gc, i686 and wasm32 with and without `simd128`, at `Baseline` and in the region
// of `V3` in builds for `x86-64`, `x86-64-v2` and `haswell`, and in that of `V2` in one for
// `x86-64`).
//
// Where the `fma` or `sse42` backend is the build's, the methods `add_ru`, `div_ru` and `mul_ru`
// of `Baseline` (and `mul_add_ru` where `sse42` is) are `#[inline(always)]` and call forwarders
// to these functions, `add_ru_exported`, `div_ru_exported`, `mul_ru_exported` and
// `mul_add_ru_exported`, which take the same ABI and which the crate exports, so that a user's
// crate calls them without the methods in between, with each vector and the result in a register.
// Each forwarder is one `jmp` to its function (see `add_ru_exported` in `x86_64/lanewise.rs`).
// `CrateBaseline` calls `add_ru`, `div_ru`, `mul_ru` and `mul_add_ru` themselves, which the crate
// does not export, so that its operations, `x + y` and `x - y` of intervals among them, call them
// directly, not through the global offset table. In a crate that links inari, built for `haswell`
// and for `x86-64-v2` in Cargo's default release profile, each operation without a token that
// was counted then ran as many instructions and conditional branches as with the methods without
// `#[inline]` above, and a loop of `*_with` calls at `Baseline`, at `V3` in the build for `haswell`
// or at `V2` in that for `x86-64-v2`, whose methods there are those of `Baseline`, ran 14 fewer
// instructions per `add_with`, 13 fewer per `mul_with` (27 to 29 for two intervals that have 0 in
// their interiors), 15 fewer per `div_with` that divides, 191 to 322 fewer per value of a
// polynomial of degree 8 by Horner's scheme with `mul_with` and `add_with`, 120 to 232 fewer with
// `mul_add_with` where `sse42` is the backend, and 207 to 210 fewer per 3x3 determinant. It lost
// in two places. It ran 3 more instructions (5 where `sse42` is the backend) per `div_with` of a
// positive interval by one that has 0 in its interior, which divides nothing, as LLVM allocated
// the loop's registers differently around the calls of `div_ru_exported` in the other cases of
// `div_with`. And at `Baseline` it ran 1 more conditional branch per value of that polynomial with
// `mul_with` and `add_with`, whose loop LLVM did not rotate there (cachegrind, row 164).
impl sealed::Backend for Baseline {
    #[cfg(not(any(
        all(target_arch = "aarch64", not(inari_generic_backend), not(docsrs)),
        all(
            target_arch = "x86_64",
            not(inari_generic_backend),
            not(target_feature = "avx512f"),
            not(docsrs)
        )
    )))]
    fn add_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::add_ru(x, y)
    }

    // Where the `fma` or `sse42` backend is the build's, `#[inline(always)]`, so that a user's
    // crate calls the forwarder to `add_ru` that the crate exports without this method in
    // between (see above).
    #[cfg(all(
        target_arch = "x86_64",
        not(inari_generic_backend),
        not(target_feature = "avx512f"),
        not(docsrs)
    ))]
    #[inline(always)]
    fn add_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::add_ru_exported(x, y)
    }

    // Where the `aarch64` backend is the build's, `#[inline(always)]`, so that a user's crate calls
    // the copy of `add_ru` with the ABI `C` without this method in between (see above).
    #[cfg(all(target_arch = "aarch64", not(inari_generic_backend), not(docsrs)))]
    #[inline(always)]
    fn add_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::add_ru_c_abi(x, y)
    }

    #[cfg(not(all(target_arch = "x86_64", not(feature = "force-generic"), not(docsrs))))]
    #[inline(always)]
    fn classify_bits(self, x: &F64X2) -> u8 {
        crate::classify::classify_bits(x)
    }

    // Where the build's backend is one of `src/simd/x86_64.rs` (`sse42`, `fma` or `avx512f`), the
    // `classify_bits` of that file, which the copies of `V2`, `V3` and `V4` below call too. These
    // are the x86-64 builds without `inari_generic_backend` and `docsrs`: `build.rs` does not look
    // at `docsrs`, with which `src/simd.rs` takes `unimplemented.rs`. Where `fma` or `avx512f` is
    // the backend, the classification then puts no `vzeroupper` into the operations that classify
    // (see that function).
    #[cfg(all(target_arch = "x86_64", not(inari_generic_backend), not(docsrs)))]
    #[inline(always)]
    fn classify_bits(self, x: &F64X2) -> u8 {
        super::x86_64::classify_bits(*x)
    }

    // In the other x86-64 builds without `force-generic` and `docsrs`, those without `sse4.2`
    // (such as one for plain `x86-64`), whose backend is the portable one, the `classify_bits` of
    // `src/simd/x86_64.rs` too, which the copies of `V2`, `V3` and `V4` below call there as well.
    // It uses only SSE and SSE2 intrinsics, which every x86-64 CPU has, and `to_m128d` passes it
    // the `F64X2` of these builds, `[f64; 2]`, as an `__m128d`. In a crate that links inari,
    // built for `x86-64` in Cargo's default release profile, a call of `Interval::recip` or
    // `Interval::sqr` took 8 fewer instructions with it than with that of `src/classify.rs`, and
    // one of `Interval::mul`, `Interval::div`, `Interval::mul_add` or
    // `Interval::mul_rev_to_pair` 11 to 16 fewer, in the classes counted (cachegrind, row 152).
    //
    // `build.rs` sets `inari_generic_backend` on x86-64 exactly where `sse4.2` is missing or
    // `force-generic` is on, so the `cfg`s of this arm and the one above, which are disjoint,
    // together hold in exactly the x86-64 builds without `force-generic` and `docsrs`, and that
    // of the first arm is their complement: each build compiles one of the three.
    #[cfg(all(
        target_arch = "x86_64",
        inari_generic_backend,
        not(feature = "force-generic"),
        not(docsrs)
    ))]
    #[inline(always)]
    fn classify_bits(self, x: &F64X2) -> u8 {
        x86_64::classify_bits(to_m128d(*x))
    }

    #[cfg(not(any(
        all(inari_generic_backend, target_arch = "x86_64"),
        all(target_arch = "aarch64", not(inari_generic_backend), not(docsrs)),
        all(
            target_arch = "x86_64",
            not(inari_generic_backend),
            not(target_feature = "avx512f"),
            not(docsrs)
        )
    )))]
    fn div_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::div_ru(x, y)
    }

    // As `add_ru` above.
    #[cfg(all(
        target_arch = "x86_64",
        not(inari_generic_backend),
        not(target_feature = "avx512f"),
        not(docsrs)
    ))]
    #[inline(always)]
    fn div_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::div_ru_exported(x, y)
    }

    // As `add_ru` above.
    #[cfg(all(target_arch = "aarch64", not(inari_generic_backend), not(docsrs)))]
    #[inline(always)]
    fn div_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::div_ru_c_abi(x, y)
    }

    // `#[inline(always)]`, as is `mul_ru`: a user's crate then calls `div_ru_rust_abi` without
    // this method in between, and the crate exports `div_ru_rust_abi`, which an inline body
    // calls, so LLVM keeps its ABI however the crate is split into codegen units. Without the
    // attribute, where it shared this method's codegen unit (with one codegen unit, and with
    // rustc 1.98 in Cargo's default release profile in a build for `x86-64`), LLVM changed its
    // ABI and made this method an adapter of 10 instructions in place of a jump (row 146).
    #[cfg(all(inari_generic_backend, target_arch = "x86_64"))]
    #[inline(always)]
    fn div_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::generic::div_ru_rust_abi(x, y)
    }

    #[inline(always)]
    fn max(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::max(x, y)
    }

    #[cfg(not(any(
        all(inari_generic_backend, target_arch = "x86_64"),
        all(inari_sse42_backend, not(docsrs))
    )))]
    #[inline(always)]
    fn mul_add_ru(self, x: F64X2, y: F64X2, z: F64X2) -> F64X2 {
        crate::simd::mul_add_ru(x, y, z)
    }

    // Where the `sse42` backend is the build's, whose `mul_add_ru` is out of line, as `add_ru`
    // above. `build.rs` sets `inari_sse42_backend` where it is the backend, but does not look at
    // `docsrs`.
    #[cfg(all(inari_sse42_backend, not(docsrs)))]
    #[inline(always)]
    fn mul_add_ru(self, x: F64X2, y: F64X2, z: F64X2) -> F64X2 {
        crate::simd::mul_add_ru_exported(x, y, z)
    }

    // `#[inline(always)]`, as are `div_ru` and `mul_ru`: a user's crate then calls
    // `mul_add_ru_sysv64` without this method in between, and passes it the vectors in registers.
    // The crate's own `Interval::mul_add` passes `CrateBaseline`, which calls `mul_add_ru` (see
    // `mul_add_ru` of `CrateBaseline`).
    #[cfg(all(inari_generic_backend, target_arch = "x86_64"))]
    #[inline(always)]
    fn mul_add_ru(self, x: F64X2, y: F64X2, z: F64X2) -> F64X2 {
        crate::simd::generic::mul_add_ru_sysv64(x, y, z)
    }

    #[cfg(not(any(
        all(inari_generic_backend, target_arch = "x86_64"),
        all(target_arch = "aarch64", not(inari_generic_backend), not(docsrs)),
        all(
            target_arch = "x86_64",
            not(inari_generic_backend),
            not(target_feature = "avx512f"),
            not(docsrs)
        )
    )))]
    fn mul_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::mul_ru(x, y)
    }

    // As `add_ru` above.
    #[cfg(all(
        target_arch = "x86_64",
        not(inari_generic_backend),
        not(target_feature = "avx512f"),
        not(docsrs)
    ))]
    #[inline(always)]
    fn mul_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::mul_ru_exported(x, y)
    }

    // As `add_ru` above.
    #[cfg(all(target_arch = "aarch64", not(inari_generic_backend), not(docsrs)))]
    #[inline(always)]
    fn mul_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::mul_ru_c_abi(x, y)
    }

    // `#[inline(always)]`: see `div_ru`.
    #[cfg(all(inari_generic_backend, target_arch = "x86_64"))]
    #[inline(always)]
    fn mul_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::generic::mul_ru_rust_abi(x, y)
    }

    #[inline(always)]
    fn neg0(self, x: F64X2) -> F64X2 {
        crate::simd::neg0(x)
    }

    #[inline(always)]
    fn shuffle02(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::shuffle02(x, y)
    }

    #[inline(always)]
    fn shuffle03(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::shuffle03(x, y)
    }

    #[inline(always)]
    fn shuffle13(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::shuffle13(x, y)
    }

    #[inline(always)]
    fn splat(self, x: f64) -> F64X2 {
        crate::simd::splat(x)
    }

    #[inline(always)]
    fn sqrt_rd_ru(self, x: F64X2) -> F64X2 {
        crate::simd::sqrt_rd_ru(x)
    }

    #[inline(always)]
    fn sqrt1_ru(self, x: f64) -> f64 {
        crate::simd::sqrt1_ru(x)
    }

    #[inline(always)]
    fn swap(self, x: F64X2) -> F64X2 {
        crate::simd::swap(x)
    }
}

// The token of the operations of `Interval` without a token that call `add_ru`, `div_ru`,
// `mul_ru` or `mul_add_ru` (`Interval::{add, div, mul, mul_add, mul_rev_to_pair, recip, sqr,
// sub}`), in place of `Baseline`: its backend is that of `Baseline`. Where the portable backend is
// the build's on x86-64, it calls the `sysv64` `div_ru` and `mul_ru` of `src/simd/generic.rs`,
// which take the vectors in registers, where the methods of `Baseline` call their copies with
// Rust's ABI, and, the other way round, `mul_add_ru`, which takes Rust's ABI, where `Baseline`
// calls its copy `mul_add_ru_sysv64` with the ABI `sysv64` (see `mul_add_ru` below), and `add_ru`
// through `Baseline`. Only functions that a user's crate cannot inline or instantiate may use it,
// as otherwise the crate would export the `sysv64` functions, and its own operations would call
// them through the global offset table. Where the `aarch64` backend is the build's, it calls the
// `div_ru` and `mul_ru` of that backend, which take Rust's ABI, where the methods of `Baseline`
// call their copies with the ABI `C`, which the crate exports (see above), and `add_ru` and
// `mul_add_ru` through `Baseline`. Where the `fma` or `sse42` backend is the build's, it calls the
// `add_ru`, `div_ru`, `mul_ru` and `mul_add_ru` of that backend, which the crate does not export,
// where the methods of `Baseline` call the forwarders to them that it exports (see above), except
// that where `fma` is, `Baseline` calls `mul_add_ru` itself, which is `#[inline(always)]` there.
// Where `sse42` is, `mul_add_ru` is out of line, as before.
#[cfg(any(
    all(inari_generic_backend, target_arch = "x86_64"),
    all(target_arch = "aarch64", not(inari_generic_backend), not(docsrs)),
    all(
        target_arch = "x86_64",
        not(inari_generic_backend),
        not(target_feature = "avx512f"),
        not(docsrs)
    )
))]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct CrateBaseline;

#[cfg(not(any(
    all(inari_generic_backend, target_arch = "x86_64"),
    all(target_arch = "aarch64", not(inari_generic_backend), not(docsrs)),
    all(
        target_arch = "x86_64",
        not(inari_generic_backend),
        not(target_feature = "avx512f"),
        not(docsrs)
    )
)))]
pub(crate) use Baseline as CrateBaseline;

#[cfg(any(
    all(inari_generic_backend, target_arch = "x86_64"),
    all(target_arch = "aarch64", not(inari_generic_backend), not(docsrs)),
    all(
        target_arch = "x86_64",
        not(inari_generic_backend),
        not(target_feature = "avx512f"),
        not(docsrs)
    )
))]
impl Simd for CrateBaseline {
    #[inline(always)]
    fn vectorize<F: FnOnce() -> R, R>(self, f: F) -> R {
        f()
    }
}

#[cfg(any(
    all(inari_generic_backend, target_arch = "x86_64"),
    all(target_arch = "aarch64", not(inari_generic_backend), not(docsrs)),
    all(
        target_arch = "x86_64",
        not(inari_generic_backend),
        not(target_feature = "avx512f"),
        not(docsrs)
    )
))]
impl sealed::Backend for CrateBaseline {
    // The method of `Baseline` where the portable or the `aarch64` backend is the build's.
    #[cfg(not(all(target_arch = "x86_64", not(inari_generic_backend))))]
    #[inline(always)]
    fn add_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        sealed::Backend::add_ru(Baseline, x, y)
    }

    // No inline attribute, as for `div_ru`: the body of an `#[inline]` method would make the crate
    // export `add_ru`. Where the `fma` or `sse42` backend is the build's.
    #[cfg(all(target_arch = "x86_64", not(inari_generic_backend)))]
    fn add_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::add_ru(x, y)
    }

    #[inline(always)]
    fn classify_bits(self, x: &F64X2) -> u8 {
        sealed::Backend::classify_bits(Baseline, x)
    }

    // No inline attribute: rustc takes every method of a trait impl as reachable from other crates,
    // so the body of an `#[inline]` one would make the crate export the `sysv64` `div_ru`, and its
    // own operations would call it through the global offset table. Without the attribute, LLVM
    // still inlines this method into the crate's operations. This type exists where the portable
    // backend is the build's only on x86-64, so `inari_generic_backend` selects that build here.
    #[cfg(inari_generic_backend)]
    fn div_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::generic::div_ru(x, y)
    }

    // No inline attribute here either: the body of an `#[inline]` method would make the crate
    // export `div_ru`. Where the `aarch64`, `fma` or `sse42` backend is the build's.
    #[cfg(not(inari_generic_backend))]
    fn div_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::div_ru(x, y)
    }

    #[inline(always)]
    fn max(self, x: F64X2, y: F64X2) -> F64X2 {
        sealed::Backend::max(Baseline, x, y)
    }

    // `mul_add_ru`, which takes Rust's ABI, not its copy `mul_add_ru_sysv64`, which `Baseline`
    // calls. In a build for `x86-64`, with or without `force-generic`, `Interval::mul_add` inlines
    // `mul_add_ru` (seen with rustc 1.98), so no vectors pass between them. When it called a
    // `sysv64` `mul_add_ru` that was `#[inline(never)]`, it ran 3 to 32 more instructions per
    // call, in Cargo's default release profile and with one codegen unit. When it inlined a
    // `sysv64` `mul_add_ru`, it ran 1 more instruction per call for some classes of arguments and
    // 1 fewer for others in Cargo's default release profile, and had the same code as with
    // `mul_add_ru` with one codegen unit (cachegrind, row 154).
    #[cfg(inari_generic_backend)]
    #[inline(always)]
    fn mul_add_ru(self, x: F64X2, y: F64X2, z: F64X2) -> F64X2 {
        crate::simd::generic::mul_add_ru(x, y, z)
    }

    // Where the `fma` or `sse42` backend is the build's, its `mul_add_ru`, not the forwarder that
    // `Baseline` calls where `sse42` is. There this method has no inline attribute, as for
    // `div_ru`, and the crate's operations call `mul_add_ru` out of line, as they did before
    // `Baseline` called the forwarder. Where `fma` is, `mul_add_ru` is `#[inline(always)]`, and so
    // is this method.
    #[cfg(all(target_arch = "x86_64", not(inari_generic_backend)))]
    #[cfg_attr(not(inari_sse42_backend), inline(always))]
    fn mul_add_ru(self, x: F64X2, y: F64X2, z: F64X2) -> F64X2 {
        crate::simd::mul_add_ru(x, y, z)
    }

    // The method of `Baseline`, which calls the `mul_add_ru` of the `aarch64` backend.
    #[cfg(target_arch = "aarch64")]
    #[inline(always)]
    fn mul_add_ru(self, x: F64X2, y: F64X2, z: F64X2) -> F64X2 {
        sealed::Backend::mul_add_ru(Baseline, x, y, z)
    }

    // No inline attribute, as for `div_ru`.
    #[cfg(inari_generic_backend)]
    fn mul_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::generic::mul_ru(x, y)
    }

    // No inline attribute, as for `div_ru`.
    #[cfg(not(inari_generic_backend))]
    fn mul_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::mul_ru(x, y)
    }

    #[inline(always)]
    fn neg0(self, x: F64X2) -> F64X2 {
        sealed::Backend::neg0(Baseline, x)
    }

    #[inline(always)]
    fn shuffle02(self, x: F64X2, y: F64X2) -> F64X2 {
        sealed::Backend::shuffle02(Baseline, x, y)
    }

    #[inline(always)]
    fn shuffle03(self, x: F64X2, y: F64X2) -> F64X2 {
        sealed::Backend::shuffle03(Baseline, x, y)
    }

    #[inline(always)]
    fn shuffle13(self, x: F64X2, y: F64X2) -> F64X2 {
        sealed::Backend::shuffle13(Baseline, x, y)
    }

    #[inline(always)]
    fn splat(self, x: f64) -> F64X2 {
        sealed::Backend::splat(Baseline, x)
    }

    #[inline(always)]
    fn sqrt_rd_ru(self, x: F64X2) -> F64X2 {
        sealed::Backend::sqrt_rd_ru(Baseline, x)
    }

    #[inline(always)]
    fn sqrt1_ru(self, x: f64) -> f64 {
        sealed::Backend::sqrt1_ru(Baseline, x)
    }

    #[inline(always)]
    fn swap(self, x: F64X2) -> F64X2 {
        sealed::Backend::swap(Baseline, x)
    }
}

// A token whose backend is the build's, that of `Baseline`.
#[cfg(target_arch = "x86_64")]
#[allow(unused_macros)] // Unused in a plain `x86-64` build, where `V2`, `V3` and `V4` have copies.
macro_rules! baseline_backend {
    ($t:ty) => {
        impl sealed::Backend for $t {
            #[inline(always)]
            fn add_ru(self, x: F64X2, y: F64X2) -> F64X2 {
                sealed::Backend::add_ru(Baseline, x, y)
            }

            #[inline(always)]
            fn classify_bits(self, x: &F64X2) -> u8 {
                sealed::Backend::classify_bits(Baseline, x)
            }

            #[inline(always)]
            fn div_ru(self, x: F64X2, y: F64X2) -> F64X2 {
                sealed::Backend::div_ru(Baseline, x, y)
            }

            #[inline(always)]
            fn max(self, x: F64X2, y: F64X2) -> F64X2 {
                sealed::Backend::max(Baseline, x, y)
            }

            #[inline(always)]
            fn mul_add_ru(self, x: F64X2, y: F64X2, z: F64X2) -> F64X2 {
                sealed::Backend::mul_add_ru(Baseline, x, y, z)
            }

            #[inline(always)]
            fn mul_ru(self, x: F64X2, y: F64X2) -> F64X2 {
                sealed::Backend::mul_ru(Baseline, x, y)
            }

            #[inline(always)]
            fn neg0(self, x: F64X2) -> F64X2 {
                sealed::Backend::neg0(Baseline, x)
            }

            #[inline(always)]
            fn shuffle02(self, x: F64X2, y: F64X2) -> F64X2 {
                sealed::Backend::shuffle02(Baseline, x, y)
            }

            #[inline(always)]
            fn shuffle03(self, x: F64X2, y: F64X2) -> F64X2 {
                sealed::Backend::shuffle03(Baseline, x, y)
            }

            #[inline(always)]
            fn shuffle13(self, x: F64X2, y: F64X2) -> F64X2 {
                sealed::Backend::shuffle13(Baseline, x, y)
            }

            #[inline(always)]
            fn splat(self, x: f64) -> F64X2 {
                sealed::Backend::splat(Baseline, x)
            }

            #[inline(always)]
            fn sqrt_rd_ru(self, x: F64X2) -> F64X2 {
                sealed::Backend::sqrt_rd_ru(Baseline, x)
            }

            #[inline(always)]
            fn sqrt1_ru(self, x: f64) -> f64 {
                sealed::Backend::sqrt1_ru(Baseline, x)
            }

            #[inline(always)]
            fn swap(self, x: F64X2) -> F64X2 {
                sealed::Backend::swap(Baseline, x)
            }
        }
    };
}

// A token of an x86-64 level, with its `try_new` and `vectorize`, and its backend: copies of the
// functions of `$backend` (`src/simd/x86_64/`) in the builds `$copies`, and otherwise the
// build's. The list of target features is written once, so that the features that `try_new`
// detects are those that `vectorize` and the copies enable. Only string literals are passed as
// `$f`, but `is_x86_feature_detected!` matches them as tokens, which a `literal` is not. `$ad`
// are the attributes of the copies of `add_ru`, `div_ru` and `mul_ru`, and `$adabi` their ABI;
// `$ma` are the attributes of the copy of `mul_add_ru`, and `$abi` its ABI.
#[cfg(target_arch = "x86_64")]
macro_rules! level {
    // `sqrt1_ru copy`: the level has a copy of its backend's `sqrt1_ru`, which is out of line.
    // Inlined into the region of `sqrt_with`, the copy that `V3` has ran 4 to 6 fewer
    // instructions per call on an interval containing zero, but 1 to 5 more on a positive one,
    // whose path does not call it (cachegrind, row 136).
    (@sqrt1_ru_copy copy, $backend:ident, [$($f:tt),*]) => {
        $(#[target_feature(enable = $f)])*
        pub(super) fn sqrt1_ru(x: f64) -> f64 {
            $backend::sqrt1_ru(x)
        }
    };
    (@sqrt1_ru copy, $m:ident) => {
        #[inline(always)]
        fn sqrt1_ru(self, x: f64) -> f64 {
            // SAFETY: as in `vectorize`, for the target features of the copy.
            unsafe { $m::sqrt1_ru(x) }
        }
    };
    // `sqrt1_ru inline`: as `copy`, but the copy is inlined.
    (@sqrt1_ru_copy inline, $backend:ident, [$($f:tt),*]) => {
        #[inline]
        $(#[target_feature(enable = $f)])*
        pub(super) fn sqrt1_ru(x: f64) -> f64 {
            $backend::sqrt1_ru(x)
        }
    };
    (@sqrt1_ru inline, $m:ident) => {
        level!(@sqrt1_ru copy, $m);
    };
    // `sqrt1_ru baseline`: the level takes the `sqrt1_ru` of `Baseline`.
    (@sqrt1_ru_copy baseline, $backend:ident, [$($f:tt),*]) => {};
    (@sqrt1_ru baseline, $m:ident) => {
        #[inline(always)]
        fn sqrt1_ru(self, x: f64) -> f64 {
            sealed::Backend::sqrt1_ru(Baseline, x)
        }
    };
    (
        $(#[$attr:meta])*
        $t:ident, copies $m:ident in $copies:meta, backend $backend:ident, features [$($f:tt),*],
        add_ru div_ru mul_ru [$($ad:meta),*] extern $adabi:literal,
        mul_add_ru [$($ma:meta),*] extern $abi:literal, sqrt1_ru $sq:ident
    ) => {
        $(#[$attr])*
        #[derive(Clone, Copy, Debug)]
        pub struct $t {
            _private: (),
        }

        impl $t {
            #[doc = concat!(
                "Returns a token if the CPU has each target feature that [`", stringify!($t),
                "`] lists, and `None` otherwise."
            )]
            ///
            /// Each call checks the features (std caches what it detects), so call it outside
            /// a loop, and pass the token on.
            ///
            /// ```
            #[doc = concat!("use inari::{simd::{Simd, ", stringify!($t), "}, *};")]
            ///
            /// let x = const_interval!(1.0, 2.0);
            /// let y = const_interval!(-3.0, 0.5);
            #[doc = concat!("match ", stringify!($t), "::try_new() {")]
            ///     Some(s) => assert_eq!(s.vectorize(|| x.mul_with(s, y)), x * y),
            ///     None => println!("This CPU does not have the target features."),
            /// }
            /// ```
            #[must_use]
            pub fn try_new() -> Option<Self> {
                if $(is_x86_feature_detected!($f))&&* {
                    Some(Self { _private: () })
                } else {
                    None
                }
            }
        }

        impl Simd for $t {
            #[inline(always)]
            fn vectorize<F: FnOnce() -> R, R>(self, f: F) -> R {
                $(#[target_feature(enable = $f)])*
                #[inline]
                fn region<F: FnOnce() -> R, R>(f: F) -> R {
                    f()
                }

                // SAFETY: `self` exists only once `try_new` has detected every target feature
                // that `region` enables.
                unsafe { region(f) }
            }
        }

        // Each copy is out of line or inlined as the function it copies is in a build for the
        // level, whose backend is the level's (see `Baseline`). At `V2` and `V3`, `add_ru`,
        // `div_ru` and `mul_ru` are out of line, `sqrt_rd_ru` is inlined, and `mul_add_ru` is
        // inlined at `V3` and out of line at `V2`. The copy of `sqrt1_ru` that `V3` has is out
        // of line (see `@sqrt1_ru_copy`). At `V4`, every copy is inlined, as the functions of
        // `avx512f`, all of which but `sqrt_rd_ru` are one instruction, are in a build for
        // `x86-64-v4`: LLVM inlined each into its callers in the lib of that build, which has
        // none of them out of line (objdump, row 138). A function with `#[target_feature]`
        // cannot be `#[inline(always)]`, so the copies that are inlined are `#[inline]`.
        //
        // The copies of vector functions that are out of line take the ABI `sysv64`, which
        // passes their vectors in registers (see `Baseline`, which also explains `-unwind` and
        // the lint `improper_ctypes_definitions`), and those that are inlined Rust's ABI. So
        // the copies of `add_ru`, `div_ru` and `mul_ru` take `$adabi`, `sysv64` at `V2` and
        // `V3`, and Rust's ABI at `V4`, and the copy of `mul_add_ru` takes `$abi`, `sysv64` at
        // `V2`, and Rust's ABI at `V3` and `V4`. With `sysv64` at `V3`, a region that evaluated
        // a polynomial of degree 8 by Horner's rule with `mul_add_with` ran up to 19 more
        // instructions per polynomial (cachegrind, row 136).
        #[cfg($copies)]
        mod $m {
            use crate::simd::x86_64::$backend;
            use std::arch::x86_64::__m128d;

            #[allow(improper_ctypes_definitions)] // `__m128d` (see `Baseline`).
            $(#[$ad])*
            $(#[target_feature(enable = $f)])*
            pub(super) extern $adabi fn add_ru(x: __m128d, y: __m128d) -> __m128d {
                $backend::add_ru(x, y)
            }

            #[allow(improper_ctypes_definitions)] // `__m128d` (see `Baseline`).
            $(#[$ad])*
            $(#[target_feature(enable = $f)])*
            pub(super) extern $adabi fn div_ru(x: __m128d, y: __m128d) -> __m128d {
                $backend::div_ru(x, y)
            }

            #[allow(improper_ctypes_definitions)] // `__m128d` (see `Baseline`).
            $(#[$ma])*
            $(#[target_feature(enable = $f)])*
            pub(super) extern $abi fn mul_add_ru(
                x: __m128d,
                y: __m128d,
                z: __m128d,
            ) -> __m128d {
                $backend::mul_add_ru(x, y, z)
            }

            #[allow(improper_ctypes_definitions)] // `__m128d` (see `Baseline`).
            $(#[$ad])*
            $(#[target_feature(enable = $f)])*
            pub(super) extern $adabi fn mul_ru(x: __m128d, y: __m128d) -> __m128d {
                $backend::mul_ru(x, y)
            }

            #[inline]
            $(#[target_feature(enable = $f)])*
            pub(super) fn sqrt_rd_ru(x: __m128d) -> __m128d {
                $backend::sqrt_rd_ru(x)
            }

            level!(@sqrt1_ru_copy $sq, $backend, [$($f),*]);
        }

        // The copies take the place of the backend functions that are not thin layers (but the
        // `sqrt1_ru` of `V2`, see below), and the thin layers of `src/simd/x86_64.rs` (but
        // `splat`) those of the build. In a plain `x86-64` build, those of the build are the
        // portable backend's, except `classify_bits`: that of `Baseline` is the one of
        // `src/simd/x86_64.rs` there too (see `Baseline` above).
        #[cfg($copies)]
        impl sealed::Backend for $t {
            #[inline(always)]
            fn add_ru(self, x: F64X2, y: F64X2) -> F64X2 {
                // SAFETY: as in `vectorize`, for the target features of the copy.
                from_m128d(unsafe { $m::add_ru(to_m128d(x), to_m128d(y)) })
            }

            // The `classify_bits` of `src/simd/x86_64.rs`, as that of `Baseline` in every build
            // that has the copies.
            #[inline(always)]
            fn classify_bits(self, x: &F64X2) -> u8 {
                x86_64::classify_bits(to_m128d(*x))
            }

            #[inline(always)]
            fn div_ru(self, x: F64X2, y: F64X2) -> F64X2 {
                // SAFETY: as in `vectorize`, for the target features of the copy.
                from_m128d(unsafe { $m::div_ru(to_m128d(x), to_m128d(y)) })
            }

            #[inline(always)]
            fn max(self, x: F64X2, y: F64X2) -> F64X2 {
                from_m128d(x86_64::max(to_m128d(x), to_m128d(y)))
            }

            #[inline(always)]
            fn mul_add_ru(self, x: F64X2, y: F64X2, z: F64X2) -> F64X2 {
                // SAFETY: as in `vectorize`, for the target features of the copy.
                from_m128d(unsafe { $m::mul_add_ru(to_m128d(x), to_m128d(y), to_m128d(z)) })
            }

            #[inline(always)]
            fn mul_ru(self, x: F64X2, y: F64X2) -> F64X2 {
                // SAFETY: as in `vectorize`, for the target features of the copy.
                from_m128d(unsafe { $m::mul_ru(to_m128d(x), to_m128d(y)) })
            }

            #[inline(always)]
            fn neg0(self, x: F64X2) -> F64X2 {
                from_m128d(x86_64::neg0(to_m128d(x)))
            }

            #[inline(always)]
            fn shuffle02(self, x: F64X2, y: F64X2) -> F64X2 {
                from_m128d(x86_64::shuffle02(to_m128d(x), to_m128d(y)))
            }

            #[inline(always)]
            fn shuffle03(self, x: F64X2, y: F64X2) -> F64X2 {
                from_m128d(x86_64::shuffle03(to_m128d(x), to_m128d(y)))
            }

            #[inline(always)]
            fn shuffle13(self, x: F64X2, y: F64X2) -> F64X2 {
                from_m128d(x86_64::shuffle13(to_m128d(x), to_m128d(y)))
            }

            #[inline(always)]
            fn splat(self, x: f64) -> F64X2 {
                crate::simd::splat(x)
            }

            #[inline(always)]
            fn sqrt_rd_ru(self, x: F64X2) -> F64X2 {
                // SAFETY: as in `vectorize`, for the target features of the copy.
                from_m128d(unsafe { $m::sqrt_rd_ru(to_m128d(x)) })
            }

            // The scalar operations of `sse42` are those of the portable backend, so `V2` takes
            // the `sqrt1_ru` of `Baseline`, which in the builds of the copies is the portable
            // backend's without the FMA. `V3` has a copy of the `sqrt1_ru` that `fma` has in
            // those builds, a lane-wise form of the portable one, which the copy inlines with
            // the FMA. A copy calling the portable `sqrt1_ru_impl::<true>` did not use the FMA:
            // LLVM called that function out of line, in an instance compiled without `fma`
            // that calls the C library's `fma`. Marking `sqrt1_ru_impl` `#[inline(always)]`
            // inlined it into `Interval::sqrt` too, which `DecInterval::sqrt` then called out
            // of line, at up to 15 more instructions per call (cachegrind, row 123). `V4` has an
            // inlined copy of the `sqrt1_ru` of `avx512f`, one square root with embedded rounding.
            level!(@sqrt1_ru $sq, $m);

            #[inline(always)]
            fn swap(self, x: F64X2) -> F64X2 {
                from_m128d(x86_64::swap(to_m128d(x)))
            }
        }

        #[cfg(not($copies))]
        baseline_backend!($t);
    };
}

// The builds of the copies of `V4`, which include those of `V2` and `V3`.
#[cfg(all(
    target_arch = "x86_64",
    not(docsrs),
    not(feature = "force-generic"),
    not(target_feature = "avx512f"),
))]
use super::x86_64::{self, from_m128d, to_m128d};

#[cfg(target_arch = "x86_64")]
level! {
    /// The token of the target features `popcnt`, `sse3`, `sse4.1`, `sse4.2` and `ssse3`, which
    /// the level `x86-64-v2` of the x86-64 psABI has.
    ///
    /// [`V2::try_new`] returns one only if the CPU has each of these features, and the
    /// [`vectorize`](Simd::vectorize) of `V2` enables these features and no others. The level
    /// also has `cmpxchg16b` and LAHF-SAHF, which `V2` neither checks nor enables.
    ///
    /// Unless the feature `force-generic` is on, the `*_with` operations of
    /// [`Interval`](crate::Interval) and [`DecInterval`](crate::DecInterval) at `V2` run the
    /// `sse42` backend in a build without the target feature `sse4.2`, such as one for `x86-64`,
    /// the default of `x86_64-unknown-linux-gnu`. In other builds, and with `force-generic`, they
    /// run the build's backend, that of [`Baseline`].
    ///
    /// ```
    /// use inari::{simd::{Simd, V2}, *};
    ///
    /// let x = const_interval!(1.0, 2.0);
    /// let y = const_interval!(4.0, 8.0);
    /// if let Some(s) = V2::try_new() {
    ///     assert_eq!(s.vectorize(|| x.div_with(s, y)), const_interval!(0.125, 0.5));
    /// }
    /// ```
    V2,
    copies v2 in all(not(docsrs), not(feature = "force-generic"), not(target_feature = "sse4.2")),
    backend sse42,
    features ["popcnt", "sse3", "sse4.1", "sse4.2", "ssse3"],
    add_ru div_ru mul_ru [] extern "sysv64-unwind",
    mul_add_ru [] extern "sysv64-unwind",
    sqrt1_ru baseline
}

#[cfg(target_arch = "x86_64")]
level! {
    /// The token of the target features of [`V2`] and `avx`, `avx2`, `bmi1`, `bmi2`, `f16c`,
    /// `fma`, `lzcnt` and `movbe`, which the level `x86-64-v3` of the x86-64 psABI has.
    ///
    /// [`V3::try_new`] returns one only if the CPU has each of these features, and the
    /// [`vectorize`](Simd::vectorize) of `V3` enables these features and no others. The level
    /// also has `cmpxchg16b` and LAHF-SAHF, which `V3` neither checks nor enables, and OSXSAVE,
    /// which std checks as part of `avx`.
    ///
    /// Unless the feature `force-generic` is on, the `*_with` operations of
    /// [`Interval`](crate::Interval) and [`DecInterval`](crate::DecInterval) at `V3` run the `fma`
    /// backend in a build that has neither the target feature `avx512f` nor both `avx` and `fma`,
    /// such as one for `x86-64` or `x86-64-v2`. There, the parts that the `fma` backend takes from
    /// the portable backend, its slow paths, compute without the FMA, as those of the build's
    /// backend do. In other builds, such as one for `x86-64-v3` or `haswell`, and with
    /// `force-generic`, the operations run the build's backend, that of [`Baseline`].
    ///
    /// ```
    /// use inari::{simd::{Simd, V3}, *};
    ///
    /// let x = const_interval!(4.0, 9.0);
    /// if let Some(s) = V3::try_new() {
    ///     assert_eq!(s.vectorize(|| x.sqrt_with(s)), const_interval!(2.0, 3.0));
    /// }
    /// ```
    V3,
    copies v3 in all(
        not(docsrs),
        not(feature = "force-generic"),
        not(all(target_feature = "avx", target_feature = "fma")),
        not(target_feature = "avx512f")
    ),
    backend fma,
    features [
        "avx", "avx2", "bmi1", "bmi2", "f16c", "fma", "lzcnt", "movbe", "popcnt", "sse3",
        "sse4.1", "sse4.2", "ssse3"
    ],
    add_ru div_ru mul_ru [] extern "sysv64-unwind",
    mul_add_ru [inline] extern "Rust",
    sqrt1_ru copy
}

#[cfg(target_arch = "x86_64")]
level! {
    /// The token of the target features of [`V3`] and `avx512bw`, `avx512cd`, `avx512dq`,
    /// `avx512f` and `avx512vl`, which the level `x86-64-v4` of the x86-64 psABI has.
    ///
    /// [`V4::try_new`] returns one only if the CPU has each of these features, and the
    /// [`vectorize`](Simd::vectorize) of `V4` enables these features and no others. The level
    /// also has `cmpxchg16b` and LAHF-SAHF, which `V4` neither checks nor enables, and OSXSAVE,
    /// which std checks as part of `avx`.
    ///
    /// Unless the feature `force-generic` is on, the `*_with` operations of
    /// [`Interval`](crate::Interval) and [`DecInterval`](crate::DecInterval) at `V4` run the
    /// `avx512f` backend, which rounds with the embedded rounding of AVX-512, in a build without
    /// the target feature `avx512f`, such as one for `x86-64`, `x86-64-v2`, `x86-64-v3` or
    /// `haswell`. In other builds, such as one for `x86-64-v4`, and with `force-generic`, they run
    /// the build's backend, that of [`Baseline`].
    ///
    /// ```
    /// use inari::{simd::{Simd, V4}, *};
    ///
    /// let x = const_interval!(1.0, 2.0);
    /// let y = const_interval!(3.0, 4.0);
    /// let z = const_interval!(-1.0, 1.0);
    /// if let Some(s) = V4::try_new() {
    ///     assert_eq!(s.vectorize(|| x.mul_add_with(s, y, z)), const_interval!(2.0, 9.0));
    /// }
    /// ```
    V4,
    copies v4 in all(
        not(docsrs),
        not(feature = "force-generic"),
        not(target_feature = "avx512f")
    ),
    backend avx512f,
    features [
        "avx", "avx2", "avx512bw", "avx512cd", "avx512dq", "avx512f", "avx512vl", "bmi1", "bmi2",
        "f16c", "fma", "lzcnt", "movbe", "popcnt", "sse3", "sse4.1", "sse4.2", "ssse3"
    ],
    add_ru div_ru mul_ru [inline] extern "Rust",
    mul_add_ru [inline] extern "Rust",
    sqrt1_ru inline
}

#[cfg(test)]
mod tests;
