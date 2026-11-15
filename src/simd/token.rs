// The tokens of the levels of the CPU, and the backend that each one gives the `*_with`
// operations of `Interval` (`src/arith.rs` and `src/basic.rs`) in each build.
//
// A token of a level above `Baseline` exists only once its `try_new` has detected each target
// feature in its list, which is what makes it safe to call the functions compiled with those
// features: its `vectorize` region and its copies of the backend functions below. The list
// leaves out `cmpxchg16b` and LAHF-SAHF, features of the psABI levels that the source of the
// backends does not use, and OSXSAVE, which std checks as part of `avx`.
//
// The backend of a token is that of the build, unless the token's level is above the build's:
//
//   build                                     Baseline       V2              V3
//   docsrs, force-generic, avx512f,           the build's    the build's     the build's
//     avx + fma, other architectures
//   sse4.2 (x86-64-v2)                        sse42          sse42           fma (copies)
//   plain x86-64                              generic        sse42 (copies)  fma (copies)
//
// A copy is a function with the level's target features that calls the backend function, which
// is `#[inline(always)]` in such a build, so that the copy compiles it with those features. The
// thin layers of `src/simd/x86_64.rs` and its submodules are `#[inline(always)]` in every build,
// so that they take the target features of their caller.

use super::F64X2;
use std::fmt::Debug;

mod sealed {
    use crate::simd::F64X2;

    // The functions of the backend that the `*_with` operations of `Interval` call. Each method
    // computes what the function of the same name computes in the backend that the token gives
    // (the table above). `src/simd/generic.rs` says what its functions compute. The other
    // backends need not compute the same on every argument: where an argument is a NaN, or the
    // arguments are zeros of opposite signs, `max` of `src/simd/x86_64.rs` (`_mm_max_pd`) can
    // return another value than `max` of `src/simd/generic.rs`. A user can call the methods
    // through the bound `S: Simd`, but cannot name the trait.
    pub trait Backend {
        fn add_ru(self, x: F64X2, y: F64X2) -> F64X2;
        fn div_ru(self, x: F64X2, y: F64X2) -> F64X2;
        fn max(self, x: F64X2, y: F64X2) -> F64X2;
        fn mul_add_ru(self, x: F64X2, y: F64X2, z: F64X2) -> F64X2;
        fn mul_ru(self, x: F64X2, y: F64X2) -> F64X2;
        fn neg0(self, x: F64X2) -> F64X2;
        fn shuffle02(self, x: F64X2, y: F64X2) -> F64X2;
        fn shuffle03(self, x: F64X2, y: F64X2) -> F64X2;
        fn shuffle13(self, x: F64X2, y: F64X2) -> F64X2;
        fn splat(self, x: f64) -> F64X2;
        fn sqrt_rd_ru(self, x: F64X2) -> F64X2;
        fn sqrt1_ru(self, x: f64) -> f64;
        fn swap(self, x: F64X2) -> F64X2;
    }
}

/// A token of a level of the CPU: it gives the backend that the `*_with` operations of
/// [`Interval`](crate::Interval) run, such as [`Interval::add_with`](crate::Interval::add_with),
/// and the target features of its [`vectorize`](Simd::vectorize).
///
/// The tokens are [`Baseline`], on every target, and on x86-64 `V2` and `V3`, whose `try_new`
/// returns one only on a CPU that has their target features. Only inari implements `Simd`.
/// Every token gives the same intervals, since these operations return the tightest results
/// (see [Conformance to the standard](crate::_docs::conformance)); only the speed differs.
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
    /// The `*_with` operations of [`Interval`](crate::Interval) are `#[inline(always)]`, so
    /// they are inlined into their caller. Mark a closure that is more than a few operations
    /// `#[inline(always)]`, and the functions between it and the operations too. Code that is
    /// not inlined into the region computes the same intervals, but can be slower. For
    /// [`Baseline`], `vectorize` only calls `f`.
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
/// operations of [`Interval`](crate::Interval) without a token run (`x + y` is
/// `x.add_with(Baseline, y)`).
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

/// Runs `w` at the highest level of `V3`, `V2` and [`Baseline`] that the CPU has, inside that
/// level's [`vectorize`](Simd::vectorize), and returns what `w` returns.
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

// The build's backend, which the operations of `Interval` that take no token call through
// `Baseline` (`x + y` is `x.add_with(Baseline, y)`).
//
// A function that a user's crate can inline or instantiate, such as `add_with`, can call only
// functions that the crate exports, and Rust passes the vector arguments of an exported function
// in memory. Inside the crate, LLVM passes them in registers. So `add_ru`, `div_ru` and `mul_ru`,
// which the crate's operations call out of line (on aarch64 only `mul_ru`, see below), are called
// here from methods without `#[inline]`, which the crate exports in their place. LLVM inlines
// these small methods into the crate's operations, which then call the backend functions as
// before. The backend functions are `#[inline(never)]`, as otherwise LLVM would inline each into
// its only caller, the method. On aarch64 only `mul_ru` is: there LLVM inlines `add_ru` and
// `div_ru` into the methods and into the crate's operations, which then take fewer instructions
// (counted under QEMU), whereas inlining `mul_ru` gives `Interval::mul` a stack frame and more
// instructions. `mul_add_ru` and `sqrt_rd_ru` have one caller each in the crate's operations,
// which inlines them, and are `#[inline(always)]`, except `mul_add_ru` where `sse42` is the
// backend, which the crate calls out of line, as `add_ru`. (`src/__bench.rs`, compiled only with
// the feature `__bench`, for the benchmarks, also calls `mul_add_ru`.)
//
// The other functions that a `*_with` method reaches, and that rustc would not by itself inline
// into a user's crate on some target, are marked for it, apart from the backend functions that
// round upward or downward (`sqrt1_ru` as well as those above, and the copies of `V2` and `V3`
// below, of which those that a build for their level inlines are `#[inline]`) and the functions
// that they call: `add_rn`, `all`, `and`, `bitmask`, `eq`, `ge`, `gt`, `le`, `lt`, `max`, `or` and
// `sub_rn` on aarch64, with the helpers of `aarch64/lanewise.rs` and `aarch64/fma.rs` that
// `mul_add_ru` and `sqrt_rd_ru` call on their fast paths, and the thin layers of `wasm32.rs` that
// a `*_with` method reaches are `#[inline(always)]`, and `Interval::classify`, `classify2`,
// `inf_raw`, `sup_raw`, `with_infsup_raw`, `zero` and `is_empty` are `#[inline]`. So a `*_with`
// method instantiated in a user's crate calls out of line only functions that round upward or
// downward, and functions that they call.
impl sealed::Backend for Baseline {
    fn add_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::add_ru(x, y)
    }

    fn div_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::div_ru(x, y)
    }

    #[inline(always)]
    fn max(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::max(x, y)
    }

    #[cfg_attr(not(inari_sse42_backend), inline(always))]
    fn mul_add_ru(self, x: F64X2, y: F64X2, z: F64X2) -> F64X2 {
        crate::simd::mul_add_ru(x, y, z)
    }

    fn mul_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        crate::simd::mul_ru(x, y)
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

// A token whose backend is the build's, that of `Baseline`.
#[cfg(target_arch = "x86_64")]
#[allow(unused_macros)] // Unused in a plain `x86-64` build, where `V2` and `V3` have copies.
macro_rules! baseline_backend {
    ($t:ty) => {
        impl sealed::Backend for $t {
            #[inline(always)]
            fn add_ru(self, x: F64X2, y: F64X2) -> F64X2 {
                sealed::Backend::add_ru(Baseline, x, y)
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
// `$f`, but `is_x86_feature_detected!` matches them as tokens, which a `literal` is not. `$ma`
// are the attributes of the copy of `mul_add_ru`.
#[cfg(target_arch = "x86_64")]
macro_rules! level {
    (
        $(#[$attr:meta])*
        $t:ident, copies $m:ident in $copies:meta, backend $backend:ident, features [$($f:tt),*],
        mul_add_ru [$($ma:meta),*]
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
        // level, whose backend is the level's (see `Baseline`): `add_ru`, `div_ru` and `mul_ru`
        // are out of line, `sqrt_rd_ru` is inlined, and `mul_add_ru` is inlined at `V3` and out
        // of line at `V2`. A function with `#[target_feature]` cannot be `#[inline(always)]`,
        // so the copies that are inlined are `#[inline]`.
        #[cfg($copies)]
        mod $m {
            use crate::simd::x86_64::$backend;
            use std::arch::x86_64::__m128d;

            $(#[target_feature(enable = $f)])*
            pub(super) fn add_ru(x: __m128d, y: __m128d) -> __m128d {
                $backend::add_ru(x, y)
            }

            $(#[target_feature(enable = $f)])*
            pub(super) fn div_ru(x: __m128d, y: __m128d) -> __m128d {
                $backend::div_ru(x, y)
            }

            $(#[$ma])*
            $(#[target_feature(enable = $f)])*
            pub(super) fn mul_add_ru(x: __m128d, y: __m128d, z: __m128d) -> __m128d {
                $backend::mul_add_ru(x, y, z)
            }

            $(#[target_feature(enable = $f)])*
            pub(super) fn mul_ru(x: __m128d, y: __m128d) -> __m128d {
                $backend::mul_ru(x, y)
            }

            #[inline]
            $(#[target_feature(enable = $f)])*
            pub(super) fn sqrt_rd_ru(x: __m128d) -> __m128d {
                $backend::sqrt_rd_ru(x)
            }
        }

        // The copies take the place of the backend functions that are not thin layers, and the
        // thin layers of `src/simd/x86_64.rs` those of the build, which in a plain `x86-64`
        // build are the portable backend's.
        #[cfg($copies)]
        impl sealed::Backend for $t {
            #[inline(always)]
            fn add_ru(self, x: F64X2, y: F64X2) -> F64X2 {
                // SAFETY: as in `vectorize`, for the target features of the copy.
                from_m128d(unsafe { $m::add_ru(to_m128d(x), to_m128d(y)) })
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

            // The scalar operations of `sse42` and `fma` are those of the portable backend,
            // with the FMA under `fma`. Both levels take the `sqrt1_ru` of `Baseline`, which in
            // the builds of the copies is the portable backend's without the FMA. The copy that
            // `V3` had, which called `sqrt1_ru_impl::<true>`, did not use the FMA either: LLVM
            // called that function out of line, in an instance compiled without `fma` that
            // calls the C library's `fma`. Marking `sqrt1_ru_impl` `#[inline(always)]` inlined
            // it into `Interval::sqrt` too, which `DecInterval::sqrt` then called out of line,
            // at up to 15 more instructions per call (cachegrind, row 123).
            #[inline(always)]
            fn sqrt1_ru(self, x: f64) -> f64 {
                sealed::Backend::sqrt1_ru(Baseline, x)
            }

            #[inline(always)]
            fn swap(self, x: F64X2) -> F64X2 {
                from_m128d(x86_64::swap(to_m128d(x)))
            }
        }

        #[cfg(not($copies))]
        baseline_backend!($t);
    };
}

#[cfg(all(
    target_arch = "x86_64",
    not(docsrs),
    not(feature = "force-generic"),
    not(all(target_feature = "avx", target_feature = "fma")),
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
    /// [`Interval`](crate::Interval) at `V2` run the `sse42` backend in a build without the
    /// target feature `sse4.2`, such as one for `x86-64`, the default of
    /// `x86_64-unknown-linux-gnu`. In other builds, and with `force-generic`, they run the
    /// build's backend, that of [`Baseline`].
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
    mul_add_ru []
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
    /// [`Interval`](crate::Interval) at `V3` run the `fma` backend in a build that has neither
    /// the target feature `avx512f` nor both `avx` and `fma`, such as one for `x86-64` or
    /// `x86-64-v2`. There, the parts that the `fma` backend takes from the portable backend, its
    /// slow paths and the square root of the upper bound alone in
    /// [`Interval::sqrt_with`](crate::Interval::sqrt_with), compute without the FMA, as those of
    /// the build's backend do. In other builds, such as one for `x86-64-v3` or `haswell`, and
    /// with `force-generic`, the operations run the build's backend, that of [`Baseline`]. inari
    /// has no token of `x86-64-v4`: enabling the AVX-512 target features in a function needs
    /// Rust 1.89, and inari also builds with Rust 1.86.
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
    mul_add_ru [inline]
}

#[cfg(test)]
mod tests;
