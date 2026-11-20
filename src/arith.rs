use crate::{classify::*, interval::*, simd::*};
use forward_ref::*;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

impl Neg for Interval {
    type Output = Self;

    fn neg(self) -> Self {
        // Proved correct in `rocq/theories/Neg.v` for the portable backend.
        // `rocq/theories/Model.v` transcribes this function for that proof and those of
        // `(Dec)Interval::atan2` and `(Dec)Interval::cancel_plus`, so it has to be updated
        // along with it.
        // [-b, -a] = [b; -a]
        Self {
            rep: swap(self.rep),
        }
    }
}

forward_ref_unop!(impl Neg, neg for Interval);

impl Interval {
    /// Returns `self + rhs`, computed by the backend of `s` (see [`Simd`](crate::simd::Simd)).
    ///
    /// The result is the same interval as `self + rhs` for every `s`, as both are the tightest
    /// result ([Conformance to the standard](crate::_docs::conformance): "Unless otherwise noted,
    /// all operations return the tightest results").
    ///
    /// This method is `#[inline(always)]`, so that it gets the target features of the level of
    /// `s` where it is inlined into the function inside which
    /// [`s.vectorize`](crate::simd::Simd::vectorize) calls its closure: where it is called in the
    /// closure, and the closure is inlined into that function.
    ///
    /// # Examples
    ///
    /// ```
    /// use inari::{const_interval as c, simd::{Baseline, Simd}};
    /// let x = c!(1.0, 2.0);
    /// let y = c!(-3.0, 0.5);
    /// assert_eq!(Baseline.vectorize(|| x.add_with(Baseline, y)), x + y);
    /// #[cfg(target_arch = "x86_64")]
    /// {
    ///     if let Some(s) = inari::simd::V3::try_new() {
    ///         assert_eq!(s.vectorize(|| x.add_with(s, y)), x + y);
    ///     }
    /// }
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn add_with<S: Simd>(self, s: S, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/AddSub.v` for an `s` whose backend is the portable
        // one. `rocq/theories/Model.v` transcribes this function for such an `s`, so it has to
        // be updated along with it.
        // [a + c, b + d] = [-a - c; b + d] = [-a; b] .+ [-c; d]
        let x = self.rep; // [-a; b]
        let y = rhs.rep; // [-c; d]
        Self {
            rep: s.add_ru(x, y),
        }
    }
}

impl Add for Interval {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/AddSub.v` for the portable backend, as `add_with`
        // called with `CrateBaseline`, whose backend is that of `Baseline` (see `CrateBaseline`
        // in `src/simd/token.rs`). `rocq/theories/Model.v` transcribes this call, so it has to
        // be updated along with it.
        self.add_with(CrateBaseline, rhs)
    }
}

forward_ref_binop!(impl Add, add for Interval, Interval);

impl Interval {
    /// Returns `self - rhs`, computed by the backend of `s` (see [`Simd`](crate::simd::Simd)).
    ///
    /// The result is the same interval as `self - rhs` for every `s`, as both are the tightest
    /// result ([Conformance to the standard](crate::_docs::conformance): "Unless otherwise noted,
    /// all operations return the tightest results").
    ///
    /// This method is `#[inline(always)]`, so that it gets the target features of the level of
    /// `s` where it is inlined into the function inside which
    /// [`s.vectorize`](crate::simd::Simd::vectorize) calls its closure: where it is called in the
    /// closure, and the closure is inlined into that function.
    ///
    /// # Examples
    ///
    /// ```
    /// use inari::{const_interval as c, simd::{Baseline, Simd}};
    /// let x = c!(1.0, 2.0);
    /// let y = c!(-3.0, 0.5);
    /// assert_eq!(Baseline.vectorize(|| x.sub_with(Baseline, y)), x - y);
    /// #[cfg(target_arch = "x86_64")]
    /// {
    ///     if let Some(s) = inari::simd::V3::try_new() {
    ///         assert_eq!(s.vectorize(|| x.sub_with(s, y)), x - y);
    ///     }
    /// }
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn sub_with<S: Simd>(self, s: S, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/AddSub.v` for an `s` whose backend is the portable
        // one. `rocq/theories/Model.v` transcribes this function for such an `s`, so it has to
        // be updated along with it.
        // [a - d, b - c] = [-a + d; b - c] = [-a; b] .+ [d; -c]
        let x = self.rep; // [-a; b]
        let y = s.swap(rhs.rep); // [d; -c]
        Self {
            rep: s.add_ru(x, y),
        }
    }
}

impl Sub for Interval {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/AddSub.v` for the portable backend, as `sub_with`
        // called with `CrateBaseline`, whose backend is that of `Baseline` (see `CrateBaseline`
        // in `src/simd/token.rs`). `rocq/theories/Model.v` transcribes this call, so it has to
        // be updated along with it.
        self.sub_with(CrateBaseline, rhs)
    }
}

forward_ref_binop!(impl Sub, sub for Interval, Interval);

// The body of `Interval::mul_with`, with `$lhs` for `self`, `$s` for `s` and `$rhs` for `rhs`.
// `Mul::mul` expands it with `CrateBaseline` rather than calling `mul_with`. The body is too
// large for rustc's MIR inliner even with `#[inline(always)]` (seen with rustc 1.98), which only
// LLVM always follows, so the call would stay in the MIR of `mul`, and as it takes `self` and
// `rhs` by `move`, rustc would no longer mark the pointers through which `mul` takes them
// `readonly` and `captures(none)`.
// A caller that sees only the declaration of `mul`, such as `<DecInterval as Mul>::mul` in
// another codegen unit, would then copy both intervals to its stack before the call.
macro_rules! mul_with_body {
    ($lhs:expr, $s:expr, $rhs:expr) => {{
        let lhs: Interval = $lhs;
        let s = $s;
        let rhs: Interval = $rhs;
        // [a, b] * [c, d] =
        //
        //    |      M     |      N     |      P     |  Z
        // ---+------------+------------+------------+-----
        //  M |     *1     | [b*c, a*c] | [a*d, b*d] | {0}
        //  N | [a*d, a*c] | [b*d, a*c] | [a*d, b*c] | {0}
        //  P | [b*c, b*d] | [b*c, a*d] | [a*c, b*d] | {0}
        //  Z |     {0}    |     {0}    |     {0}    | {0}
        // *1 [min{a*d, b*c}, max{a*c, b*d}]

        use IntervalClass2::*;
        match lhs.classify2_with(s, rhs) {
            E_E | E_M | E_N0 | E_N1 | E_P0 | E_P1 | E_Z | M_E | N0_E | N1_E | P0_E | P1_E | Z_E => {
                Self::EMPTY
            }
            M_Z | N0_Z | N1_Z | P0_Z | P1_Z | Z_M | Z_N0 | Z_N1 | Z_P0 | Z_P1 | Z_Z => Self::zero(),
            M_M => {
                // M * M => [min(a*d, b*c), max(a*c, b*d)]
                //   = [-min(a*d, b*c); max(a*c, b*d)]
                //   = [max(-a*d, -b*c); max(a*c, b*d)]
                //   = [max(-a*d, b*-c); max(-a*-c, b*d)]
                //   = .max([-a*d; -a*-c], [b*-c; b*d])
                //   = .max([-a; -a] .* [d; -c], [b; b] .* [-c; d])
                let x = s.shuffle02(lhs.rep, lhs.rep); // [-a; -a]
                let y = s.swap(rhs.rep); // [d; -c]
                let xy = s.mul_ru(x, y);
                let z = s.shuffle13(lhs.rep, lhs.rep); // [b; b]
                let w = rhs.rep; // [-c; d]
                let zw = s.mul_ru(z, w);
                let r = s.max(xy, zw);
                Self { rep: r }
            }
            M_N0 | M_N1 => {
                // M * N => [b*c, a*c] = [-b*c; a*c] = [b*-c; -a*-c] = [b; -a] .* [-c; -c]
                let x = s.swap(lhs.rep); // [b; -a]
                let y = s.shuffle02(rhs.rep, rhs.rep); // [-c; -c]
                Self {
                    rep: s.mul_ru(x, y),
                }
            }
            M_P0 | M_P1 => {
                // M * P => [a*d, b*d] = [-a*d; b*d] = [-a; b] .* [d; d]
                let x = lhs.rep; // [-a; b]
                let y = s.shuffle13(rhs.rep, rhs.rep); // [d; d]
                Self {
                    rep: s.mul_ru(x, y),
                }
            }
            N0_M | N1_M => {
                // N * M => [a*d, a*c] = [-a*d; a*c] = [-a*d; -a*-c] = [-a; -a] .* [d; -c]
                let x = s.shuffle02(lhs.rep, lhs.rep); // [-a; -a]
                let y = s.swap(rhs.rep); // [d; -c]
                Self {
                    rep: s.mul_ru(x, y),
                }
            }
            N0_N0 | N0_N1 | N1_N0 | N1_N1 => {
                // N * N => [b*d, a*c] = [-b*d; a*c] = [-b*d; -a*-c] = [-b; -a] .* [d; -c]
                let x = s.swap(lhs.rep); // [b; -a]
                let x = s.neg0(x); // [-b; -a]
                let y = s.swap(rhs.rep); // [d; -c]
                Self {
                    rep: s.mul_ru(x, y),
                }
            }
            N0_P0 | N0_P1 | N1_P0 | N1_P1 => {
                // N * P => [a*d, b*c] = [-a*d; b*c] = [-a; b] .* [d; c]
                let x = lhs.rep; // [-a; b]
                let y = s.neg0(rhs.rep); // [c; d]
                let y = s.swap(y); // [d; c]
                Self {
                    rep: s.mul_ru(x, y),
                }
            }
            P0_M | P1_M => {
                // P * M => [b*c, b*d] = [-b*c; b*d] = [b*-c; b*d] = [b; b] .* [-c; d]
                let x = s.shuffle13(lhs.rep, lhs.rep); // [b; b]
                let y = rhs.rep; // [-c; d]
                Self {
                    rep: s.mul_ru(x, y),
                }
            }
            P0_N0 | P0_N1 | P1_N0 | P1_N1 => {
                // P * N => [b*c, a*d] = [-b*c; a*d] = [b*-c; a*d] = [b; a] .* [-c; d]
                let x = s.neg0(lhs.rep); // [a; b]
                let x = s.swap(x); // [b; a]
                let y = rhs.rep; // [-c; d]
                Self {
                    rep: s.mul_ru(x, y),
                }
            }
            P0_P0 | P0_P1 | P1_P0 | P1_P1 => {
                // P * P => [a*c, b*d] = [-a*c; b*d] = [-a; b] .* [c; d]
                let x = lhs.rep; // [-a; b]
                let y = s.neg0(rhs.rep); // [c; d]
                Self {
                    rep: s.mul_ru(x, y),
                }
            }
        }
    }};
}

// The methods of a token that `mul_with_body!` calls, for `Mul::mul`, which expands the macro with
// `CrateBaseline`. They are those of the sealed supertrait of `Simd`, which this module cannot
// name: `mul_with` calls them through its bound `S: Simd`, but on the type `CrateBaseline` only a
// trait in scope gives them. Each method calls the one of the same name through the bound
// `S: Simd`, as the bound comes first in method resolution.
trait TokenMethods {
    fn max(self, x: F64X2, y: F64X2) -> F64X2;
    fn mul_ru(self, x: F64X2, y: F64X2) -> F64X2;
    fn neg0(self, x: F64X2) -> F64X2;
    fn shuffle02(self, x: F64X2, y: F64X2) -> F64X2;
    fn shuffle13(self, x: F64X2, y: F64X2) -> F64X2;
    fn swap(self, x: F64X2) -> F64X2;
}

impl<S: Simd> TokenMethods for S {
    fn max(self, x: F64X2, y: F64X2) -> F64X2 {
        self.max(x, y)
    }

    fn mul_ru(self, x: F64X2, y: F64X2) -> F64X2 {
        self.mul_ru(x, y)
    }

    fn neg0(self, x: F64X2) -> F64X2 {
        self.neg0(x)
    }

    fn shuffle02(self, x: F64X2, y: F64X2) -> F64X2 {
        self.shuffle02(x, y)
    }

    fn shuffle13(self, x: F64X2, y: F64X2) -> F64X2 {
        self.shuffle13(x, y)
    }

    fn swap(self, x: F64X2) -> F64X2 {
        self.swap(x)
    }
}

impl Interval {
    /// Returns `self * rhs`, computed by the backend of `s` (see [`Simd`](crate::simd::Simd)).
    ///
    /// The result is the same interval as `self * rhs` for every `s`, as both are the tightest
    /// result ([Conformance to the standard](crate::_docs::conformance): "Unless otherwise noted,
    /// all operations return the tightest results").
    ///
    /// This method is `#[inline(always)]`, so that it gets the target features of the level of
    /// `s` where it is inlined into the function inside which
    /// [`s.vectorize`](crate::simd::Simd::vectorize) calls its closure: where it is called in the
    /// closure, and the closure is inlined into that function.
    ///
    /// # Examples
    ///
    /// ```
    /// use inari::{const_interval as c, simd::{Baseline, Simd}};
    /// let x = c!(1.0, 2.0);
    /// let y = c!(-3.0, 0.5);
    /// assert_eq!(Baseline.vectorize(|| x.mul_with(Baseline, y)), x * y);
    /// #[cfg(target_arch = "x86_64")]
    /// {
    ///     if let Some(s) = inari::simd::V3::try_new() {
    ///         assert_eq!(s.vectorize(|| x.mul_with(s, y)), x * y);
    ///     }
    /// }
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn mul_with<S: Simd>(self, s: S, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/Mul.v` for an `s` whose backend is the portable one
        // and whose `classify_bits` is that of `src/classify.rs`. `rocq/theories/Model.v`
        // transcribes this function for such an `s`, so it has to be updated along with it and
        // with `mul_with_body!`, which is its body.
        mul_with_body!(self, s, rhs)
    }
}

impl Mul for Interval {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/Mul.v` for the portable backend, as `mul_with`
        // called with `CrateBaseline`, whose backend is that of `Baseline` (see `CrateBaseline`
        // in `src/simd/token.rs`): this is the body of `mul_with`, `mul_with_body!`, with
        // `CrateBaseline` for `s` (see the comment on the macro). `rocq/theories/Model.v`
        // transcribes this, so it has to be updated along with it.
        mul_with_body!(self, CrateBaseline, rhs)
    }
}

forward_ref_binop!(impl Mul, mul for Interval, Interval);

impl Interval {
    /// Returns `self / rhs`, computed by the backend of `s` (see [`Simd`](crate::simd::Simd)).
    ///
    /// The result is the same interval as `self / rhs` for every `s`, as both are the tightest
    /// result ([Conformance to the standard](crate::_docs::conformance): "Unless otherwise noted,
    /// all operations return the tightest results").
    ///
    /// This method is `#[inline(always)]`, so that it gets the target features of the level of
    /// `s` where it is inlined into the function inside which
    /// [`s.vectorize`](crate::simd::Simd::vectorize) calls its closure: where it is called in the
    /// closure, and the closure is inlined into that function.
    ///
    /// # Examples
    ///
    /// ```
    /// use inari::{const_interval as c, simd::{Baseline, Simd}};
    /// let x = c!(1.0, 2.0);
    /// let y = c!(3.0, 4.0);
    /// assert_eq!(Baseline.vectorize(|| x.div_with(Baseline, y)), x / y);
    /// #[cfg(target_arch = "x86_64")]
    /// {
    ///     if let Some(s) = inari::simd::V3::try_new() {
    ///         assert_eq!(s.vectorize(|| x.div_with(s, y)), x / y);
    ///     }
    /// }
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn div_with<S: Simd>(self, s: S, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/Div.v` for an `s` whose backend is the portable one
        // and whose `classify_bits` is that of `src/classify.rs`. `rocq/theories/Model.v`
        // transcribes this function for such an `s`, so it has to be updated along with it.
        // [a, b] / [c, d] =
        //
        //    |  M  |     N0    |     N1     |     P0    |     P1     | Z
        // ---+-----+-----------+------------+-----------+------------+---
        //  M |  ℝ  |     ℝ     | [b/d, a/d] |     ℝ     | [a/c, b/c] | ∅
        //  N |  ℝ  | [b/c, +∞] | [b/c, a/d] | [-∞, b/d] | [a/c, b/d] | ∅
        //  P |  ℝ  | [-∞, a/c] | [b/d, a/c] | [a/d, +∞] | [a/d, b/c] | ∅
        //  Z | {0} |    {0}    |     {0}    |    {0}    |     {0}    | ∅

        use IntervalClass2::*;
        match self.classify2_with(s, rhs) {
            E_E | E_M | E_N0 | E_N1 | E_P0 | E_P1 | E_Z | M_E | M_Z | N0_E | N0_Z | N1_E | N1_Z
            | P0_E | P0_Z | P1_E | P1_Z | Z_E | Z_Z => Self::EMPTY,
            M_M | M_N0 | M_P0 | N0_M | N1_M | P0_M | P1_M => Self::ENTIRE,
            Z_M | Z_N0 | Z_N1 | Z_P0 | Z_P1 => Self::zero(),
            M_N1 => self.div_m_n1(s, rhs),
            M_P1 => self.div_m_p1(s, rhs),
            N0_N0 | N1_N0 => self.div_n_n0(s, rhs),
            N0_N1 | N1_N1 => self.div_n_n1(s, rhs),
            N0_P0 | N1_P0 => self.div_n_p0(s, rhs),
            N0_P1 | N1_P1 => self.div_n_p1(s, rhs),
            P0_N0 | P1_N0 => self.div_p_n0(s, rhs),
            P0_N1 | P1_N1 => self.div_p_n1(s, rhs),
            P0_P0 | P1_P0 => self.div_p_p0(s, rhs),
            P0_P1 | P1_P1 => self.div_p_p1(s, rhs),
        }
    }
}

impl Div for Interval {
    type Output = Self;

    fn div(self, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/Div.v` for the portable backend, as `div_with`
        // called with `CrateBaseline`, whose backend is that of `Baseline` (see `CrateBaseline`
        // in `src/simd/token.rs`). `rocq/theories/Model.v` transcribes this call, so it has to
        // be updated along with it.
        self.div_with(CrateBaseline, rhs)
    }
}

forward_ref_binop!(impl Div, div for Interval, Interval);

impl Neg for DecInterval {
    type Output = Self;

    fn neg(self) -> Self {
        // Proved correct in `rocq/theories/Neg.v` for the portable backend.
        // `rocq/theories/Model.v` transcribes this function, so it has to be updated
        // along with it.
        if self.is_nai() {
            return self;
        }

        Self::set_dec(-self.x(), self.d())
    }
}

forward_ref_unop!(impl Neg, neg for DecInterval);

// The body of `DecInterval::add_with`, `DecInterval::sub_with` and `DecInterval::mul_with`, with
// `$lhs` for `self`, `$rhs` for `rhs`, `$x` for the interval of the result, which it evaluates
// only if neither `$lhs` nor `$rhs` is NaI, and `$set_dec` for the function that decorates it.
// The methods expand it with their call of `Interval`'s method, such as
// `self.x().add_with(s, rhs.x())`, and with `Self::set_dec_impl`, which is `#[inline]`.
// `Add::add`, `Sub::sub` and `Mul::mul` expand it with `Interval`'s operator, such as
// `self.x() + rhs.x()`, and with `Self::set_dec`, which is not, rather than calling the methods
// with `Baseline`. With those calls, `+` and `-` took 7 and 4 more instructions per call in a
// plain x86-64 build of the library. With every operation of `DecInterval` without a token
// calling its `*_with` method with `Baseline`, `<Interval as Mul>::mul` and
// `<Interval as Div>::div`, whose source is the same either way, took up to 2 and 4 more (seen
// with rustc 1.98).
macro_rules! dec_add_sub_mul_with_body {
    ($lhs:ident, $rhs:ident, $x:expr, $set_dec:path) => {{
        if $lhs.is_nai() || $rhs.is_nai() {
            return Self::NAI;
        }

        $set_dec($x, $lhs.d().min($rhs.d()))
    }};
}

// The body of `DecInterval::div_with`, with `$lhs`, `$rhs`, `$x` and `$set_dec` as in
// `dec_add_sub_mul_with_body!`. `Div::div` expands it with `self.x() / rhs.x()` and with
// `Self::set_dec` for the reasons given there.
macro_rules! dec_div_with_body {
    ($lhs:ident, $rhs:ident, $x:expr, $set_dec:path) => {{
        if $lhs.is_nai() || $rhs.is_nai() {
            return Self::NAI;
        }

        let d = if $rhs.x().contains(0.0) {
            Decoration::Trv
        } else {
            $lhs.d().min($rhs.d())
        };
        $set_dec($x, d)
    }};
}

impl DecInterval {
    /// The decorated version of [`Interval::add_with`].
    ///
    /// A NaI is returned if `self` or `rhs` is NaI.
    ///
    /// The result has the same `interval()` and `decoration()` as `self + rhs` for every `s`, as
    /// the interval that [`Interval::add_with`] returns is the same for every `s`, and the
    /// decoration depends only on `self`, `rhs` and that interval.
    ///
    /// This method is `#[inline(always)]`, so that it gets the target features of the level of
    /// `s` where it is inlined into the function inside which
    /// [`s.vectorize`](crate::simd::Simd::vectorize) calls its closure: where it is called in the
    /// closure, and the closure is inlined into that function.
    ///
    /// # Examples
    ///
    /// ```
    /// use inari::{const_dec_interval as c, simd::{Baseline, Simd}};
    /// let x = c!(1.0, 2.0);
    /// let y = c!(-3.0, 0.5);
    /// let z = x + y;
    /// let r = Baseline.vectorize(|| x.add_with(Baseline, y));
    /// assert_eq!((r.interval(), r.decoration()), (z.interval(), z.decoration()));
    /// #[cfg(target_arch = "x86_64")]
    /// {
    ///     if let Some(s) = inari::simd::V3::try_new() {
    ///         let r = s.vectorize(|| x.add_with(s, y));
    ///         assert_eq!((r.interval(), r.decoration()), (z.interval(), z.decoration()));
    ///     }
    /// }
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn add_with<S: Simd>(self, s: S, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/AddSub.v` for an `s` whose backend is the portable
        // one. `rocq/theories/Model.v` transcribes this function for such an `s`, so it has to
        // be updated along with it and with `dec_add_sub_mul_with_body!`, which is its body.
        dec_add_sub_mul_with_body!(self, rhs, self.x().add_with(s, rhs.x()), Self::set_dec_impl)
    }
}

impl Add for DecInterval {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/AddSub.v` for the portable backend, as `add_with`
        // called with `CrateBaseline`, whose backend is that of `Baseline` (see `CrateBaseline`
        // in `src/simd/token.rs`): this is the body of `add_with`, `dec_add_sub_mul_with_body!`,
        // with `self.x() + rhs.x()`, which is `self.x().add_with(CrateBaseline, rhs.x())`, for
        // the interval, and with `Self::set_dec`, which calls `Self::set_dec_impl` (see the
        // comment on the macro). `rocq/theories/Model.v` transcribes this, so it has to be
        // updated along with it.
        dec_add_sub_mul_with_body!(self, rhs, self.x() + rhs.x(), Self::set_dec)
    }
}

forward_ref_binop!(impl Add, add for DecInterval, DecInterval);

impl DecInterval {
    /// The decorated version of [`Interval::sub_with`].
    ///
    /// A NaI is returned if `self` or `rhs` is NaI.
    ///
    /// The result has the same `interval()` and `decoration()` as `self - rhs` for every `s`, as
    /// the interval that [`Interval::sub_with`] returns is the same for every `s`, and the
    /// decoration depends only on `self`, `rhs` and that interval.
    ///
    /// This method is `#[inline(always)]`, so that it gets the target features of the level of
    /// `s` where it is inlined into the function inside which
    /// [`s.vectorize`](crate::simd::Simd::vectorize) calls its closure: where it is called in the
    /// closure, and the closure is inlined into that function.
    ///
    /// # Examples
    ///
    /// ```
    /// use inari::{const_dec_interval as c, simd::{Baseline, Simd}};
    /// let x = c!(1.0, 2.0);
    /// let y = c!(-3.0, 0.5);
    /// let z = x - y;
    /// let r = Baseline.vectorize(|| x.sub_with(Baseline, y));
    /// assert_eq!((r.interval(), r.decoration()), (z.interval(), z.decoration()));
    /// #[cfg(target_arch = "x86_64")]
    /// {
    ///     if let Some(s) = inari::simd::V3::try_new() {
    ///         let r = s.vectorize(|| x.sub_with(s, y));
    ///         assert_eq!((r.interval(), r.decoration()), (z.interval(), z.decoration()));
    ///     }
    /// }
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn sub_with<S: Simd>(self, s: S, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/AddSub.v` for an `s` whose backend is the portable
        // one. `rocq/theories/Model.v` transcribes this function for such an `s`, so it has to
        // be updated along with it and with `dec_add_sub_mul_with_body!`, which is its body.
        dec_add_sub_mul_with_body!(self, rhs, self.x().sub_with(s, rhs.x()), Self::set_dec_impl)
    }
}

impl Sub for DecInterval {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/AddSub.v` for the portable backend, as `sub_with`
        // called with `CrateBaseline`, whose backend is that of `Baseline` (see `CrateBaseline`
        // in `src/simd/token.rs`): this is the body of `sub_with`, `dec_add_sub_mul_with_body!`,
        // with `self.x() - rhs.x()`, which is `self.x().sub_with(CrateBaseline, rhs.x())`, for
        // the interval, and with `Self::set_dec`, which calls `Self::set_dec_impl` (see the
        // comment on the macro). `rocq/theories/Model.v` transcribes this, so it has to be
        // updated along with it.
        dec_add_sub_mul_with_body!(self, rhs, self.x() - rhs.x(), Self::set_dec)
    }
}

forward_ref_binop!(impl Sub, sub for DecInterval, DecInterval);

impl DecInterval {
    /// The decorated version of [`Interval::mul_with`].
    ///
    /// A NaI is returned if `self` or `rhs` is NaI.
    ///
    /// The result has the same `interval()` and `decoration()` as `self * rhs` for every `s`, as
    /// the interval that [`Interval::mul_with`] returns is the same for every `s`, and the
    /// decoration depends only on `self`, `rhs` and that interval.
    ///
    /// This method is `#[inline(always)]`, so that it gets the target features of the level of
    /// `s` where it is inlined into the function inside which
    /// [`s.vectorize`](crate::simd::Simd::vectorize) calls its closure: where it is called in the
    /// closure, and the closure is inlined into that function.
    ///
    /// # Examples
    ///
    /// ```
    /// use inari::{const_dec_interval as c, simd::{Baseline, Simd}};
    /// let x = c!(1.0, 2.0);
    /// let y = c!(-3.0, 0.5);
    /// let z = x * y;
    /// let r = Baseline.vectorize(|| x.mul_with(Baseline, y));
    /// assert_eq!((r.interval(), r.decoration()), (z.interval(), z.decoration()));
    /// #[cfg(target_arch = "x86_64")]
    /// {
    ///     if let Some(s) = inari::simd::V3::try_new() {
    ///         let r = s.vectorize(|| x.mul_with(s, y));
    ///         assert_eq!((r.interval(), r.decoration()), (z.interval(), z.decoration()));
    ///     }
    /// }
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn mul_with<S: Simd>(self, s: S, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/Mul.v` for an `s` whose backend is the portable one
        // and whose `classify_bits` is that of `src/classify.rs`, if `self` and `rhs` are `com`
        // only when `self.x()` and `rhs.x()` are common, which
        // `rocq/theories/ComCommon.v` proves of every `DecInterval` that the library makes.
        // `rocq/theories/Model.v` transcribes this function for such an `s`, so it has to be
        // updated along with it and with `dec_add_sub_mul_with_body!`, which is its body.
        dec_add_sub_mul_with_body!(self, rhs, self.x().mul_with(s, rhs.x()), Self::set_dec_impl)
    }
}

impl Mul for DecInterval {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/Mul.v` for the portable backend, as `mul_with`
        // called with `CrateBaseline`, whose backend is that of `Baseline` (see `CrateBaseline`
        // in `src/simd/token.rs`), if `self` and `rhs` are `com` only when `self.x()` and
        // `rhs.x()` are common, which `rocq/theories/ComCommon.v` proves of every
        // `DecInterval` that the library makes: this is the body of `mul_with`,
        // `dec_add_sub_mul_with_body!`, with `self.x() * rhs.x()`, which is the body of
        // `Interval::mul_with` with `CrateBaseline` for `s`, for the interval, and with
        // `Self::set_dec`, which calls `Self::set_dec_impl` (see the comment on the macro).
        // `rocq/theories/Model.v` transcribes this, so it has to be updated along with it.
        dec_add_sub_mul_with_body!(self, rhs, self.x() * rhs.x(), Self::set_dec)
    }
}

forward_ref_binop!(impl Mul, mul for DecInterval, DecInterval);

impl DecInterval {
    /// The decorated version of [`Interval::div_with`].
    ///
    /// A NaI is returned if `self` or `rhs` is NaI.
    ///
    /// The result has the same `interval()` and `decoration()` as `self / rhs` for every `s`, as
    /// the interval that [`Interval::div_with`] returns is the same for every `s`, and the
    /// decoration depends only on `self`, `rhs` and that interval.
    ///
    /// This method is `#[inline(always)]`, so that it gets the target features of the level of
    /// `s` where it is inlined into the function inside which
    /// [`s.vectorize`](crate::simd::Simd::vectorize) calls its closure: where it is called in the
    /// closure, and the closure is inlined into that function.
    ///
    /// # Examples
    ///
    /// ```
    /// use inari::{const_dec_interval as c, simd::{Baseline, Simd}};
    /// let x = c!(1.0, 2.0);
    /// let y = c!(3.0, 4.0);
    /// let z = x / y;
    /// let r = Baseline.vectorize(|| x.div_with(Baseline, y));
    /// assert_eq!((r.interval(), r.decoration()), (z.interval(), z.decoration()));
    /// #[cfg(target_arch = "x86_64")]
    /// {
    ///     if let Some(s) = inari::simd::V3::try_new() {
    ///         let r = s.vectorize(|| x.div_with(s, y));
    ///         assert_eq!((r.interval(), r.decoration()), (z.interval(), z.decoration()));
    ///     }
    /// }
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn div_with<S: Simd>(self, s: S, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/Div.v` for an `s` whose backend is the portable one
        // and whose `classify_bits` is that of `src/classify.rs`, if `self` and `rhs` are `com`
        // only when `self.x()` and `rhs.x()` are common, which
        // `rocq/theories/ComCommon.v` proves of every `DecInterval` that the library makes.
        // `rocq/theories/Model.v` transcribes this function for such an `s`, so it has to be
        // updated along with it and with `dec_div_with_body!`, which is its body.
        dec_div_with_body!(self, rhs, self.x().div_with(s, rhs.x()), Self::set_dec_impl)
    }
}

impl Div for DecInterval {
    type Output = Self;

    fn div(self, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/Div.v` for the portable backend, as `div_with`
        // called with `CrateBaseline`, whose backend is that of `Baseline` (see `CrateBaseline`
        // in `src/simd/token.rs`), if `self` and `rhs` are `com` only when `self.x()` and
        // `rhs.x()` are common, which `rocq/theories/ComCommon.v` proves of every
        // `DecInterval` that the library makes: this is the body of `div_with`,
        // `dec_div_with_body!`, with `self.x() / rhs.x()`, which is
        // `self.x().div_with(CrateBaseline, rhs.x())`, for the interval, and with
        // `Self::set_dec`, which calls `Self::set_dec_impl` (see the comment on the macro).
        // `rocq/theories/Model.v` transcribes this, so it has to be updated along with it.
        dec_div_with_body!(self, rhs, self.x() / rhs.x(), Self::set_dec)
    }
}

forward_ref_binop!(impl Div, div for DecInterval, DecInterval);

macro_rules! impl_op_assign {
    ($OpAssign:ident, $op_assign:ident, $op:ident) => {
        impl $OpAssign for Interval {
            fn $op_assign(&mut self, rhs: Self) {
                *self = self.$op(rhs);
            }
        }

        forward_ref_op_assign!(impl $OpAssign, $op_assign for Interval,
                               Interval);

        impl $OpAssign for DecInterval {
            fn $op_assign(&mut self, rhs: Self) {
                *self = self.$op(rhs);
            }
        }

        forward_ref_op_assign!(impl $OpAssign, $op_assign for DecInterval,
                               DecInterval);
    };
}

impl_op_assign!(AddAssign, add_assign, add);
impl_op_assign!(SubAssign, sub_assign, sub);
impl_op_assign!(MulAssign, mul_assign, mul);
impl_op_assign!(DivAssign, div_assign, div);

#[cfg(test)]
mod tests {
    use crate::*;
    use DecInterval as DI;
    use Interval as I;

    #[test]
    fn add_assign() {
        let mut i = const_interval!(3.0, 4.0);
        i += const_interval!(1.0, 2.0);
        assert_eq!(i, const_interval!(4.0, 6.0));

        let mut i = const_dec_interval!(3.0, 4.0);
        i += const_dec_interval!(1.0, 2.0);
        assert_eq!(i, const_dec_interval!(4.0, 6.0));
    }

    #[test]
    fn sub_assign() {
        let mut i = const_interval!(3.0, 4.0);
        i -= const_interval!(1.0, 2.0);
        assert_eq!(i, const_interval!(1.0, 3.0));

        let mut i = const_dec_interval!(3.0, 4.0);
        i -= const_dec_interval!(1.0, 2.0);
        assert_eq!(i, const_dec_interval!(1.0, 3.0));
    }

    #[test]
    fn mul_assign() {
        let mut i = const_interval!(3.0, 4.0);
        i *= const_interval!(1.0, 2.0);
        assert_eq!(i, const_interval!(3.0, 8.0));

        let mut i = const_dec_interval!(3.0, 4.0);
        i *= const_dec_interval!(1.0, 2.0);
        assert_eq!(i, const_dec_interval!(3.0, 8.0));
    }

    #[test]
    fn div_assign() {
        let mut i = const_interval!(3.0, 4.0);
        i /= const_interval!(1.0, 2.0);
        assert_eq!(i, const_interval!(1.5, 4.0));

        let mut i = const_dec_interval!(3.0, 4.0);
        i /= const_dec_interval!(1.0, 2.0);
        assert_eq!(i, const_dec_interval!(1.5, 4.0));
    }

    #[test]
    fn empty() {
        assert!((-I::EMPTY).is_empty());

        assert!((I::EMPTY + I::PI).is_empty());
        assert!((I::PI + I::EMPTY).is_empty());

        assert!((I::EMPTY - I::PI).is_empty());
        assert!((I::PI - I::EMPTY).is_empty());

        assert!((I::EMPTY * I::PI).is_empty());
        assert!((I::PI * I::EMPTY).is_empty());

        assert!((I::EMPTY / I::PI).is_empty());
        assert!((I::PI / I::EMPTY).is_empty());

        assert!((-DI::EMPTY).is_empty());

        assert!((DI::EMPTY + DI::PI).is_empty());
        assert!((DI::PI + DI::EMPTY).is_empty());

        assert!((DI::EMPTY - DI::PI).is_empty());
        assert!((DI::PI - DI::EMPTY).is_empty());

        assert!((DI::EMPTY * DI::PI).is_empty());
        assert!((DI::PI * DI::EMPTY).is_empty());

        assert!((DI::EMPTY / DI::PI).is_empty());
        assert!((DI::PI / DI::EMPTY).is_empty());
    }

    #[test]
    fn nai() {
        assert!((-DI::NAI).is_nai());

        assert!((DI::NAI + DI::PI).is_nai());
        assert!((DI::PI + DI::NAI).is_nai());

        assert!((DI::NAI - DI::PI).is_nai());
        assert!((DI::PI - DI::NAI).is_nai());

        assert!((DI::NAI * DI::PI).is_nai());
        assert!((DI::PI * DI::NAI).is_nai());

        assert!((DI::NAI / DI::PI).is_nai());
        assert!((DI::PI / DI::NAI).is_nai());
    }

    #[allow(clippy::op_ref)]
    #[test]
    fn ref_type_args() {
        const E: I = I::EMPTY;
        const DE: DI = DI::EMPTY;

        let _ = -&E;

        let _ = &E + E;
        let _ = E + &E;
        let _ = &E + &E;

        let _ = &E - E;
        let _ = E - &E;
        let _ = &E - &E;

        let _ = &E * E;
        let _ = E * &E;
        let _ = &E * &E;

        let _ = &E / E;
        let _ = E / &E;
        let _ = &E / &E;

        let _ = -&DE;

        let _ = &DE + DE;
        let _ = DE + &DE;
        let _ = &DE + &DE;

        let _ = &DE - DE;
        let _ = DE - &DE;
        let _ = &DE - &DE;

        let _ = &DE * DE;
        let _ = DE * &DE;
        let _ = &DE * &DE;

        let _ = &DE / DE;
        let _ = DE / &DE;
        let _ = &DE / &DE;

        let mut e = I::EMPTY;
        e += &E;
        e -= &E;
        e *= &E;
        e /= &E;

        let mut de = DI::EMPTY;
        de += &DE;
        de -= &DE;
        de *= &DE;
        de /= &DE;
    }
}
