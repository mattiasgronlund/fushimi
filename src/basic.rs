use crate::{classify::*, interval::*, simd::*};
use std::{cmp::Ordering, unreachable};

// NOTE: `neg`, `add`, `sub`, `mul` and `div` are implemented in arith.rs

impl Interval {
    // Division functions [a, b] / [c, d] for various cases, shared
    // between `mul_rev_to_pair` (below) and `Div` (in arith.rs).
    #[inline(always)]
    pub(crate) fn div_m_n1<S: Simd>(self, s: S, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for an `s` whose backend is the
        // portable one, for the proofs of `(Dec)Interval::div` and
        // `(Dec)Interval::mul_rev_to_pair`, so it has to be updated along with it.
        // M / N1 => [b/d, a/d] = [-b/d; a/d] = [b/-d; -a/-d] = [b; -a] ./ [-d; -d]
        let x = s.swap(self.rep); // [b; -a]
        let y = s.swap(rhs.rep); // [d; -c]
        let y = s.neg0(y); // [-d; -c]
        let y = s.shuffle02(y, y); // [-d; -d]
        Self {
            rep: s.div_ru(x, y),
        }
    }

    #[inline(always)]
    pub(crate) fn div_m_p1<S: Simd>(self, s: S, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for an `s` whose backend is the
        // portable one, for the proofs of `(Dec)Interval::div` and
        // `(Dec)Interval::mul_rev_to_pair`, so it has to be updated along with it.
        // M / P1 => [a/c, b/c] = [-a/c; b/c] = [-a; b] ./ [c; c]
        let x = self.rep; // [-a; b]
        let y = s.neg0(rhs.rep); // [c; d]
        let y = s.shuffle02(y, y); // [c; c]
        Self {
            rep: s.div_ru(x, y),
        }
    }

    #[inline(always)]
    pub(crate) fn div_n_n0<S: Simd>(self, s: S, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for an `s` whose backend is the
        // portable one, for the proofs of `(Dec)Interval::div` and
        // `(Dec)Interval::mul_rev_to_pair`, so it has to be updated along with it.
        // N / N0 => [b/c, +∞] = [-b/c; +∞] = [b/-c; +∞]
        let x = s.swap(self.rep); // [b; -a]
        let y = rhs.rep; // [-c; d]
        Self {
            rep: s.shuffle02(s.div_ru(x, y), s.splat(f64::INFINITY)),
        }
    }

    #[inline(always)]
    pub(crate) fn div_n_n1<S: Simd>(self, s: S, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for an `s` whose backend is the
        // portable one, for the proofs of `(Dec)Interval::div` and
        // `(Dec)Interval::mul_rev_to_pair`, so it has to be updated along with it.
        // N / N1 => [b/c, a/d] = [-b/c; a/d] = [b/-c; a/d] = [b; a] ./ [-c; d]
        let x = s.neg0(self.rep); // [a; b]
        let x = s.swap(x); // [b; a]
        let y = rhs.rep; // [-c; d]
        Self {
            rep: s.div_ru(x, y),
        }
    }

    #[inline(always)]
    pub(crate) fn div_n_p0<S: Simd>(self, s: S, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for an `s` whose backend is the
        // portable one, for the proofs of `(Dec)Interval::div` and
        // `(Dec)Interval::mul_rev_to_pair`, so it has to be updated along with it.
        // N / P0 => [-∞, b/d] = [+∞; b/d]
        let x = self.rep; // [-a; b]
        let y = rhs.rep; // [-c; d]
        Self {
            rep: s.shuffle03(s.splat(f64::INFINITY), s.div_ru(x, y)),
        }
    }

    #[inline(always)]
    pub(crate) fn div_n_p1<S: Simd>(self, s: S, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for an `s` whose backend is the
        // portable one, for the proofs of `(Dec)Interval::div` and
        // `(Dec)Interval::mul_rev_to_pair`, so it has to be updated along with it.
        // N / P1 => [a/c, b/d] = [-a/c; b/d] = [-a; b] ./ [c; d]
        let x = self.rep; // [-a; b]
        let y = s.neg0(rhs.rep); // [c; d]
        Self {
            rep: s.div_ru(x, y),
        }
    }

    #[inline(always)]
    pub(crate) fn div_p_n0<S: Simd>(self, s: S, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for an `s` whose backend is the
        // portable one, for the proofs of `(Dec)Interval::div` and
        // `(Dec)Interval::mul_rev_to_pair`, so it has to be updated along with it.
        // P / N0 => [-∞, a/c] = [+∞; a/c] = [+∞; -a/-c]
        let x = self.rep; // [-a; b]
        let y = rhs.rep; // [-c; d]
        Self {
            rep: s.shuffle02(s.splat(f64::INFINITY), s.div_ru(x, y)),
        }
    }

    #[inline(always)]
    pub(crate) fn div_p_n1<S: Simd>(self, s: S, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for an `s` whose backend is the
        // portable one, for the proofs of `(Dec)Interval::div` and
        // `(Dec)Interval::mul_rev_to_pair`, so it has to be updated along with it.
        // P / N1 => [b/d, a/c] = [-b/d; a/c] = [-b/d; -a/-c] = [-b; -a] ./ [d; -c]
        let x = s.swap(self.rep); // [b; -a]
        let x = s.neg0(x); // [-b; -a]
        let y = s.swap(rhs.rep); // [d; -c]
        Self {
            rep: s.div_ru(x, y),
        }
    }

    #[inline(always)]
    pub(crate) fn div_p_p0<S: Simd>(self, s: S, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for an `s` whose backend is the
        // portable one, for the proofs of `(Dec)Interval::div` and
        // `(Dec)Interval::mul_rev_to_pair`, so it has to be updated along with it.
        // P / P0 => [a/d, +∞] = [-a/d; +∞]
        let x = self.rep; // [-a; b]
        let y = s.swap(rhs.rep); // [d; -c]
        Self {
            rep: s.shuffle02(s.div_ru(x, y), s.splat(f64::INFINITY)),
        }
    }

    #[inline(always)]
    pub(crate) fn div_p_p1<S: Simd>(self, s: S, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for an `s` whose backend is the
        // portable one, for the proofs of `(Dec)Interval::div` and
        // `(Dec)Interval::mul_rev_to_pair`, so it has to be updated along with it.
        // P / P1 => [a/d, b/c] = [-a/d; b/c] = [-a; b] ./ [d; c]
        let x = self.rep; // [-a; b]
        let y = s.neg0(rhs.rep); // [c; d]
        let y = s.swap(y); // [d; c]
        Self {
            rep: s.div_ru(x, y),
        }
    }

    /// Returns the reverse multiplication $\numerator \setdiv′ \self$
    /// (beware the order of the arguments) as an array of two intervals.
    /// The operation is also known as *two-output division* in IEEE Std 1788-2015.
    ///
    /// For intervals $𝒙$ and $𝒚$, the reverse multiplication is defined as:
    ///
    /// $$
    /// 𝒙 \setdiv′ 𝒚 = \set{z ∈ \R ∣ ∃y ∈ 𝒚 : zy ∈ 𝒙}.
    /// $$
    ///
    /// For comparison, the standard division is defined as:
    ///
    /// $$
    /// \begin{align*}
    ///  𝒙 \setdiv 𝒚 &= \set{x / y ∣ (x, y) ∈ 𝒙 × 𝒚 ∖ \set 0} \\\\
    ///   &= \set{z ∈ \R ∣ ∃y ∈ 𝒚 ∖ \set 0 : zy ∈ 𝒙}.
    /// \end{align*}
    /// $$
    ///
    /// The interval division $𝒙 / 𝒚$ is an enclosure of $𝒙 \setdiv 𝒚$.
    /// A notable difference between two definitions is that when $𝒙 = 𝒚 = \set 0$,
    /// $𝒙 \setdiv 𝒚 = ∅$, while $𝒙 \setdiv′ 𝒚 = \R$.
    ///
    /// The function returns:
    ///
    /// - `[`[`Interval::EMPTY`]`; 2]` if $\numerator \setdiv′ \self$ is empty;
    /// - `[z, `[`Interval::EMPTY`]`]` if $\numerator \setdiv′ \self$ has one component $𝒛$,
    ///   where `z` is the tightest enclosure of $𝒛$;
    /// - `[z1, z2]` if $\numerator \setdiv′ \self$ has two components $𝒛₁$ and $𝒛₂$
    ///   ordered so that $\sup 𝒛₁ ≤ \inf 𝒛₂$,
    ///   where `z1` and `z2` are the tightest enclosures of $𝒛₁$ and $𝒛₂$, respectively.
    ///
    /// When $\self ≠ ∅ ∧ \numerator ≠ ∅$, the number of components $\numerator \setdiv′ \self$ has
    /// are summarized as:
    ///
    /// |             | $0 ∈ \numerator$ | $0 ∉ \numerator$ |
    /// | :---------: | :--------------: | :--------------: |
    /// | $0 ∈ \self$ |        1         |    0, 1, or 2    |
    /// | $0 ∉ \self$ |        1         |        1         |
    ///
    /// # Examples
    ///
    /// ```
    /// use inari::{Interval as I, const_interval as c};
    /// let zero = c!(0.0, 0.0);
    /// assert_eq!(zero.mul_rev_to_pair(c!(1.0, 2.0)), [I::EMPTY; 2]);
    /// assert_eq!(zero.mul_rev_to_pair(c!(0.0, 2.0)), [I::ENTIRE, I::EMPTY]);
    /// assert_eq!(zero.mul_rev_to_pair(zero), [I::ENTIRE, I::EMPTY]);
    /// let x = c!(1.0, 2.0);
    /// assert_eq!(I::ENTIRE.mul_rev_to_pair(x), [c!(f64::NEG_INFINITY, 0.0), c!(0.0, f64::INFINITY)]);
    /// assert_eq!(c!(1.0, 1.0).mul_rev_to_pair(x), [x, I::EMPTY]);
    /// assert_eq!(c!(1.0, f64::INFINITY).mul_rev_to_pair(c!(1.0, 1.0)),
    ///            [c!(0.0, 1.0), I::EMPTY]);
    /// assert_eq!(c!(-1.0, 1.0).mul_rev_to_pair(c!(1.0, 2.0)),
    ///            [c!(f64::NEG_INFINITY, -1.0), c!(1.0, f64::INFINITY)]);
    /// assert_eq!(c!(-1.0, 1.0).mul_rev_to_pair(zero), [I::ENTIRE, I::EMPTY]);
    /// ```
    #[must_use]
    pub fn mul_rev_to_pair(self, numerator: Self) -> [Self; 2] {
        // Proved correct in `rocq/theories/MulRev.v` for the portable backend.
        // `rocq/theories/Model.v` transcribes this function, so it has to be updated
        // along with it.
        use IntervalClass2::*;
        match numerator.classify2(self) {
            E_E | E_M | E_N0 | E_N1 | E_P0 | E_P1 | E_Z | M_E | N0_E | N1_E | N1_Z | P0_E
            | P1_E | P1_Z | Z_E => [Self::EMPTY; 2],
            M_Z | N0_Z | P0_Z | Z_Z | M_M | M_N0 | M_P0 | N0_M | P0_M | Z_M | Z_N0 | Z_P0
            | N0_N0 | N0_P0 | P0_N0 | P0_P0 => [Self::ENTIRE, Self::EMPTY],
            Z_N1 | Z_P1 => [Self::zero(), Self::EMPTY],
            N1_M => {
                // N1 / M => [-∞, b/d] ∪ [b/c, +∞] = [+∞; b/d] ∪ [-b/c; +∞]
                // [-b/c, b/d] = [b; b] ./ [-c; d]
                let x = numerator.rep; // [-a; b]
                let x = shuffle13(x, x); // [b; b]
                let q = div_ru(x, self.rep); // [b/(-c); b/d]
                [
                    Self {
                        rep: shuffle13(splat(f64::INFINITY), q),
                    },
                    Self {
                        rep: shuffle02(q, splat(f64::INFINITY)),
                    },
                ]
            }
            P1_M => {
                // P1 / M => [-∞, a/c] ∪ [a/d, +∞] = [+∞; a/c] ∪ [-a/d; +∞]
                // [a/c; -a/d] = [-a; -a] ./ [-c; d]
                let x = numerator.rep; // [-a; b]
                let x = shuffle02(x, x); // [-a; -a]
                let q = div_ru(x, self.rep); // [a/c; -a/d]
                [
                    Self {
                        rep: shuffle02(splat(f64::INFINITY), q),
                    },
                    Self {
                        rep: shuffle13(q, splat(f64::INFINITY)),
                    },
                ]
            }
            M_N1 => [numerator.div_m_n1(CrateBaseline, self), Self::EMPTY],
            M_P1 => [numerator.div_m_p1(CrateBaseline, self), Self::EMPTY],
            N1_N0 => [numerator.div_n_n0(CrateBaseline, self), Self::EMPTY],
            N0_N1 | N1_N1 => [numerator.div_n_n1(CrateBaseline, self), Self::EMPTY],
            N1_P0 => [numerator.div_n_p0(CrateBaseline, self), Self::EMPTY],
            N0_P1 | N1_P1 => [numerator.div_n_p1(CrateBaseline, self), Self::EMPTY],
            P1_N0 => [numerator.div_p_n0(CrateBaseline, self), Self::EMPTY],
            P0_N1 | P1_N1 => [numerator.div_p_n1(CrateBaseline, self), Self::EMPTY],
            P1_P0 => [numerator.div_p_p0(CrateBaseline, self), Self::EMPTY],
            P0_P1 | P1_P1 => [numerator.div_p_p1(CrateBaseline, self), Self::EMPTY],
        }
    }

    /// Returns the tightest interval `z` such that `rhs` $+$ `z` $⊇$ `self`,
    /// if both `self` and `rhs` are bounded and the width of `self` is greater than or equal to
    /// that of `rhs`. Otherwise, returns [`Interval::ENTIRE`].
    ///
    /// Even when `x.cancel_minus(y)` is not [`Interval::ENTIRE`], its value is generally
    /// different from `x - y`, as the latter gives the tightest enclosure of `x` $-$ `y`,
    /// while the former does not always enclose `x` $-$ `y`.
    /// In such case, `x.cancel_minus(y)` $⊆$ `x - y` holds, but generally not the equality.
    ///
    /// # Examples
    ///
    /// Getting an enclosure of a partial sum omitting a single term from their total:
    ///
    /// ```
    /// use inari::*;
    /// let x = interval!("[0.1, 0.2]").unwrap();
    /// let y = interval!("[0.3, 0.4]").unwrap();
    /// let z = interval!("[0.5, 0.6]").unwrap();
    /// let sum = x + y + z;
    /// assert!((y + z).subset(sum.cancel_minus(x)));
    /// assert!((x + z).subset(sum.cancel_minus(y)));
    /// assert!((x + y).subset(sum.cancel_minus(z)));
    /// ```
    ///
    /// `sum.cancel_minus(x)` is a subset of `sum - x`:
    ///
    /// ```
    /// # use inari::*;
    /// # let x = interval!("[0.1, 0.2]").unwrap();
    /// # let y = interval!("[0.3, 0.4]").unwrap();
    /// # let z = interval!("[0.5, 0.6]").unwrap();
    /// # let sum = x + y + z;
    /// assert!(sum.cancel_minus(x).subset(sum - x));
    /// ```
    ///
    /// But the inverse does not hold in general:
    ///
    /// ```should_panic
    /// # use inari::*;
    /// # let x = interval!("[0.1, 0.2]").unwrap();
    /// # let y = interval!("[0.3, 0.4]").unwrap();
    /// # let z = interval!("[0.5, 0.6]").unwrap();
    /// # let sum = x + y + z;
    /// assert!((sum - x).subset(sum.cancel_minus(x)));
    /// ```
    ///
    /// `sum.cancel_minus(x)`, etc. returns [`Interval::ENTIRE`] when `sum` is unbounded:
    ///
    /// ```
    /// use inari::*;
    /// let x = const_interval!(1.0, 2.0);
    /// let y = const_interval!(3.0, f64::MAX);
    /// let sum = x + y;
    /// assert_eq!(sum.cancel_minus(x), Interval::ENTIRE);
    /// assert_eq!(sum.cancel_minus(y), Interval::ENTIRE);
    /// ```
    ///
    /// `sum.cancel_minus(x)` returns [`Interval::ENTIRE`] when the width of “`sum`” is
    /// less than that of `x`:
    ///
    /// ```
    /// use inari::*;
    /// let x = const_interval!(1.0, 2.0);
    /// let sum = const_interval!(4.0, 4.5);
    /// assert_eq!(sum.cancel_minus(x), Interval::ENTIRE);
    /// ```
    #[must_use]
    pub fn cancel_minus(self, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/Cancel.v` for the portable backend.
        // `rocq/theories/Model.v` transcribes this function, so it has to be updated
        // along with it.
        use Ordering::*;
        // cancel_minus([a, b], [c, d]) =
        //
        //            | Empty  | Common | Unbounded
        // -----------+--------+--------+-----------
        //  Empty     | Empty  | Empty  |  Entire
        //  Common    | Entire |   *1   |  Entire
        //  Unbounded | Entire | Entire |  Entire
        //
        // *1  | [a - c, b - d]  if width(x) ≥ width(y),
        //     | Entire          otherwise.
        if self.is_empty() && (rhs.is_empty() || rhs.is_common_interval()) {
            return Self::EMPTY;
        }
        if !self.is_common_interval() || rhs.is_empty() || !rhs.is_common_interval() {
            return Self::ENTIRE;
        }

        let x = self.rep; // [-a; b]
        let y = rhs.rep; // [-c; d]
        let z = sub_ru(x, y); // [a - c, b - d] = [c - a; b - d] = [-a; b] .- [-c; d]
        let w_rn = hadd_rn(x, y); // [width(x); width(y)] = [b - a; d - c] = [-a; -c] .+ [b; d],
                                  // rounded to nearest, ≥ 0.
        let [wx, wy] = extract(w_rn);
        let (x, y, w_rn) = if wx == f64::INFINITY && wy == f64::INFINITY {
            // Both widths overflow, so every bound is at least 2^970 in magnitude:
            // b - a ≥ 2^1024 - 2^970 and b ≤ f64::MAX = 2^1024 - 2^971 give -a ≥ 2^970,
            // and the same holds for b, c and d. Halving such a float is exact, and the
            // halved widths are at most f64::MAX, so they are compared instead.
            let [ma, b] = extract(x);
            let [mc, d] = extract(y);
            let x = constant(0.5 * ma, 0.5 * b);
            let y = constant(0.5 * mc, 0.5 * d);
            (x, y, hadd_rn(x, y))
        } else {
            (x, y, w_rn)
        };
        let [wx, wy] = extract(w_rn);
        // `wx` and `wy` are not NaN as `x` and `y` are common intervals.
        match wx.partial_cmp(&wy) {
            Some(Greater) => {
                // width(x) > width(y) without rounding.
                // `z.inf()` cannot be +∞ due to rounding downward.
                Self { rep: z }
            }
            Some(Less) => Self::ENTIRE,
            Some(Equal) => {
                // wx = wy < +∞.
                // Use the Fast2Sum algorithm (T. J. Dekker, A floating-point technique for
                // extending the available precision, Numer. Math. 18, 1971) to compute the
                // remainders dx and dy, where
                //   -a + b = wx + dx, -c + d = wy + dy, or
                //   [-a; -c] .+ [b; d] = w_rn .+ dw.
                // It needs an addend whose magnitude is at least that of the other:
                // -a + b ≥ 0, so the larger of -a and b is at least |the smaller|, and the
                // same holds for -c and d. No step overflows, unlike in 2Sum, which
                // overflows for x = y = [f64::MIN, -3 × 2^970].
                //
                // (w_rn, dw) = elementwise_fast_two_sum(hi, lo)
                //   hi := max([-a; -c], [b; d]), lo := min([-a; -c], [b; d])
                //   w_rn = hi .+ lo
                //   t := hi .- w_rn
                //   dw := lo .+ t
                let hi = max(shuffle02(x, y), shuffle13(x, y));
                let lo = min(shuffle02(x, y), shuffle13(x, y));
                let t = sub_rn(hi, w_rn);
                let dw = add_rn(lo, t);
                let [dwx, dwy] = extract(dw);
                if dwx >= dwy {
                    Self { rep: z }
                } else {
                    Self::ENTIRE
                }
            }
            None => unreachable!(),
        }
    }

    /// `x.cancel_plus(y)` is equivalent to `x.cancel_minus(-y)`.
    ///
    /// See [`Interval::cancel_minus`] for more information.
    #[inline]
    #[must_use]
    pub fn cancel_plus(self, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/Cancel.v` for the portable backend.
        // `rocq/theories/Model.v` transcribes this function, so it has to be updated
        // along with it.
        self.cancel_minus(-rhs)
    }

    /// Returns $(\self × \rhs) + \addend$.
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain | Range |
    /// | ------ | ----- |
    /// | $\R^3$ | $\R$  |
    #[must_use]
    pub fn mul_add(self, rhs: Self, addend: Self) -> Self {
        // Proved correct in `rocq/theories/MulAdd.v` for the portable backend, as `mul_add_with`
        // called with `CrateBaseline`, whose backend is that of `Baseline` (see `CrateBaseline`
        // in `src/simd/token.rs`). `rocq/theories/Model.v` transcribes this call, so it has to
        // be updated along with it.
        self.mul_add_with(CrateBaseline, rhs, addend)
    }

    /// Returns `self.mul_add(rhs, addend)`, computed by the backend of `s` (see
    /// [`Simd`](crate::simd::Simd)).
    ///
    /// The result is the same interval as `self.mul_add(rhs, addend)` for every `s`, as both are
    /// the tightest result ([Conformance to the standard](crate::_docs::conformance): "Unless
    /// otherwise noted, all operations return the tightest results").
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
    /// let z = c!(0.1, 0.2);
    /// assert_eq!(Baseline.vectorize(|| x.mul_add_with(Baseline, y, z)), x.mul_add(y, z));
    /// #[cfg(target_arch = "x86_64")]
    /// {
    ///     if let Some(s) = inari::simd::V3::try_new() {
    ///         assert_eq!(s.vectorize(|| x.mul_add_with(s, y, z)), x.mul_add(y, z));
    ///     }
    /// }
    /// ```
    // Almost a copy-paste of mul. Additions/modifications are indicated with "// *".
    #[allow(clippy::many_single_char_names)]
    #[inline(always)]
    #[must_use]
    pub fn mul_add_with<S: Simd>(self, s: S, rhs: Self, addend: Self) -> Self {
        // Proved correct in `rocq/theories/MulAdd.v` for an `s` whose backend is the portable
        // one and whose `classify_bits` is that of `src/classify.rs`. `rocq/theories/Model.v`
        // transcribes this function for such an `s`, so it has to be updated along with it.
        if addend.is_empty() {
            return Self::EMPTY; // *
        }

        use IntervalClass2::*;
        match self.classify2_with(s, rhs) {
            E_E | E_M | E_N0 | E_N1 | E_P0 | E_P1 | E_Z | M_E | N0_E | N1_E | P0_E | P1_E | Z_E => {
                Self::EMPTY
            }
            M_Z | N0_Z | N1_Z | P0_Z | P1_Z | Z_M | Z_N0 | Z_N1 | Z_P0 | Z_P1 | Z_Z => addend, // *
            M_M => {
                let x = s.shuffle02(self.rep, self.rep);
                let y = s.swap(rhs.rep);
                let xy = s.mul_add_ru(x, y, addend.rep); // *
                let z = s.shuffle13(self.rep, self.rep);
                let w = rhs.rep;
                let zw = s.mul_add_ru(z, w, addend.rep); // *
                let r = s.max(xy, zw);
                Self { rep: r }
            }
            M_N0 | M_N1 => {
                let x = s.swap(self.rep);
                let y = s.shuffle02(rhs.rep, rhs.rep);
                Self {
                    rep: s.mul_add_ru(x, y, addend.rep), // *
                }
            }
            M_P0 | M_P1 => {
                let x = self.rep;
                let y = s.shuffle13(rhs.rep, rhs.rep);
                Self {
                    rep: s.mul_add_ru(x, y, addend.rep), // *
                }
            }
            N0_M | N1_M => {
                let x = s.shuffle02(self.rep, self.rep);
                let y = s.swap(rhs.rep);
                Self {
                    rep: s.mul_add_ru(x, y, addend.rep), // *
                }
            }
            N0_N0 | N0_N1 | N1_N0 | N1_N1 => {
                let x = s.swap(self.rep);
                let x = s.neg0(x);
                let y = s.swap(rhs.rep);
                Self {
                    rep: s.mul_add_ru(x, y, addend.rep), // *
                }
            }
            N0_P0 | N0_P1 | N1_P0 | N1_P1 => {
                let x = self.rep;
                let y = s.neg0(rhs.rep);
                let y = s.swap(y);
                Self {
                    rep: s.mul_add_ru(x, y, addend.rep), // *
                }
            }
            P0_M | P1_M => {
                let x = s.shuffle13(self.rep, self.rep);
                let y = rhs.rep;
                Self {
                    rep: s.mul_add_ru(x, y, addend.rep), // *
                }
            }
            P0_N0 | P0_N1 | P1_N0 | P1_N1 => {
                let x = s.neg0(self.rep);
                let x = s.swap(x);
                let y = rhs.rep;
                Self {
                    rep: s.mul_add_ru(x, y, addend.rep), // *
                }
            }
            P0_P0 | P0_P1 | P1_P0 | P1_P1 => {
                let x = self.rep;
                let y = s.neg0(rhs.rep);
                Self {
                    rep: s.mul_add_ru(x, y, addend.rep), // *
                }
            }
        }
    }

    /// Returns the multiplicative inverse of `self`.
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain        | Range         |
    /// | ------------- | ------------- |
    /// | $\R ∖ \set 0$ | $\R ∖ \set 0$ |
    #[must_use]
    pub fn recip(self) -> Self {
        // Proved correct in `rocq/theories/Recip.v` for the portable backend, as `recip_with`
        // called with `CrateBaseline`, whose backend is that of `Baseline` (see `CrateBaseline`
        // in `src/simd/token.rs`). `rocq/theories/Model.v` transcribes this call, so it has to
        // be updated along with it.
        self.recip_with(CrateBaseline)
    }

    /// Returns `self.recip()`, computed by the backend of `s` (see [`Simd`](crate::simd::Simd)).
    ///
    /// The result is the same interval as `self.recip()` for every `s`, as both are the tightest
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
    /// let x = c!(3.0, 4.0);
    /// assert_eq!(Baseline.vectorize(|| x.recip_with(Baseline)), x.recip());
    /// #[cfg(target_arch = "x86_64")]
    /// {
    ///     if let Some(s) = inari::simd::V3::try_new() {
    ///         assert_eq!(s.vectorize(|| x.recip_with(s)), x.recip());
    ///     }
    /// }
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn recip_with<S: Simd>(self, s: S) -> Self {
        // Proved correct in `rocq/theories/Recip.v` for an `s` whose backend is the portable
        // one and whose `classify_bits` is that of `src/classify.rs`. `rocq/theories/Model.v`
        // transcribes this function for such an `s`, so it has to be updated along with it.
        use IntervalClass::*;
        match self.classify_with(s) {
            E | Z => Self::EMPTY,
            M => Self::ENTIRE,
            N0 => {
                // 1 / N0 => [-∞, 1/a] = [+∞; -1/-a]
                let x = s.splat(-1.0);
                let y = self.rep; // [-a; b]
                Self {
                    rep: s.shuffle02(s.splat(f64::INFINITY), s.div_ru(x, y)),
                }
            }
            N1 => {
                // 1 / N1 => [1/b, 1/a] = [-1/b; 1/a] = [-1/b; -1/-a] = [-1; -1] ./ [b; -a]
                let x = s.splat(-1.0);
                let y = s.swap(self.rep); // [b; -a]
                Self {
                    rep: s.div_ru(x, y),
                }
            }
            P0 => {
                // 1 / P0 => [1/b, +∞] = [-1/b; +∞]
                let x = s.splat(-1.0);
                let y = self.rep; // [-a; b]
                Self {
                    rep: s.shuffle13(s.div_ru(x, y), s.splat(f64::INFINITY)),
                }
            }
            P1 => {
                // 1 / P1 => [1/b, 1/a] = [-1/b; 1/a] = [-1/b; -1/-a] = [-1; -1] ./ [b; -a]
                let x = s.splat(-1.0);
                let y = s.swap(self.rep); // [b; -a]
                Self {
                    rep: s.div_ru(x, y),
                }
            }
        }
    }

    /// Returns the square of `self`.
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain | Range     |
    /// | ------ | --------- |
    /// | $\R$   | $\[0, ∞)$ |
    #[must_use]
    pub fn sqr(self) -> Self {
        // Proved correct in `rocq/theories/Sqr.v` for the portable backend, as `sqr_with`
        // called with `CrateBaseline`, whose backend is that of `Baseline` (see `CrateBaseline`
        // in `src/simd/token.rs`). `rocq/theories/Model.v` transcribes this call, so it has to
        // be updated along with it.
        self.sqr_with(CrateBaseline)
    }

    /// Returns `self.sqr()`, computed by the backend of `s` (see [`Simd`](crate::simd::Simd)).
    ///
    /// The result is the same interval as `self.sqr()` for every `s`, as both are the tightest
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
    /// let x = c!(-3.0, 0.1);
    /// assert_eq!(Baseline.vectorize(|| x.sqr_with(Baseline)), x.sqr());
    /// #[cfg(target_arch = "x86_64")]
    /// {
    ///     if let Some(s) = inari::simd::V3::try_new() {
    ///         assert_eq!(s.vectorize(|| x.sqr_with(s)), x.sqr());
    ///     }
    /// }
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn sqr_with<S: Simd>(self, s: S) -> Self {
        // Proved correct in `rocq/theories/Sqr.v` for an `s` whose backend is the portable one
        // and whose `classify_bits` is that of `src/classify.rs`. `rocq/theories/Model.v`
        // transcribes this function for such an `s`, so it has to be updated along with it.
        use IntervalClass::*;
        match self.classify_with(s) {
            E => Self::EMPTY,
            Z => Self::zero(),
            M => {
                // [0, max(a^2, b^2)] = [0; max(a^2, b^2)]
                let x = self.rep; // [-a; b]
                let r = s.mul_ru(x, x); // [a^2; b^2]
                let r = s.max(r, s.swap(r)); // [max(a^2, b^2); _]
                Self {
                    rep: s.shuffle02(s.splat(0.0), r),
                }
            }
            N0 | N1 => {
                // [b^2, a^2] = [-b^2; a^2] = [-b; -a] .* [b; -a]
                let x = s.swap(self.rep); // [b; -a]
                let y = s.neg0(x); // [-b; -a]
                Self {
                    rep: s.mul_ru(x, y),
                }
            }
            P0 | P1 => {
                // [a^2, b^2] = [-a^2; b^2] = [-a; b] .* [a; b]
                let x = self.rep; // [-a; b]
                let y = s.neg0(x); // [a; b]
                Self {
                    rep: s.mul_ru(x, y),
                }
            }
        }
    }

    /// Returns the principal square root of `self`.
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain    | Range     |
    /// | --------- | --------- |
    /// | $\[0, ∞)$ | $\[0, ∞)$ |
    #[must_use]
    pub fn sqrt(self) -> Self {
        // Proved correct in `rocq/theories/Sqrt.v` for the portable backend, as `sqrt_with`
        // called with `Baseline`. `rocq/theories/Model.v` transcribes this call, so it has to
        // be updated along with it.
        self.sqrt_with(Baseline)
    }

    /// Returns `self.sqrt()`, computed by the backend of `s` (see [`Simd`](crate::simd::Simd)).
    ///
    /// The result is the same interval as `self.sqrt()` for every `s`, as both are the tightest
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
    /// let x = c!(2.0, 3.0);
    /// assert_eq!(Baseline.vectorize(|| x.sqrt_with(Baseline)), x.sqrt());
    /// #[cfg(target_arch = "x86_64")]
    /// {
    ///     if let Some(s) = inari::simd::V3::try_new() {
    ///         assert_eq!(s.vectorize(|| x.sqrt_with(s)), x.sqrt());
    ///     }
    /// }
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn sqrt_with<S: Simd>(self, s: S) -> Self {
        // Proved correct in `rocq/theories/Sqrt.v` for an `s` whose backend is the portable
        // one. `rocq/theories/Model.v` transcribes this function for such an `s`, each arm of
        // the `cfg_if!`, so it has to be updated along with it.
        cfg_if::cfg_if! {
            if #[cfg(target_arch = "wasm32")] {
                // The two tests of the empty results, as the one test of the other arm ran
                // more wasm operators per call on some arguments (counted with wasmtime's
                // fuel, rustc 1.96): up to 4 more on an empty `self` (none in `Interval::sqrt`),
                // with and without `simd128`, and 1 more on [-2, -1] and [-1, 4] in
                // `DecInterval::sqrt_with` without it, where the branch to `EMPTY` on
                // `b >= 0.0` false took an `i32.eqz`, though 2 to 8 fewer on most of the others.
                if self.is_empty() {
                    return Self::EMPTY;
                }

                let a = self.inf_raw();
                let b = self.sup_raw();

                if b < 0.0 {
                    Self::EMPTY
                } else if a <= 0.0 {
                    // As in the other arm.
                    Self::with_infsup_raw(0.0, s.sqrt1_ru(b))
                } else {
                    Self {
                        rep: s.neg0(s.sqrt_rd_ru(s.neg0(self.rep))),
                    }
                }
            } else {
                let a = self.inf_raw();
                let b = self.sup_raw();

                // `b >= 0.0` is false where `b < 0.0`, and where `self` is empty, which is
                // stored as [NaN; NaN] (see `Interval`), so this one test sends both to
                // `EMPTY`.
                if b >= 0.0 {
                    if a <= 0.0 {
                        // Only one square root is needed, so `sqrt_rd_ru` would be wasted: a
                        // lower lane of zero fails its fast-path check (see BENCHMARKS.md).
                        Self::with_infsup_raw(0.0, s.sqrt1_ru(b))
                    } else {
                        // Both endpoints in one vector square root. `neg0` turns the
                        // representation [-a; b] into [a; b], and back afterward.
                        Self {
                            rep: s.neg0(s.sqrt_rd_ru(s.neg0(self.rep))),
                        }
                    }
                } else {
                    Self::EMPTY
                }
            }
        }
    }
}

// The body of `DecInterval::mul_add_with`, with `$lhs` for `self`, `$rhs` for `rhs`, `$addend` for
// `addend`, `$x` for the interval of the result, which it evaluates only if none of `$lhs`,
// `$rhs` and `$addend` is NaI, and `$set_dec` for the function that decorates it. `mul_add_with`
// expands it with `self.x().mul_add_with(s, rhs.x(), addend.x())` and with
// `Self::set_dec_impl`, which is `#[inline]`. `DecInterval::mul_add` expands it with
// `self.x().mul_add(rhs.x(), addend.x())` and with `Self::set_dec`, which is not, rather than
// calling `mul_add_with` with `Baseline`, which would inline the body of
// `Interval::mul_add_with` into it. In a plain x86-64 build of the library that took 7 to 56
// more instructions per call, as `DecInterval::mul_add` then called `generic::mul_add_ru_impl`
// and `generic::max` out of line (seen with rustc 1.98, when `Interval::mul_add` called
// `mul_add_with` with `Baseline` too, not with `CrateBaseline`).
macro_rules! dec_mul_add_with_body {
    ($lhs:ident, $rhs:ident, $addend:ident, $x:expr, $set_dec:path) => {{
        if $lhs.is_nai() || $rhs.is_nai() || $addend.is_nai() {
            return Self::NAI;
        }

        $set_dec($x, $lhs.d().min($rhs.d().min($addend.d())))
    }};
}

// The body of `DecInterval::recip_with`, with `$lhs` for `self`, `$x` for the interval of the
// result, which it evaluates only if `$lhs` is not NaI, and `$set_dec` for the function that
// decorates it. `recip_with` expands it with `self.x().recip_with(s)` and with
// `Self::set_dec_impl`, which is `#[inline]`. `DecInterval::recip` expands it with
// `self.x().recip()` and with `Self::set_dec`, which is not, rather than calling `recip_with`
// with `Baseline`. With that call, `DecInterval::recip` took one more branch per call for a
// positive or a negative interval in a plain x86-64 build of the library, though 12 fewer
// instructions (seen with rustc 1.98, when `Interval::recip` called `recip_with` with `Baseline`
// too, not with `CrateBaseline`).
macro_rules! dec_recip_with_body {
    ($lhs:ident, $x:expr, $set_dec:path) => {{
        if $lhs.is_nai() {
            return $lhs;
        }

        let d = if $lhs.x().contains(0.0) {
            Decoration::Trv
        } else {
            $lhs.d()
        };
        $set_dec($x, d)
    }};
}

// The body of `DecInterval::sqr_with`, with `$lhs`, `$x` and `$set_dec` as in
// `dec_recip_with_body!`. `DecInterval::sqr` expands it with `self.x().sqr()` and with
// `Self::set_dec` rather than calling `sqr_with` with `Baseline`. With every operation of
// `DecInterval` without a token calling its `*_with` method with `Baseline`, `Interval::sqr`,
// whose source is the same either way, took 5 more instructions per call for a positive or a
// mixed interval in a plain x86-64 build of the library (seen with rustc 1.98, when
// `Interval::sqr` called `sqr_with` with `Baseline` too, not with `CrateBaseline`).
macro_rules! dec_sqr_with_body {
    ($lhs:ident, $x:expr, $set_dec:path) => {{
        if $lhs.is_nai() {
            return $lhs;
        }

        $set_dec($x, $lhs.d())
    }};
}

// The body of `DecInterval::sqrt_with`, with `$lhs`, `$x` and `$set_dec` as in
// `dec_recip_with_body!`. `DecInterval::sqrt` expands it with `self.x().sqrt()` and with
// `Self::set_dec` rather than calling `sqrt_with` with `Baseline`. With that call, and with
// `Interval::contains` and `Interval::is_common_interval` not `#[inline]`, `DecInterval::sqrt`
// took two more branches per call for a positive interval in a haswell build of the library.
// With them `#[inline]`, and with every operation of `DecInterval` without a token calling its
// `*_with` method with `Baseline`, it took no more instructions or branches per call there, and
// up to 6 fewer instructions per call in a plain x86-64 build (seen with rustc 1.98). That call
// in `DecInterval::sqrt` alone, with the other operations as they are, was not counted.
macro_rules! dec_sqrt_with_body {
    ($lhs:ident, $x:expr, $set_dec:path) => {{
        if $lhs.is_nai() {
            return $lhs;
        }

        let d = if $lhs.x().inf_raw() < 0.0 {
            Decoration::Trv
        } else {
            $lhs.d()
        };
        $set_dec($x, d)
    }};
}

impl DecInterval {
    /// The decorated version of [`Interval::mul_rev_to_pair`].
    ///
    /// `[`[`DecInterval::NAI`]`; 2]` is returned if `self` or `numerator` is NaI.
    /// When $0 ∉ \self ≠ ∅ ∧ \numerator ≠ ∅$, `[z,`[`DecInterval::EMPTY`]`]` is returned
    /// with `z` being the same as `numerator / self` and decorated the same way.
    /// In all other cases, both outputs are decorated with [`Decoration::Trv`].
    #[must_use]
    pub fn mul_rev_to_pair(self, numerator: Self) -> [Self; 2] {
        // Proved correct in `rocq/theories/MulRev.v` for the portable backend.
        // `rocq/theories/Model.v` transcribes this function, so it has to be updated
        // along with it.
        if self.is_nai() || numerator.is_nai() {
            return [Self::NAI; 2];
        }
        let [u, v] = self.x().mul_rev_to_pair(numerator.x());
        let d = if self.x().contains(0.0) {
            Decoration::Trv
        } else {
            self.d().min(numerator.d())
        };
        [Self::set_dec(u, d), Self::set_dec(v, Decoration::Trv)]
    }

    /// The decorated version of [`Interval::cancel_minus`].
    ///
    /// A NaI is returned if `self` or `rhs` is NaI.
    #[must_use]
    pub fn cancel_minus(self, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/Cancel.v` for the portable backend.
        // `rocq/theories/Model.v` transcribes this function, so it has to be updated
        // along with it.
        if self.is_nai() || rhs.is_nai() {
            return Self::NAI;
        }
        Self::set_dec(self.x().cancel_minus(rhs.x()), Decoration::Trv)
    }

    /// The decorated version of [`Interval::cancel_plus`].
    ///
    /// A NaI is returned if `self` or `rhs` is NaI.
    #[must_use]
    pub fn cancel_plus(self, rhs: Self) -> Self {
        // Proved correct in `rocq/theories/Cancel.v` for the portable backend.
        // `rocq/theories/Model.v` transcribes this function, so it has to be updated
        // along with it.
        if self.is_nai() || rhs.is_nai() {
            return Self::NAI;
        }
        Self::set_dec(self.x().cancel_plus(rhs.x()), Decoration::Trv)
    }

    /// The decorated version of [`Interval::mul_add`].
    ///
    /// A NaI is returned if `self`, `rhs` or `addend` is NaI.
    #[must_use]
    pub fn mul_add(self, rhs: Self, addend: Self) -> Self {
        // Proved correct in `rocq/theories/MulAdd.v` for the portable backend, as
        // `mul_add_with` called with `CrateBaseline`, if `self` and `rhs` are `com` only when
        // `self.x()` and `rhs.x()` are common, which `rocq/theories/ComCommon.v` proves of
        // every `DecInterval` that the library makes: this is the body of `mul_add_with`,
        // `dec_mul_add_with_body!`, with `self.x().mul_add(rhs.x(), addend.x())`, which is
        // `self.x().mul_add_with(CrateBaseline, rhs.x(), addend.x())`, for the interval, and
        // with `Self::set_dec`, which calls `Self::set_dec_impl` (see the comment on the macro).
        // `rocq/theories/Model.v` transcribes this, so it has to be updated along with it.
        dec_mul_add_with_body!(
            self,
            rhs,
            addend,
            self.x().mul_add(rhs.x(), addend.x()),
            Self::set_dec
        )
    }

    /// The decorated version of [`Interval::mul_add_with`].
    ///
    /// A NaI is returned if `self`, `rhs` or `addend` is NaI.
    ///
    /// The result has the same `interval()` and `decoration()` as `self.mul_add(rhs, addend)` for
    /// every `s`, as the interval that [`Interval::mul_add_with`] returns is the same for every
    /// `s`, and the decoration depends only on `self`, `rhs`, `addend` and that interval.
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
    /// let z = c!(0.1, 0.2);
    /// let w = x.mul_add(y, z);
    /// let r = Baseline.vectorize(|| x.mul_add_with(Baseline, y, z));
    /// assert_eq!((r.interval(), r.decoration()), (w.interval(), w.decoration()));
    /// #[cfg(target_arch = "x86_64")]
    /// {
    ///     if let Some(s) = inari::simd::V3::try_new() {
    ///         let r = s.vectorize(|| x.mul_add_with(s, y, z));
    ///         assert_eq!((r.interval(), r.decoration()), (w.interval(), w.decoration()));
    ///     }
    /// }
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn mul_add_with<S: Simd>(self, s: S, rhs: Self, addend: Self) -> Self {
        // Proved correct in `rocq/theories/MulAdd.v` for an `s` whose backend is the portable
        // one and whose `classify_bits` is that of `src/classify.rs`, if `self` and `rhs` are
        // `com` only when `self.x()` and `rhs.x()` are common, which `rocq/theories/ComCommon.v`
        // proves of every `DecInterval` that the library makes. `rocq/theories/Model.v`
        // transcribes this function for such an `s`, so it has to be updated along with it and
        // with `dec_mul_add_with_body!`, which is its body.
        dec_mul_add_with_body!(
            self,
            rhs,
            addend,
            self.x().mul_add_with(s, rhs.x(), addend.x()),
            Self::set_dec_impl
        )
    }

    /// The decorated version of [`Interval::recip`].
    ///
    /// A NaI is returned if `self` is NaI.
    #[must_use]
    pub fn recip(self) -> Self {
        // Proved correct in `rocq/theories/Recip.v` for the portable backend, as `recip_with`
        // called with `CrateBaseline`, if `self` is `com` only when `self.x()` is common, which
        // `rocq/theories/ComCommon.v` proves of every `DecInterval` that the library makes:
        // this is the body of `recip_with`, `dec_recip_with_body!`, with `self.x().recip()`,
        // which is `self.x().recip_with(CrateBaseline)`, for the interval, and with
        // `Self::set_dec`, which calls `Self::set_dec_impl` (see the comment on the macro).
        // `rocq/theories/Model.v` transcribes this, so it has to be updated along with it.
        dec_recip_with_body!(self, self.x().recip(), Self::set_dec)
    }

    /// The decorated version of [`Interval::recip_with`].
    ///
    /// A NaI is returned if `self` is NaI.
    ///
    /// The result has the same `interval()` and `decoration()` as `self.recip()` for every `s`, as
    /// the interval that [`Interval::recip_with`] returns is the same for every `s`, and the
    /// decoration depends only on `self` and that interval.
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
    /// let x = c!(3.0, 4.0);
    /// let w = x.recip();
    /// let r = Baseline.vectorize(|| x.recip_with(Baseline));
    /// assert_eq!((r.interval(), r.decoration()), (w.interval(), w.decoration()));
    /// #[cfg(target_arch = "x86_64")]
    /// {
    ///     if let Some(s) = inari::simd::V3::try_new() {
    ///         let r = s.vectorize(|| x.recip_with(s));
    ///         assert_eq!((r.interval(), r.decoration()), (w.interval(), w.decoration()));
    ///     }
    /// }
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn recip_with<S: Simd>(self, s: S) -> Self {
        // Proved correct in `rocq/theories/Recip.v` for an `s` whose backend is the portable
        // one and whose `classify_bits` is that of `src/classify.rs`, if `self` is `com` only
        // when `self.x()` is common, which
        // `rocq/theories/ComCommon.v` proves of every `DecInterval` that the library makes.
        // `rocq/theories/Model.v` transcribes this function for such an `s`, so it has to be
        // updated along with it and with `dec_recip_with_body!`, which is its body.
        dec_recip_with_body!(self, self.x().recip_with(s), Self::set_dec_impl)
    }

    /// The decorated version of [`Interval::sqr`].
    ///
    /// A NaI is returned if `self` is NaI.
    #[must_use]
    pub fn sqr(self) -> Self {
        // Proved correct in `rocq/theories/Sqr.v` for the portable backend, as `sqr_with`
        // called with `CrateBaseline`: this is the body of `sqr_with`, `dec_sqr_with_body!`, with
        // `self.x().sqr()`, which is `self.x().sqr_with(CrateBaseline)`, for the interval, and
        // with `Self::set_dec`, which calls `Self::set_dec_impl` (see the comment on the macro).
        // `rocq/theories/Model.v` transcribes this, so it has to be updated along with it.
        dec_sqr_with_body!(self, self.x().sqr(), Self::set_dec)
    }

    /// The decorated version of [`Interval::sqr_with`].
    ///
    /// A NaI is returned if `self` is NaI.
    ///
    /// The result has the same `interval()` and `decoration()` as `self.sqr()` for every `s`, as
    /// the interval that [`Interval::sqr_with`] returns is the same for every `s`, and the
    /// decoration depends only on `self` and that interval.
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
    /// let x = c!(-3.0, 0.1);
    /// let w = x.sqr();
    /// let r = Baseline.vectorize(|| x.sqr_with(Baseline));
    /// assert_eq!((r.interval(), r.decoration()), (w.interval(), w.decoration()));
    /// #[cfg(target_arch = "x86_64")]
    /// {
    ///     if let Some(s) = inari::simd::V3::try_new() {
    ///         let r = s.vectorize(|| x.sqr_with(s));
    ///         assert_eq!((r.interval(), r.decoration()), (w.interval(), w.decoration()));
    ///     }
    /// }
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn sqr_with<S: Simd>(self, s: S) -> Self {
        // Proved correct in `rocq/theories/Sqr.v` for an `s` whose backend is the portable one
        // and whose `classify_bits` is that of `src/classify.rs`. `rocq/theories/Model.v`
        // transcribes this function for such an `s`, so it has to be updated along with it and
        // with `dec_sqr_with_body!`, which is its body.
        dec_sqr_with_body!(self, self.x().sqr_with(s), Self::set_dec_impl)
    }

    /// The decorated version of [`Interval::sqrt`].
    ///
    /// A NaI is returned if `self` is NaI.
    #[must_use]
    pub fn sqrt(self) -> Self {
        // Proved correct in `rocq/theories/Sqrt.v` for the portable backend, as `sqrt_with`
        // called with `Baseline`: this is the body of `sqrt_with`, `dec_sqrt_with_body!`, with
        // `self.x().sqrt()`, which is `self.x().sqrt_with(Baseline)`, for the interval, and with
        // `Self::set_dec`, which calls `Self::set_dec_impl` (see the comment on the macro).
        // `rocq/theories/Model.v` transcribes this, so it has to be updated along with it.
        dec_sqrt_with_body!(self, self.x().sqrt(), Self::set_dec)
    }

    /// The decorated version of [`Interval::sqrt_with`].
    ///
    /// A NaI is returned if `self` is NaI.
    ///
    /// The result has the same `interval()` and `decoration()` as `self.sqrt()` for every `s`, as
    /// the interval that [`Interval::sqrt_with`] returns is the same for every `s`, and the
    /// decoration depends only on `self` and that interval.
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
    /// let x = c!(2.0, 3.0);
    /// let w = x.sqrt();
    /// let r = Baseline.vectorize(|| x.sqrt_with(Baseline));
    /// assert_eq!((r.interval(), r.decoration()), (w.interval(), w.decoration()));
    /// #[cfg(target_arch = "x86_64")]
    /// {
    ///     if let Some(s) = inari::simd::V3::try_new() {
    ///         let r = s.vectorize(|| x.sqrt_with(s));
    ///         assert_eq!((r.interval(), r.decoration()), (w.interval(), w.decoration()));
    ///     }
    /// }
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn sqrt_with<S: Simd>(self, s: S) -> Self {
        // Proved correct in `rocq/theories/Sqrt.v` for an `s` whose backend is the portable
        // one. `rocq/theories/Model.v` transcribes this function for such an `s`, so it has to
        // be updated along with it and with `dec_sqrt_with_body!`, which is its body.
        dec_sqrt_with_body!(self, self.x().sqrt_with(s), Self::set_dec_impl)
    }
}

#[cfg(test)]
mod tests {
    use crate::*;
    use DecInterval as DI;
    use Interval as I;

    #[test]
    fn empty() {
        assert!((I::EMPTY.mul_add(I::PI, I::PI)).is_empty());
        assert!((I::PI.mul_add(I::EMPTY, I::PI)).is_empty());
        assert!((I::PI.mul_add(I::PI, I::EMPTY)).is_empty());

        assert!(I::EMPTY.recip().is_empty());
        assert!(I::EMPTY.sqrt().is_empty());
        assert!(I::EMPTY.sqr().is_empty());

        assert!((DI::EMPTY.mul_add(DI::PI, DI::PI)).is_empty());
        assert!((DI::PI.mul_add(DI::EMPTY, DI::PI)).is_empty());
        assert!((DI::PI.mul_add(DI::PI, DI::EMPTY)).is_empty());

        assert!(DI::EMPTY.recip().is_empty());
        assert!(DI::EMPTY.sqrt().is_empty());
        assert!(DI::EMPTY.sqr().is_empty());
    }

    #[test]
    fn nai() {
        assert!((DI::NAI.mul_add(DI::PI, DI::PI)).is_nai());
        assert!((DI::PI.mul_add(DI::NAI, DI::PI)).is_nai());
        assert!((DI::PI.mul_add(DI::PI, DI::NAI)).is_nai());

        assert!(DI::NAI.recip().is_nai());
        assert!(DI::NAI.sqrt().is_nai());
        assert!(DI::NAI.sqr().is_nai());
    }

    #[test]
    fn mul_rev_to_pair() {
        let zero = const_interval!(0., 0.);
        assert_eq!(zero.mul_rev_to_pair(const_interval!(1., 2.)), [I::EMPTY; 2]);
        let pos = const_interval!(0., f64::INFINITY);
        let neg = const_interval!(f64::NEG_INFINITY, 0.);
        assert_eq!(
            I::ENTIRE.mul_rev_to_pair(const_interval!(1., 1.)),
            [neg, pos]
        );
        assert_eq!(pos.mul_rev_to_pair(pos), [I::ENTIRE, I::EMPTY]);
        assert_eq!(neg.mul_rev_to_pair(pos), [I::ENTIRE, I::EMPTY]);
    }

    #[test]
    fn cancel_minus() {
        assert_eq!(
            const_interval!(f64::MAX, f64::MAX).cancel_minus(const_interval!(f64::MIN, f64::MIN)),
            const_interval!(f64::MAX, f64::INFINITY)
        );
        assert_eq!(
            const_interval!(f64::MIN, f64::MIN).cancel_minus(const_interval!(f64::MAX, f64::MAX)),
            const_interval!(f64::NEG_INFINITY, f64::MIN)
        );
        assert_eq!(
            const_interval!(1e292, f64::MAX).cancel_minus(const_interval!(f64::MIN, f64::MIN)),
            const_interval!(f64::MAX, f64::INFINITY)
        );
        assert_eq!(
            const_interval!(f64::MAX, f64::MAX).cancel_minus(const_interval!(f64::MIN, -1e292)),
            I::ENTIRE
        );

        // 2^970, half an ulp of `f64::MAX`. Computing the remainders of the widths with
        // 2Sum instead of Fast2Sum overflowed here, which gave `Interval::ENTIRE`.
        let h = f64::from_bits((970 + 1023) << 52);
        let x = I::try_from((f64::MIN, -3.0 * h)).unwrap();
        assert_eq!(x.cancel_minus(x), const_interval!(0.0, 0.0));
        // The widths overflow and are equal, and a - c = b - d = -(2^1024 - 5 × 2^970).
        let x = I::try_from((f64::MIN, h)).unwrap();
        let y = I::try_from((-3.0 * h, f64::MAX - 2.0 * h)).unwrap();
        assert_eq!(
            x.cancel_minus(y),
            I::try_from((f64::MIN + 2.0 * h, f64::MIN + 4.0 * h)).unwrap()
        );
        assert_eq!(
            x.cancel_plus(-y),
            I::try_from((f64::MIN + 2.0 * h, f64::MIN + 4.0 * h)).unwrap()
        );
    }
}
