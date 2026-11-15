(** * [fast_asin_poly] above 1/2

    For [1/2 < t < 1], [DyadicAtan.fast_asin_poly] of [Model.v] is [tail]
    ([FastAsinPolyTail.v]) at the [j] and [tau] of
    [FastAsinPolyRed.reduce_B], times [zh + zl = √u]
    ([FastAsinPolyRed.sqrt_B]). As [acos t = 2 asin w] for [w = √s =
    √((1 - t)/2)] ([AsinSeries.acos_half]), and [√u = 2 w], [case_B]
    bounds the result relatively to [acos t]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error Sterbenz.
From Inari Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct DyDriver NearF64
  FastDdSqrt.
From Stdlib Require Import QArith Qreals.
From Inari Require FastExpErr FastExpReduce FastAtanCore ConstTight FastRound.
From Inari Require Import AsinSeries FastAsinTable FastAsinPolyTail FastAsinPolyRed.

Open Scope R_scope.

(** [fast_asin_poly t] is [acos t] within [7 2^-64 acos t] for [1/2 < t <
    1]. In units [u = 2^-64]: [reduce_B] gives [u' = 2 - 2t] and [j/256 +
    tau = u'/4] exactly, and [sqrt_B] gives [zh + zl] within [2^-100 √u'],
    with [|zl| <= 2^-53 zh], so [zh <= (1 + 2^-51) √u']. [tail_correct]
    puts [ch + cl] within [25/4 u zh] of [(zh + zl) P] for [P = asin_poly
    34 (u'/4)]. With [w = √(u'/4)], [√u' = 2 w] and [acos t = 2 asin w]
    ([acos_half]). The error of [zh + zl] adds [2^-100 2w 2], as [|P| <=
    2], and the rest of the series ([series_rest]) [2 2^-67 w = 1/8 u 2w],
    so the total is about [6.375 u 2w], under [7 u acos t] as [w <= asin
    w] ([asin_ge]). *)
Lemma case_B :
  forall fma t ch cl,
  is_finite t = true -> / 2 < B2R t < 1 ->
  DyadicAtan.fast_asin_poly fma t = (ch, cl) ->
  is_finite ch = true /\ is_finite cl = true /\ B2R ch = RN (B2R ch + B2R cl) /\
  Rabs (B2R ch + B2R cl - acos (B2R t)) <= 7 * bpow radix2 (-64) * acos (B2R t).
Proof.
intros fma t ch cl Ft Ht E.
assert (B : bpow radix2 (-28) = / 268435456 /\
            bpow radix2 (-52) = / 4503599627370496 /\
            bpow radix2 (-53) = / 9007199254740992 /\
            bpow radix2 (-55) = / 36028797018963968 /\
            bpow radix2 (-64) = / 18446744073709551616 /\
            bpow radix2 (-67) = / 147573952589676412928 /\
            bpow radix2 (-100) = / 1267650600228229401496703205376)
  by (repeat split; reflexivity).
destruct B as (B28 & B52 & B53 & B55 & B64 & B67 & B100).
(* The reduction: the float [u] is [u' = 2 - 2t], and [j/256 + tau = u/4]
   exactly. *)
pose proof (reduce_B t Ft Ht) as R. cbv zeta in R.
set (u := sub DyadicExp.two (mul DyadicExp.two t)) in *.
set (ks := add (mul u (from_bits 0x4050000000000000)) DyadicExp.shifter) in *.
set (jd := sub ks DyadicExp.shifter) in *.
set (j := DyadicExp.low_i32 (to_bits ks)) in *.
set (tau := sub (mul DyadicAtan.quarter u) (mul jd (from_bits 0x3f70000000000000))) in *.
destruct R as (L & Fu & Eu & Hu & Hj & Ftau & Etau & Htau).
(* [zh + zl = √u] in double-double. *)
destruct (Fast.dd_sqrt fma u zero) as (zh, zl) eqn:Esq.
destruct (sqrt_B fma u zh zl Fu ltac:(rewrite B52 in Hu |- *; lra) Esq)
  as (Fzh & Fzl & Hz & Hzl & Hzh).
(* The tail, at [j/256 + tau = u/4]. *)
rewrite (poly_tail_B fma t zh zl L Esq) in E. cbv zeta in E.
change (tail fma zh zl j tau = (ch, cl)) in E.
assert (Htau' : Rabs (B2R tau) <= / 512 + bpow radix2 (-55))
  by (pose proof (bpow_ge_0 radix2 (-55)); lra).
pose proof (tail_correct fma zh zl j tau ch cl Fzh Fzl Ftau Hzh Hzl Htau' Hj E) as T.
cbv zeta in T. destruct T as (Fch & Fcl & Ech & HP & HT & _).
split; [exact Fch|]. split; [exact Fcl|]. split; [exact Ech|].
assert (Es : IZR j / 256 + B2R tau = B2R u / 4) by (rewrite Etau; ring).
rewrite Es in HP, HT.
(* [w = √(u/4)]: [√u = 2 w], [w <= 1/2] and [acos t = 2 asin w]. *)
rewrite B52 in Hu.
set (w := sqrt (B2R u / 4)).
assert (Hw2 : w * w = B2R u / 4) by (unfold w; apply sqrt_sqrt; lra).
assert (Hw0 : 0 <= w) by (unfold w; apply sqrt_pos).
assert (Hsu : sqrt (B2R u) = 2 * w) by (apply sqrt_lem_1; [lra | lra | nra]).
assert (Hw : w <= / 2) by nra.
assert (A : acos (B2R t) = 2 * asin w).
{ unfold w. rewrite Eu. replace ((2 - 2 * B2R t) / 4) with ((1 - B2R t) / 2) by field.
  apply acos_half. lra. }
(* The series: [0 <= asin w - w P <= 2^-67 w], and [w <= asin w]. *)
pose proof (series_rest w (conj Hw0 Hw)) as S.
replace (w ^ 2) with (B2R u / 4) in S by (rewrite <- Hw2; ring).
pose proof (asin_ge w (conj Hw0 Hw)) as G.
(* The sum: [(zh + zl - 2 w) P] is within [2^-100 2w 2] ([prod_le]). *)
set (P := asin_poly 34 (B2R u / 4)) in *.
rewrite Hsu in Hz.
pose proof (prod_le _ _ _ _ Hz HP) as M.
rewrite B100 in Hz, M. rewrite B53 in Hzl. rewrite B67 in S.
apply Rabs_le_inv in Hz. apply Rabs_le_inv in Hzl. apply Rabs_le_inv in HT.
rewrite B64 in HT |- *. rewrite A. apply Rabs_le. lra.
Qed.
