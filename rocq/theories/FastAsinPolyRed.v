(** * The reduction of [fast_asin_poly] above 1/2

    For [1/2 < t < 1], [DyadicAtan.fast_asin_poly] of [Model.v] takes [u =
    2 - 2t] exactly, the index [j] nearest [64 u = 256 s] for [s = u/4],
    and [tau = s - j/256] exactly ([reduce_B]), and [zh + zl = √u] in
    double-double ([sqrt_B], from [FastDdSqrt.dd_sqrt_correct]). Both
    [FastAsinPolyB.case_B] and [FastAsinPoly.fast_asin_poly_fma] use
    them. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error Sterbenz.
From Fushimi Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct DyDriver NearF64
  FastDdSqrt.
From Stdlib Require Import QArith Qreals.
From Fushimi Require FastExpErr FastExpReduce FastAtanCore ConstTight FastRound.
From Fushimi Require Import AsinSeries FastAsinTable FastAsinPolyTail.

Open Scope R_scope.

(** [lit w H] adds [H : B2R w = n * / d] for the literal [w], as in
    [FastAtanCore.v]. *)
Local Ltac lit w H :=
  let q := eval vm_compute in (ConstTight.B2Q w) in
  assert (H : B2R w = Q2R q)
    by (rewrite ConstTight.B2Q_correct; f_equal; vm_compute; reflexivity);
  unfold Q2R in H; cbn [Qnum Qden] in H.

(** A rounding to nearest at or above [2^-1022] is within [2^-53] of the
    result, as in [FastAhypAsinh.v]. *)
Local Lemma rel_half_ulp :
  forall x, bpow radix2 (-1022) <= Rabs (RN x) ->
  Rabs (RN x - x) <= bpow radix2 (-53) * Rabs (RN x).
Proof.
intros x Hx.
pose proof (ulp_FLT_le radix2 (-1074) 53 (RN x) Hx) as H.
change (1 - 53)%Z with (-52)%Z in H.
assert (HM : bpow radix2 (-53) = / 2 * bpow radix2 (-52))
  by (cbn [bpow radix_val radix2]; lra).
apply Rle_trans with (/ 2 * ulp radix2 fexp64 (RN x)).
- apply error_le_half_ulp_round; typeclasses eauto.
- rewrite HM. lra.
Qed.

(** [√u] in double-double for [2^-52 <= u <= 1]: [zh + zl] within [2^-100
    √u] ([FastDdSqrt.dd_sqrt_correct] with [al = 0]), [|zl| <= 2^-53 zh]
    as [zh = RN (zh + zl)], and [2^-28 <= zh <= 2], as [tail_correct]
    needs. *)
Lemma sqrt_B :
  forall fma u zh zl,
  is_finite u = true -> bpow radix2 (-52) <= B2R u <= 1 ->
  Fast.dd_sqrt fma u zero = (zh, zl) ->
  is_finite zh = true /\ is_finite zl = true /\
  Rabs (B2R zh + B2R zl - sqrt (B2R u)) <= bpow radix2 (-100) * sqrt (B2R u) /\
  Rabs (B2R zl) <= bpow radix2 (-53) * B2R zh /\ bpow radix2 (-28) <= B2R zh <= 2.
Proof.
intros fma u zh zl Fu Hu E.
(* [dd_sqrt_correct] with [al = 0]. *)
assert (A1 : bpow radix2 (-900) <= B2R u <= bpow radix2 900).
{ assert (L1 : bpow radix2 (-900) <= bpow radix2 (-52)) by (apply bpow_le; lia).
  assert (L2 : 1 <= bpow radix2 900) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
  lra. }
assert (A2 : Rabs (B2R zero) <= bpow radix2 (-52) * B2R u).
{ change (B2R zero) with 0. rewrite Rabs_R0.
  apply Rmult_le_pos; [apply bpow_ge_0 | pose proof (bpow_ge_0 radix2 (-52)); lra]. }
destruct (dd_sqrt_correct fma u zero zh zl Fu eq_refl A1 A2 E) as (Fh & Fl & Hr & He).
change (B2R zero) with 0 in He. rewrite Rplus_0_r in He.
(* [2^-26 <= √u <= 1], so [zh + zl] is in [[2^-27, 2]]. *)
assert (S1 : bpow radix2 (-26) <= sqrt (B2R u)).
{ rewrite <- (sqrt_bpow radix2 (-26)). apply sqrt_le_1_alt. exact (proj1 Hu). }
assert (S2 : sqrt (B2R u) <= 1) by (rewrite <- sqrt_1; apply sqrt_le_1_alt; lra).
assert (HM : bpow radix2 (-27) = / 2 * bpow radix2 (-26) /\ bpow radix2 (-100) <= / 2 /\
  bpow radix2 (-1022) <= bpow radix2 (-28) /\ bpow radix2 (-28) <= bpow radix2 (-27) /\
  0 <= bpow radix2 (-28))
  by (cbn [bpow radix_val radix2]; repeat split; lra).
destruct HM as (HM27 & HM100 & HM1022 & HM28 & HM0).
assert (P : bpow radix2 (-100) * sqrt (B2R u) <= / 2 * sqrt (B2R u))
  by (apply Rmult_le_compat_r; lra).
pose proof (Rabs_le_inv _ _ He) as He'.
assert (Z1 : bpow radix2 (-27) <= B2R zh + B2R zl <= 2) by lra.
(* [zh = RN (zh + zl)] keeps those bounds, as [2^-27] and [2] are
   floats. *)
assert (Lo : bpow radix2 (-27) <= B2R zh).
{ rewrite Hr. apply round_ge_generic; try typeclasses eauto; [|lra].
  apply generic_format_FLT_bpow; [easy | lia]. }
assert (Hi : B2R zh <= 2).
{ rewrite Hr. apply round_le_generic; try typeclasses eauto; [|lra].
  exact FastRound.format_two. }
(* [zl = (zh + zl) - RN (zh + zl)] is the error of a rounding at or above
   [2^-1022]. *)
pose proof (rel_half_ulp (B2R zh + B2R zl)) as RE.
rewrite <- Hr in RE.
rewrite (Rabs_pos_eq (B2R zh)) in RE by lra.
replace (B2R zh - (B2R zh + B2R zl)) with (- B2R zl) in RE by ring.
rewrite Rabs_Ropp in RE.
assert (RE' : Rabs (B2R zl) <= bpow radix2 (-53) * B2R zh) by (apply RE; lra).
repeat split; try assumption; lra.
Qed.

(** The reduction for [1/2 < t < 1]: [fast_asin_poly] takes the second
    branch, [u = 2 - 2t] exactly with [2^-52 <= u < 1], [j] is the integer
    nearest [64 u] in [[0, 64]], and [tau = u/4 - j/256] exactly, with
    [|tau| <= 1/512]. The [let]s are the terms of [poly_tail_B]. *)
Lemma reduce_B :
  forall t,
  is_finite t = true -> / 2 < B2R t < 1 ->
  let u := sub DyadicExp.two (mul DyadicExp.two t) in
  let ks := add (mul u (from_bits 0x4050000000000000)) DyadicExp.shifter in
  let jd := sub ks DyadicExp.shifter in
  let j := DyadicExp.low_i32 (to_bits ks) in
  let tau := sub (mul DyadicAtan.quarter u) (mul jd (from_bits 0x3f70000000000000)) in
  Model.le t DyadicLog.half = false /\
  is_finite u = true /\ B2R u = 2 - 2 * B2R t /\ bpow radix2 (-52) <= B2R u < 1 /\
  (0 <= j <= 64)%Z /\ is_finite tau = true /\
  B2R tau = B2R u / 4 - IZR j / 256 /\ Rabs (B2R tau) <= / 512.
Proof.
intros t Ft Ht. cbv zeta.
lit DyadicLog.half Hh. lit DyadicExp.two H2. lit DyadicAtan.quarter Hq.
assert (H2' : B2R DyadicExp.two = 2) by lra.
assert (Hq' : B2R DyadicAtan.quarter = / 4) by lra.
assert (Fh : is_finite DyadicLog.half = true) by reflexivity.
assert (F2 : is_finite DyadicExp.two = true) by reflexivity.
assert (Fq : is_finite DyadicAtan.quarter = true) by reflexivity.
assert (FW : is_finite (from_bits 0x4050000000000000) = true) by reflexivity.
assert (HW : B2R (from_bits 0x4050000000000000) = bpow radix2 6).
{ lit (from_bits 0x4050000000000000) HW. rewrite HW.
  change (bpow radix2 6) with 64. lra. }
(* [t > 1/2], so the second branch. *)
assert (Le : Model.le t DyadicLog.half = false).
{ destruct (Model.le t DyadicLog.half) eqn:E; [|reflexivity].
  pose proof (proj1 (le_iff t DyadicLog.half Ft Fh) E). lra. }
(* [t] is a float below 1, so [t <= pred 1 = 1 - 2^-53]. *)
assert (Ht1 : B2R t <= 1 - bpow radix2 (-53)).
{ rewrite <- (FastRound.pred_lo 1 FastRound.format_one) by lra.
  apply (pred_ge_gt radix2 fexp64);
    [apply generic_format_B2R | exact FastRound.format_one | lra]. }
(* [2t] is exact. *)
assert (M2 : Rabs (B2R DyadicExp.two * B2R t) <= MAX)
  by (apply FastExpReduce.le_MAX, Rabs_le; rewrite H2'; lra).
destruct (mul_below_max DyadicExp.two t F2 Ft M2) as (Fm & Em & _).
assert (E2 : B2R (mul DyadicExp.two t) = 2 * B2R t).
{ rewrite Em, H2'.
  replace (2 * B2R t) with (B2R t * bpow radix2 1)
    by (change (bpow radix2 1) with 2; ring).
  apply round_generic; [typeclasses eauto|].
  apply mult_bpow_pos_exact_FLT; [apply generic_format_B2R | lia]. }
(* [u = 2 - 2t] is exact by Sterbenz's lemma, as [1 < 2t < 2]. *)
assert (MU : Rabs (B2R DyadicExp.two - B2R (mul DyadicExp.two t)) <= MAX)
  by (apply FastExpReduce.le_MAX, Rabs_le; rewrite H2', E2; lra).
destruct (sub_below_max DyadicExp.two (mul DyadicExp.two t) F2 Fm MU) as (FU & HU & _).
assert (GU : generic_format radix2 fexp64 (B2R DyadicExp.two - B2R (mul DyadicExp.two t))).
{ apply sterbenz; try typeclasses eauto; try apply generic_format_B2R.
  rewrite H2', E2. lra. }
assert (EU : B2R (sub DyadicExp.two (mul DyadicExp.two t)) = 2 - 2 * B2R t)
  by (rewrite HU, round_generic by first [exact GU | typeclasses eauto]; lra).
set (u := sub DyadicExp.two (mul DyadicExp.two t)) in *.
assert (B52 : bpow radix2 (-52) = 2 * bpow radix2 (-53) /\ 0 <= bpow radix2 (-52))
  by (cbn [bpow radix_val radix2]; lra).
assert (Bu : bpow radix2 (-52) <= B2R u < 1) by lra.
(* [j] is the integer nearest [64 u], and [jd 2^-8 = j/256]. *)
assert (H64 : 0 <= B2R u * bpow radix2 6 <= 64)
  by (change (bpow radix2 6) with 64; lra).
pose proof (idx u (from_bits 0x4050000000000000) 6 FU FW HW ltac:(lia) H64) as IX.
cbv zeta in IX. destruct IX as (j & Hj & Hr & Ej & Fy & Ey).
rewrite Ej.
(* [u/4] is exact, as [u >= 2^-52] is far from the subnormals. *)
assert (MS : Rabs (B2R DyadicAtan.quarter * B2R u) <= MAX)
  by (apply FastExpReduce.le_MAX, Rabs_le; rewrite Hq'; lra).
destruct (mul_below_max DyadicAtan.quarter u Fq FU MS) as (Fs & Es & _).
assert (GS : generic_format radix2 fexp64 (B2R u * bpow radix2 (-2))).
{ apply mult_bpow_exact_FLT; [apply generic_format_B2R|].
  assert (Mu : (-51 <= mag radix2 (B2R u))%Z).
  { apply mag_ge_bpow. rewrite Rabs_pos_eq by lra.
    change (-51 - 1)%Z with (-52)%Z. lra. }
  lia. }
assert (ES : B2R (mul DyadicAtan.quarter u) = B2R u / 4).
{ rewrite Es, Hq'.
  replace (/ 4 * B2R u) with (B2R u * bpow radix2 (-2))
    by (change (bpow radix2 (-2)) with (/ 4); ring).
  rewrite round_generic by first [exact GS | typeclasses eauto].
  change (bpow radix2 (-2)) with (/ 4). lra. }
(* [tau = u/4 - j/256] is exact, as [|256 (u/4) - j| <= 1/2]. *)
assert (Hs : 0 <= B2R (mul DyadicAtan.quarter u) <= 1) by (rewrite ES; lra).
change (bpow radix2 6) with 64 in Hr.
assert (Hr' : Rabs (B2R (mul DyadicAtan.quarter u) * 256 - IZR j) <= / 2)
  by (rewrite ES; replace (B2R u / 4 * 256) with (B2R u * 64) by lra; exact Hr).
destruct (sub_idx _ _ j Fs Fy Hs (proj1 Hj) Ey Hr') as (FT & ET).
rewrite ET.
apply Rabs_le_inv in Hr.
split; [exact Le|]. split; [exact FU|]. split; [exact EU|]. split; [exact Bu|].
split; [exact Hj|]. split; [exact FT|]. split; [lra|].
apply Rabs_le. lra.
Qed.
