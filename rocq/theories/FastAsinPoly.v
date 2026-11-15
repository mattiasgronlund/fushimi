(** * The core of stage 0 of [asin] and [acos]

    [DyadicAtan.fast_asin_poly t] of [Model.v] is [asin t] for [t <= 1/2]
    and [acos t] above, in double-double, without atan, and with no
    division but that of [dd_sqrt] above 1/2, by the reduction of
    CORE-MATH's [cr_asin] and [cr_acos]: [asin t = t
    F(t^2)], and [acos t = 2 asin √s = √u F(s)] for [u = 2 - 2t] and [s =
    u/4] ([AsinSeries.acos_half]), where [F(s) = asin(√s) / √s]. Row [j]
    of [DyadicAtan.ASIN_TABLE], for the integer [j] nearest [256 s],
    holds the Taylor polynomial of [F] at [j / 256], rounded, within
    [11 2^-68] of the first 34 terms of the series of [F] for [|tau| <=
    2^-9 + 2^-55] ([FastAsinTable.asin_table_close]), which
    [fast_asin_poly] evaluates at [tau = s - j/256] ([FastAsinPolyGappa.v])
    and multiplies by [t], or by [√u] in double-double
    ([FastDdSqrt.dd_sqrt_correct]). The parts are in [FastAsinPolyTail.v]
    (the tail after the reduction), [FastAsinPolyRed.v] (the reduction
    above 1/2) and [FastAsinPolyB.v] (the case above 1/2); the case [t <=
    1/2] is [case_A] here. [fast_asin_poly_correct] bounds the result
    relatively, and [fast_asin_poly_fma] shows it is the same with and
    without an FMA. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error Sterbenz.
From Inari Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct DyDriver NearF64
  FastDdSqrt.
From Stdlib Require Import QArith Qreals.
From Inari Require FastExpErr FastExpReduce FastAtanCore ConstTight FastRound.
From Inari Require Import AsinSeries FastAsinTable FastAsinPolyGappa FastAsinPolyTail FastAsinPolyRed
  FastAsinPolyB.

Open Scope R_scope.

(** [lit w H] adds [H : B2R w = n * / d] for the literal [w], as in
    [FastAtanCore.v]. *)
Local Ltac lit w H :=
  let q := eval vm_compute in (ConstTight.B2Q w) in
  assert (H : B2R w = Q2R q)
    by (rewrite ConstTight.B2Q_correct; f_equal; vm_compute; reflexivity);
  unfold Q2R in H; cbn [Qnum Qden] in H.

(** ** The case [t <= 1/2] *)

(** For [2^-27 <= t <= 1/2], [fast_asin_poly t] is [tail t 0 j tau] with
    [p = RN (t^2)], [pe = t^2 - p] exactly (the pair [(t, t)] is exact,
    [prod_exact]), [|pe| <= 2^-55], [s - j/256] exact ([sub_idx]) and [tau
    = RN ((p - j/256) + pe)], so [j/256 + tau = t^2 + delta] with [|delta|
    <= 2^-61]. [tail_correct] (9/2 u t, as [zl = 0]), [asin_poly_lipschitz]
    ([/4 2^-61 t = 2 u t]) and [series_rest] (1/8 u t) sum to [6.625 u t],
    under [7 u asin t] as [asin t >= t], units [u = 2^-64]. *)
Local Lemma case_A :
  forall fma t ch cl,
  is_finite t = true -> bpow radix2 (-27) <= B2R t <= / 2 ->
  DyadicAtan.fast_asin_poly fma t = (ch, cl) ->
  is_finite ch = true /\ is_finite cl = true /\ B2R ch = RN (B2R ch + B2R cl) /\
  Rabs (B2R ch + B2R cl - asin (B2R t)) <= 7 * bpow radix2 (-64) * asin (B2R t).
Proof.
intros fma t ch cl Ft Ht E.
assert (B : bpow radix2 (-27) = / 134217728 /\ bpow radix2 (-28) = / 268435456 /\
            bpow radix2 (-55) = / 36028797018963968 /\
            bpow radix2 (-60) = / 1152921504606846976 /\
            bpow radix2 (-61) = / 2305843009213693952 /\
            bpow radix2 (-64) = / 18446744073709551616 /\
            bpow radix2 (-67) = / 147573952589676412928 /\
            bpow radix2 (-2) = / 4 /\ bpow radix2 (-8) = / 256 /\ bpow radix2 8 = 256)
  by (repeat split; reflexivity).
destruct B as (B27 & B28 & B55 & B60 & B61 & B64 & B67 & B2 & B8 & B8').
rewrite B27 in Ht.
assert (Fh : is_finite DyadicLog.half = true) by reflexivity.
lit DyadicLog.half Hh.
assert (L : Model.le t DyadicLog.half = true)
  by (apply le_iff; [exact Ft | exact Fh | rewrite Hh; lra]).
rewrite (poly_tail_A fma t L) in E. cbv zeta in E.
(* [p = RN (t^2)], and [pe = t^2 - p] exactly. *)
assert (Ht2 : / 18014398509481984 <= B2R t * B2R t <= / 4) by (split; nra).
destruct (FastExpErr.mul_e t t Ft Ft) as (Fp & Ep & _).
{ rewrite Rabs_pos_eq; lra. }
assert (Hp : 0 <= B2R (mul t t) <= / 4).
{ rewrite Ep. split.
  - apply round_ge_generic; [typeclasses eauto .. | apply generic_format_0 | lra].
  - rewrite <- B2. apply round_le_generic; [typeclasses eauto .. | |rewrite B2; lra].
    apply generic_format_bpow. unfold FLT_exp. lia. }
assert (X : Generic.two_prod_is_exact fma t t (mul t t) = true).
{ apply prod_exact; try assumption.
  - rewrite Rabs_pos_eq, B60; lra.
  - rewrite Rabs_pos_eq; lra.
  - rewrite Rabs_pos_eq; lra. }
destruct (two_prod_err_correct fma t t Ft Ft X) as (_ & _ & _ & Fpe & Epe).
set (p := mul t t) in *.
set (pe := Generic.two_prod_err fma t t p) in *.
assert (Hpe : Rabs (B2R pe) <= / 36028797018963968).
{ rewrite <- B55, Epe, Ep, Rabs_minus_sym.
  apply (FastExpReduce.RN_err_le _ (-2)); [lia | reflexivity | rewrite Rabs_pos_eq, B2; lra]. }
(* The index [j] nearest [256 p], and [d = p - j/256] exactly. *)
assert (FW : is_finite (from_bits 0x4070000000000000) = true) by reflexivity.
lit (from_bits 0x4070000000000000) HW.
assert (HW' : B2R (from_bits 0x4070000000000000) = bpow radix2 8) by (rewrite HW, B8'; lra).
pose proof (idx p _ 8 Fp FW HW' ltac:(lia) ltac:(rewrite B8'; lra)) as I.
cbv zeta in I. destruct I as (j & Hj & Hjr & Hlow & Fjd & Ejd).
rewrite B8' in Hjr.
rewrite Hlow in E.
destruct (sub_idx p _ j Fp Fjd ltac:(lra) ltac:(lia) Ejd Hjr) as (Fd & Ed).
set (d := sub p _) in *.
assert (Hd : Rabs (B2R d) <= / 512)
  by (rewrite Ed; apply Rabs_le_inv in Hjr; apply Rabs_le; lra).
(* [tau = RN (d + pe)], with [|tau| <= /512 + 2^-55] and [|tau - (d +
   pe)| <= 2^-61], as [|d + pe| <= 2^-8]. *)
apply Rabs_le_inv in Hd. apply Rabs_le_inv in Hpe.
destruct (FastExpErr.add_e d pe Fd Fpe) as (Ftau & Etau & _).
{ apply Rabs_le. lra. }
assert (Htau : Rabs (B2R (add d pe)) <= / 512 + bpow radix2 (-55)).
{ rewrite Etau. apply abs_round_le_generic; [typeclasses eauto .. | |].
  - replace (/ 512 + bpow radix2 (-55)) with (IZR 70368744177665 * bpow radix2 (-55))
      by (rewrite B55; lra).
    apply FastExpReduce.format_mult; [reflexivity | lia].
  - rewrite B55. apply Rabs_le. lra. }
assert (Hdel : Rabs (B2R (add d pe) - (B2R d + B2R pe)) <= bpow radix2 (-61)).
{ rewrite Etau. apply (FastExpReduce.RN_err_le _ (-8)); [lia | reflexivity |].
  rewrite B8. apply Rabs_le. lra. }
rewrite B61 in Hdel.
set (tau := add d pe) in *.
(* [tail_correct], with [zl = 0]. *)
pose proof (tail_correct fma t zero j tau ch cl Ft eq_refl Ftau) as T.
cbv zeta in T.
destruct T as (Fch & Fcl & Ech & _ & _ & HT); try assumption.
{ rewrite B28. lra. }
{ change (B2R zero) with 0. rewrite Rabs_R0. apply Rmult_le_pos; [apply bpow_ge_0 | lra]. }
specialize (HT eq_refl).
split; [exact Fch|]. split; [exact Fcl|]. split; [exact Ech|].
(* [asin_poly_lipschitz] at [j/256 + tau = t^2 + delta]. *)
assert (Ea : IZR j / 256 + B2R tau - B2R t ^ 2 = B2R tau - (B2R d + B2R pe))
  by (rewrite Ed, Epe; ring).
apply Rabs_le_inv in Hdel.
pose proof (asin_poly_lipschitz 34 (IZR j / 256 + B2R tau) (B2R t ^ 2)) as HL.
rewrite Ea in HL.
assert (Et2 : B2R t ^ 2 = B2R t * B2R t) by ring.
specialize (HL ltac:(rewrite <- Et2 in Ht2; lra) ltac:(rewrite Et2; lra)).
assert (HL' : Rabs (asin_poly 34 (IZR j / 256 + B2R tau) - asin_poly 34 (B2R t ^ 2)) <=
  / 4 * / 2305843009213693952) by (apply Rle_trans with (1 := HL); apply Rmult_le_compat_l;
  [lra | apply Rabs_le; lra]).
pose proof (scale_le (B2R t) _ _ ltac:(lra) HL') as M.
(* The series. *)
pose proof (series_rest (B2R t) ltac:(lra)) as S. rewrite B67 in S.
pose proof (asin_ge (B2R t) ltac:(lra)) as G.
rewrite B64 in HT |- *. apply Rabs_le_inv in HT. apply Rabs_le. lra.
Qed.

(** ** The theorems *)

(** [case_A] for [t <= 1/2] and [FastAsinPolyB.case_B] above. *)
Theorem fast_asin_poly_correct :
  forall fma t ch cl,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < 1 ->
  DyadicAtan.fast_asin_poly fma t = (ch, cl) ->
  is_finite ch = true /\ is_finite cl = true /\ B2R ch = RN (B2R ch + B2R cl) /\
  let V := if Rle_bool (B2R t) (/ 2) then asin (B2R t) else acos (B2R t) in
  Rabs (B2R ch + B2R cl - V) <= 7 * bpow radix2 (-64) * V.
Proof.
intros fma t ch cl Ft Ht E.
destruct (Rle_bool_spec (B2R t) (/ 2)) as [L | L].
- exact (case_A fma t ch cl Ft (conj (proj1 Ht) L) E).
- exact (case_B fma t ch cl Ft (conj L (proj2 Ht)) E).
Qed.

(** Only [Generic.two_prod_err] and [Fast.dd_sqrt] depend on the FMA. For
    [t <= 1/2], the pair [(t, t)] is exact ([prod_exact]), so its error is
    the same [f64] either way ([FastRound.two_prod_err_fma_eq]); for [t >
    1/2], [Fast.dd_sqrt] is ([FastDdSqrt.dd_sqrt_fma]). The rest is
    [tail_fma], with [j] in [[0, 64]] from [idx] or [reduce_B]. *)
Theorem fast_asin_poly_fma :
  forall t,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < 1 ->
  DyadicAtan.fast_asin_poly true t = DyadicAtan.fast_asin_poly false t.
Proof.
intros t Ft Ht.
assert (B : bpow radix2 (-27) = / 134217728 /\ bpow radix2 (-28) = / 268435456 /\
            bpow radix2 (-60) = / 1152921504606846976 /\
            bpow radix2 (-2) = / 4 /\ bpow radix2 8 = 256)
  by (repeat split; reflexivity).
destruct B as (B27 & B28 & B60 & B2 & B8).
destruct (Rle_bool_spec (B2R t) (/ 2)) as [L | L].
- (* [t <= 1/2]: [p = RN (t^2)] is in [[0, 1/4]], as in [case_A]. *)
  rewrite B27 in Ht.
  assert (Fh : is_finite DyadicLog.half = true) by reflexivity.
  lit DyadicLog.half Hh.
  assert (LA : Model.le t DyadicLog.half = true)
    by (apply le_iff; [exact Ft | exact Fh | rewrite Hh; lra]).
  rewrite (poly_tail_A true t LA), (poly_tail_A false t LA). cbv zeta.
  assert (Ht2 : / 18014398509481984 <= B2R t * B2R t <= / 4) by (split; nra).
  destruct (FastExpErr.mul_e t t Ft Ft) as (Fp & Ep & _).
  { rewrite Rabs_pos_eq; lra. }
  assert (Hp : 0 <= B2R (mul t t) <= / 4).
  { rewrite Ep. split.
    - apply round_ge_generic; [typeclasses eauto .. | apply generic_format_0 | lra].
    - rewrite <- B2. apply round_le_generic; [typeclasses eauto .. | |rewrite B2; lra].
      apply generic_format_bpow. unfold FLT_exp. lia. }
  assert (Hpr : bpow radix2 (-60) <= Rabs (B2R t * B2R t) <= 4)
    by (rewrite Rabs_pos_eq, B60; lra).
  assert (Hta : Rabs (B2R t) <= 2) by (rewrite Rabs_pos_eq; lra).
  rewrite (FastRound.two_prod_err_fma_eq t t Ft Ft (prod_exact true t t Ft Ft Hpr Hta Hta)
    (prod_exact false t t Ft Ft Hpr Hta Hta)).
  (* The index [j] nearest [256 p] is in [[0, 64]]. *)
  assert (FW : is_finite (from_bits 0x4070000000000000) = true) by reflexivity.
  lit (from_bits 0x4070000000000000) HW.
  assert (HW' : B2R (from_bits 0x4070000000000000) = bpow radix2 8) by (rewrite HW, B8; lra).
  pose proof (idx (mul t t) _ 8 Fp FW HW' ltac:(lia) ltac:(rewrite B8; lra)) as I.
  cbv zeta in I. destruct I as (j & Hj & _ & Hlow & _).
  rewrite Hlow.
  apply tail_fma; [exact Ft | rewrite B28; lra | exact Hj].
- (* [t > 1/2]: [u = 2 - 2t] is in [[2^-52, 1)], and [j] in [[0, 64]]. *)
  pose proof (reduce_B t Ft (conj L (proj2 Ht))) as R. cbv zeta in R.
  destruct R as (LB & Fu & _ & Hu & Hj & _).
  assert (Hu' : bpow radix2 (-52) <= B2R (sub DyadicExp.two (mul DyadicExp.two t)) <= 1)
    by lra.
  assert (B' : bpow radix2 (-900) <= bpow radix2 (-52) /\ 1 <= bpow radix2 900)
    by (split; [apply bpow_le; lia | apply (bpow_le radix2 0); lia]).
  destruct (Fast.dd_sqrt false (sub DyadicExp.two (mul DyadicExp.two t)) zero)
    as (zh, zl) eqn:Esq.
  assert (Esq' : Fast.dd_sqrt true (sub DyadicExp.two (mul DyadicExp.two t)) zero = (zh, zl)).
  { rewrite dd_sqrt_fma; [exact Esq | exact Fu | reflexivity | split; lra]. }
  destruct (sqrt_B false _ zh zl Fu Hu' Esq) as (Fzh & _ & _ & _ & Hzh).
  rewrite (poly_tail_B true t zh zl LB Esq'), (poly_tail_B false t zh zl LB Esq). cbv zeta.
  apply tail_fma; assumption.
Qed.
