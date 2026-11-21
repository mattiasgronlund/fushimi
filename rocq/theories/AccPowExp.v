(** The bounds on [e^t] of the accurate phase of x^y
    ([DyadicPow.acc_exp], [fn acc_exp] of [src/dyadic/pow/acc.rs]) for
    each [t] between its bounds [tl] and [th] at 2^-115: [e^t = 2^(k/4096)
    e^w] for [w = t - k ln 2 / 4096] in [[0, 2^-12]], [2^(k/4096) =
    2^(k >> 12) 2^(j1/64) 2^(j2/4096)] from the tables of
    [AccPowTables.v], and [e^w] by Horner's scheme on its Taylor polynomial
    of degree 8, rounded down and up at 2^-127 ([AccPowArith.v]). *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core.
From Fushimi Require Import Model Elementary AccPowArith AccPowTables HypTaylor.

Open Scope R_scope.

(** ** Integers scaled by powers of 2 *)

(** [M] at [2^e] is at most [N] at [2^(e - s)] where [2^s M <= N], and at
    least it where [N <= 2^s M]: the roundings down and up of a division
    by [2^s]. *)
Local Lemma scale_dn :
  forall N M s eN e, (0 <= s)%Z -> eN = (e - s)%Z -> (2 ^ s * M <= N)%Z ->
  IZR M * bpow radix2 e <= IZR N * bpow radix2 eN.
Proof.
intros N M s eN e Hs -> H.
assert (HP : bpow radix2 s = IZR (2 ^ s)) by (symmetry; exact (IZR_Zpower radix2 s Hs)).
assert (HB : bpow radix2 e = bpow radix2 (e - s) * bpow radix2 s)
  by (rewrite <- bpow_plus; f_equal; ring).
apply IZR_le in H. rewrite mult_IZR in H.
pose proof (bpow_gt_0 radix2 (e - s)).
rewrite HB, HP.
replace (IZR M * (bpow radix2 (e - s) * IZR (2 ^ s)))
  with (IZR (2 ^ s) * IZR M * bpow radix2 (e - s)) by ring.
apply Rmult_le_compat_r; lra.
Qed.

Local Lemma scale_up :
  forall N M s eN e, (0 <= s)%Z -> eN = (e - s)%Z -> (N <= 2 ^ s * M)%Z ->
  IZR N * bpow radix2 eN <= IZR M * bpow radix2 e.
Proof.
intros N M s eN e Hs -> H.
assert (HP : bpow radix2 s = IZR (2 ^ s)) by (symmetry; exact (IZR_Zpower radix2 s Hs)).
assert (HB : bpow radix2 e = bpow radix2 (e - s) * bpow radix2 s)
  by (rewrite <- bpow_plus; f_equal; ring).
apply IZR_le in H. rewrite mult_IZR in H.
pose proof (bpow_gt_0 radix2 (e - s)).
rewrite HB, HP.
replace (IZR M * (bpow radix2 (e - s) * IZR (2 ^ s)))
  with (IZR (2 ^ s) * IZR M * bpow radix2 (e - s)) by ring.
apply Rmult_le_compat_r; lra.
Qed.

(** The rounding up of [N / 2^s] in [mul_up], and that of [N / 2^128] in
    [acc_exp], which adds 1 where the low 128 bits are not all 0. *)
Local Lemma div_up_ge :
  forall N s, (0 <= s)%Z -> (N <= 2 ^ s * ((N + 2 ^ s - 1) / 2 ^ s))%Z.
Proof.
intros N s Hs.
assert (HP : (0 < 2 ^ s)%Z) by (apply Z.pow_pos_nonneg; lia).
pose proof (Z.div_mod (N + 2 ^ s - 1) (2 ^ s) ltac:(lia)).
pose proof (Z.mod_pos_bound (N + 2 ^ s - 1) (2 ^ s) HP).
lia.
Qed.

Local Lemma div_ceil_ge :
  forall N, (N <= 2 ^ 128 * (N / 2 ^ 128 + (if N mod 2 ^ 128 =? 0 then 0 else 1)))%Z.
Proof.
intros N.
pose proof (Z.div_mod N (2 ^ 128) ltac:(lia)).
pose proof (Z.mod_pos_bound N (2 ^ 128) ltac:(lia)).
destruct (N mod 2 ^ 128 =? 0)%Z eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; lia.
Qed.

(** A product of two scaled integers is their product, scaled. *)
Local Lemma prod_scaled :
  forall a b ea eb,
  IZR (a * b) * bpow radix2 (ea + eb) = (IZR a * bpow radix2 ea) * (IZR b * bpow radix2 eb).
Proof. intros a b ea eb. rewrite mult_IZR, bpow_plus. ring. Qed.

(** Bounds on a real at the same scale are in order. *)
Local Lemma le_of_scaled :
  forall a b s x, IZR a * bpow radix2 s <= x <= IZR b * bpow radix2 s -> (a <= b)%Z.
Proof.
intros a b s x H. apply le_IZR.
apply (Rmult_le_reg_r (bpow radix2 s)); [apply bpow_gt_0 | lra].
Qed.

(** [checked_i] returns its argument. *)
Local Lemma checked_i_eq : forall w z z', checked_i w z = Some z' -> z' = z.
Proof.
intros w z z' H. unfold checked_i in H.
destruct ((- 2 ^ (w - 1) <=? z) && (z <? 2 ^ (w - 1)))%Z; [|discriminate H].
injection H as <-. reflexivity.
Qed.

(** [k = 4096 (k >> 12) + 64 j1 + j2] for [j1 = (k >> 6) & 63] and [j2 = k
    & 63], also for a negative [k], as [>>] rounds toward -∞ and [&] reads
    [k] in two's complement. *)
Local Lemma k_split :
  forall k,
  k = (4096 * Z.shiftr k 12 + 64 * Z.land (Z.shiftr k 6) 63 + Z.land k 63)%Z /\
  (0 <= Z.land (Z.shiftr k 6) 63 < 64)%Z /\ (0 <= Z.land k 63 < 64)%Z.
Proof.
intros k.
rewrite !Z.shiftr_div_pow2 by lia.
change 63%Z with (Z.ones 6).
rewrite !Z.land_ones by lia.
replace (k / 2 ^ 12)%Z with (k / 2 ^ 6 / 2 ^ 6)%Z by (rewrite Z.div_div by lia; reflexivity).
change (2 ^ 6)%Z with 64%Z.
pose proof (Z.div_mod k 64 ltac:(lia)). pose proof (Z.div_mod (k / 64) 64 ltac:(lia)).
pose proof (Z.mod_pos_bound k 64 ltac:(lia)). pose proof (Z.mod_pos_bound (k / 64) 64 ltac:(lia)).
lia.
Qed.

(** ** The coefficients and Horner's scheme *)

(** [n!] in [Z], so that the factorials of literals compute in binary, as
    in [HypTaylor.v]. *)
Local Fixpoint zfact (n : nat) : Z :=
  match n with O => 1%Z | S m => (Z.of_nat n * zfact m)%Z end.

Local Lemma fact_R : forall n, INR (fact n) = IZR (zfact n).
Proof.
induction n as [|n IH]; [reflexivity|].
rewrite fact_simpl, mult_INR, IH. cbn [zfact]. rewrite mult_IZR, <- INR_IZR_INZ. reflexivity.
Qed.

(** [exp_d j] is [2^127 / j!] rounded down for [j <= 8], checked by
    computation. *)
Local Definition exp_d_okb (j : nat) : bool :=
  (0 <=? DyadicPow.exp_d j)%Z && (DyadicPow.exp_d j <=? 2 ^ 127)%Z && (1 <=? zfact j)%Z &&
  (DyadicPow.exp_d j * zfact j <=? 2 ^ 127)%Z && (2 ^ 127 <? (DyadicPow.exp_d j + 1) * zfact j)%Z.

Local Lemma exp_d_bounds :
  forall j, (j <= 8)%nat ->
  (0 <= DyadicPow.exp_d j <= 2 ^ 127)%Z /\
  IZR (DyadicPow.exp_d j) * bpow radix2 (-127) <= / INR (fact j) <=
    IZR (DyadicPow.exp_d j + 1) * bpow radix2 (-127).
Proof.
intros j Hj.
assert (Hb : exp_d_okb j = true).
{ do 9 (destruct j as [|j]; [vm_compute; reflexivity|]). lia. }
unfold exp_d_okb in Hb. rewrite !Bool.andb_true_iff in Hb.
destruct Hb as [[[[H1 H2] H3] H4] H5].
apply Z.leb_le in H1, H2, H3, H4. apply Z.ltb_lt in H5.
split; [lia|].
rewrite fact_R.
assert (HP : bpow radix2 127 = IZR (2 ^ 127)) by (symmetry; exact (IZR_Zpower radix2 127 ltac:(lia))).
assert (HbP : bpow radix2 (-127) * bpow radix2 127 = 1) by (rewrite <- bpow_plus; reflexivity).
rewrite HP in HbP.
pose proof (bpow_gt_0 radix2 (-127)) as Hb0.
apply IZR_le in H3, H4. apply IZR_lt in H5. rewrite mult_IZR in H4. rewrite mult_IZR, plus_IZR in H5.
rewrite plus_IZR.
set (F := IZR (zfact j)) in *. set (D := IZR (DyadicPow.exp_d j)) in *.
set (P := IZR (2 ^ 127)) in *. set (b := bpow radix2 (-127)) in *.
split.
- apply (Rmult_le_reg_r F); [lra|]. rewrite Rinv_l by lra.
  assert (D * F * b <= P * b) by (apply Rmult_le_compat_r; lra). lra.
- apply (Rmult_le_reg_r F); [lra|]. rewrite Rinv_l by lra.
  assert (P * b <= (D + 1) * F * b) by (apply Rmult_le_compat_r; lra). lra.
Qed.

(** Horner's scheme run [n] times from [x], with the coefficients [1 / j!]
    from [j = n - 1] down, as [DyadicPow.exp_p] runs it. *)
Local Fixpoint hr (n : nat) (w x : R) : R :=
  match n with O => x | S j => hr j w (/ INR (fact j) + w * x) end.

Local Lemma hr_sum :
  forall j w x, hr (S j) w x = sum_f_R0 (fun i => / INR (fact i) * w ^ i) j + w ^ S j * x.
Proof.
induction j as [|j IH]; intros w x.
- cbn [hr sum_f_R0 pow]. ring.
- change (hr (S (S j)) w x) with (hr (S j) w (/ INR (fact (S j)) + w * x)).
  rewrite IH, tech5. cbn [pow]. ring.
Qed.

(** Each step of [DyadicPow.exp_p] keeps [p'] at 2^-127 between the
    roundings down and up of [d + w p], with [w] between [wl] and [wh] at
    2^-115 and [d] within 1 below [1 / j!]: the bounds increase with [w]
    and [p], which are not negative. [p] stays below [2^127 + 2^117], so
    that the products are below [2^103 2^128 < 2^(128 + 115)], and the
    last step adds [d = 2^127]. *)
Local Lemma exp_p_bounds :
  forall n wl wh w,
  (0 <= wl <= wh)%Z -> (wh <= 2 ^ 103)%Z ->
  IZR wl * bpow radix2 (-115) <= w <= IZR wh * bpow radix2 (-115) ->
  (n <= 8)%nat ->
  forall pl ph x pl' ph',
  (0 <= pl <= ph)%Z -> (ph <= 2 ^ 127 + 2 ^ 117)%Z ->
  IZR pl * bpow radix2 (-127) <= x <= IZR ph * bpow radix2 (-127) ->
  DyadicPow.exp_p n wl wh pl ph = (pl', ph') ->
  ((n <> 0)%nat -> (2 ^ 127 <= pl')%Z) /\ (0 <= pl' <= ph')%Z /\
  (ph' <= 2 ^ 127 + 2 ^ 117)%Z /\
  IZR pl' * bpow radix2 (-127) <= hr n w x <= IZR ph' * bpow radix2 (-127).
Proof.
intros n wl wh w Hwl Hwh Hw.
pose proof (bpow_gt_0 radix2 (-115)) as Hb115.
pose proof (bpow_gt_0 radix2 (-127)) as Hb127.
assert (Hwl0 : 0 <= IZR wl * bpow radix2 (-115))
  by (apply Rmult_le_pos; [apply IZR_le; lia | lra]).
induction n as [|j IH]; intros Hn pl ph x pl' ph' Hp Hph Hx E.
- cbn [DyadicPow.exp_p] in E. injection E as <- <-. cbn [hr].
  split; [intros H; contradiction H; reflexivity|].
  split; [lia|]. split; [lia|]. exact Hx.
- cbn [DyadicPow.exp_p] in E.
  destruct (exp_d_bounds j ltac:(lia)) as [Hd [Hdl Hdh]].
  assert (Hwp : (wl * pl <= wh * ph)%Z) by (apply Z.mul_le_mono_nonneg; lia).
  assert (Hwph : (wh * ph <= 2 ^ 103 * (2 ^ 127 + 2 ^ 117))%Z)
    by (apply Z.mul_le_mono_nonneg; lia).
  assert (Hwp0 : (0 <= wl * pl)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite (mul_dn_correct wl pl 115), (mul_up_correct wh ph 115) in E by lia.
  assert (Hx0 : 0 <= x).
  { assert (0 <= IZR pl * bpow radix2 (-127)) by (apply Rmult_le_pos; [apply IZR_le; lia | lra]).
    lra. }
  assert (Hlo : IZR (wl * pl / 2 ^ 115) * bpow radix2 (-127) <= w * x).
  { eapply Rle_trans;
      [apply (scale_dn (wl * pl) _ 115 (-115 + -127)); [lia | lia | apply Z.mul_div_le; lia] |].
    rewrite prod_scaled.
    apply Rmult_le_compat; [lra | apply Rmult_le_pos; [apply IZR_le; lia | lra] | lra | lra]. }
  assert (Hhi : w * x <= IZR ((wh * ph + 2 ^ 115 - 1) / 2 ^ 115) * bpow radix2 (-127)).
  { eapply Rle_trans;
      [| apply (scale_up (wh * ph) _ 115 (-115 + -127)); [lia | lia | apply div_up_ge; lia]].
    rewrite prod_scaled.
    apply Rmult_le_compat; lra. }
  set (pl1 := (DyadicPow.exp_d j + wl * pl / 2 ^ 115)%Z) in E.
  set (ph1 := (DyadicPow.exp_d j + 1 + (wh * ph + 2 ^ 115 - 1) / 2 ^ 115)%Z) in E.
  set (x1 := / INR (fact j) + w * x).
  assert (Hx1 : IZR pl1 * bpow radix2 (-127) <= x1 <= IZR ph1 * bpow radix2 (-127)).
  { unfold pl1, ph1, x1. rewrite !plus_IZR. rewrite plus_IZR in Hdh. lra. }
  assert (Hq0 : (0 <= wl * pl / 2 ^ 115)%Z) by (apply Z.div_pos; lia).
  assert (Hpl1 : (0 <= pl1)%Z) by (unfold pl1; lia).
  assert (Hpl1h : (pl1 <= ph1)%Z) by exact (le_of_scaled _ _ _ _ Hx1).
  assert (Hph1 : (ph1 <= 2 ^ 127 + 2 ^ 117)%Z).
  { unfold ph1.
    assert (((wh * ph + 2 ^ 115 - 1) / 2 ^ 115 <= 2 ^ 115 + 2 ^ 105 + 1)%Z)
      by (apply Z.div_le_upper_bound; lia).
    lia. }
  destruct (IH ltac:(lia) pl1 ph1 x1 pl' ph' (conj Hpl1 Hpl1h) Hph1 Hx1 E) as (H1 & H2 & H3 & H4).
  change (hr (S j) w x) with (hr j w x1).
  refine (conj _ (conj H2 (conj H3 H4))).
  intros _. destruct (Nat.eq_dec j 0) as [Hj0 | Hj0]; [| apply H1; exact Hj0].
  subst j. cbn [DyadicPow.exp_p] in E. injection E as <- _.
  unfold pl1. change (DyadicPow.exp_d 0) with (2 ^ 127)%Z. lia.
Qed.

(** ** The Taylor polynomial of [e^w] *)

Local Lemma bpow_pow : forall e n, bpow radix2 e ^ n = bpow radix2 (e * Z.of_nat n).
Proof.
intros e n. induction n as [|n IH].
- rewrite Z.mul_0_r. reflexivity.
- cbn [pow]. rewrite IH, <- bpow_plus. f_equal. lia.
Qed.

(** On [[0, 2^-12]], [e^w] is at least its Taylor polynomial of degree 8,
    whose terms are not negative, and at most that plus [2 2^-127]: the
    polynomial of degree 9 plus twice the next term ([exp_le_taylor])
    adds [w^9 / 9! + 2 w^10 / 10! < 1.45 2^-127]. *)
Local Lemma exp_w_bounds :
  forall w, 0 <= w <= bpow radix2 (-12) ->
  hr 8 w (/ INR (fact 8)) <= exp w <= hr 8 w (/ INR (fact 8)) + 2 * bpow radix2 (-127).
Proof.
intros w Hw.
assert (E8 : hr 8 w (/ INR (fact 8)) = sum_f_R0 (fun i => / INR (fact i) * w ^ i) 8).
{ rewrite hr_sum, (tech5 _ 7). cbv beta. ring. }
rewrite E8.
assert (Hb12 : bpow radix2 (-12) <= 1) by (apply (bpow_le radix2 (-12) 0); lia).
split.
- apply sum_incr; [exact (proj2_sig (exist_exp w)) |].
  intros n. apply Rmult_le_pos; [left; apply Rinv_0_lt_compat, INR_fact_lt_0 | apply pow_le; lra].
- assert (Hw1 : 0 <= w <= 1) by lra.
  pose proof (exp_le_taylor 9 w Hw1) as Hu.
  rewrite (tech5 _ 8) in Hu. cbv beta in Hu.
  rewrite !fact_R in Hu.
  change (zfact 9) with 362880%Z in Hu. change (zfact (S 9)) with 3628800%Z in Hu.
  assert (H9 : w ^ 9 <= bpow radix2 (-108)).
  { replace (-108)%Z with (-12 * Z.of_nat 9)%Z by reflexivity.
    rewrite <- bpow_pow. apply pow_incr. lra. }
  assert (H10 : w ^ S 9 <= bpow radix2 (-120)).
  { replace (-120)%Z with (-12 * Z.of_nat 10)%Z by reflexivity.
    rewrite <- bpow_pow. apply pow_incr. lra. }
  assert (E108 : bpow radix2 (-108) = 524288 * bpow radix2 (-127)).
  { replace (-108)%Z with (19 + -127)%Z by reflexivity. rewrite bpow_plus. reflexivity. }
  assert (E120 : bpow radix2 (-120) = 128 * bpow radix2 (-127)).
  { replace (-120)%Z with (7 + -127)%Z by reflexivity. rewrite bpow_plus. reflexivity. }
  pose proof (pow_le w 9 ltac:(lra)). pose proof (pow_le w (S 9) ltac:(lra)).
  lra.
Qed.

(** ** The bounds *)

Theorem acc_exp_correct :
  forall tl th lo hi e t,
  DyadicPow.acc_exp tl th = Some (lo, hi, e) ->
  IZR tl * bpow radix2 (-115) <= t <= IZR th * bpow radix2 (-115) ->
  (2 ^ 126 <= lo < 2 ^ 128)%Z /\ (0 <= hi < 2 ^ 128)%Z /\ (Z.abs e < 2 ^ 20)%Z /\
  IZR lo * bpow radix2 e <= exp t <= IZR hi * bpow radix2 e.
Proof.
intros tl th lo hi e t H Ht.
unfold DyadicPow.acc_exp in H. cbv zeta in H.
set (k := Z.shiftr (Z.shiftr tl 64 * DyadicPow.INV_LN2) 101) in H.
set (m := Z.abs k) in H.
destruct (2 ^ 25 <=? m)%Z eqn:Hkm; [discriminate H|].
apply Z.leb_gt in Hkm.
assert (Hm0 : (0 <= m)%Z) by apply Z.abs_nonneg.
destruct ln2_acc_bounds as (HL1 & HL2 & HL3).
assert (Hm1 : (m * (DyadicPow.LN2 + 1) <= (2 ^ 25 - 1) * 2 ^ 128)%Z)
  by (apply Z.mul_le_mono_nonneg; lia).
assert (Hm2 : (m * DyadicPow.LN2 <= m * (DyadicPow.LN2 + 1))%Z)
  by (apply Z.mul_le_mono_nonneg_l; lia).
assert (Hm3 : (0 <= m * DyadicPow.LN2)%Z) by (apply Z.mul_nonneg_nonneg; lia).
rewrite (mul_dn_correct m DyadicPow.LN2 25), (mul_up_correct m (DyadicPow.LN2 + 1) 25) in H
  by lia.
set (cdn := (m * DyadicPow.LN2 / 2 ^ 25)%Z) in H.
set (cup := ((m * (DyadicPow.LN2 + 1) + 2 ^ 25 - 1) / 2 ^ 25)%Z) in H.
destruct (DyadicPow.signed (k <? 0)%Z cdn cup) as [[cl ch] |] eqn:Hs; [| discriminate H].
destruct (checked_i 128 (tl - ch)) as [wl |] eqn:Hwl; [| discriminate H].
destruct (checked_i 128 (th - cl)) as [wh |] eqn:Hwh; [| discriminate H].
apply checked_i_eq in Hwl, Hwh.
destruct ((wl <? 0)%Z || (2 ^ 103 <? wh)%Z) eqn:Hw; [discriminate H|].
apply Bool.orb_false_iff in Hw as [Hw1 Hw2]. apply Z.ltb_ge in Hw1, Hw2.
destruct (DyadicPow.exp_p 8 wl wh (DyadicPow.exp_d 8) (DyadicPow.exp_d 8 + 1)) as [pl ph] eqn:Hp.
destruct (k_split k) as (Hk & Hj1 & Hj2).
set (j1 := Z.land (Z.shiftr k 6) 63) in H, Hk, Hj1.
set (j2 := Z.land k 63) in H, Hk, Hj2.
set (K := Z.shiftr k 12) in H, Hk.
destruct (exp_hi_correct j1 Hj1) as (He1 & He2 & He3).
destruct (exp_lo_correct j2 Hj2) as (Hl1 & Hl2 & Hl3).
pose proof (exp_prod_bound j1 j2 Hj1 Hj2) as Hpb.
set (eh := DyadicPow.exp_hi j1) in *.
set (el := DyadicPow.exp_lo j2) in *.
assert (Hee0 : (2 ^ 127 * 2 ^ 127 <= eh * el)%Z) by (apply Z.mul_le_mono_nonneg; lia).
rewrite (mul_dn_correct eh el 127), (mul_up_correct (eh + 1) (el + 1) 127) in H by lia.
set (sl := (eh * el / 2 ^ 127)%Z) in H.
set (sh := (((eh + 1) * (el + 1) + 2 ^ 127 - 1) / 2 ^ 127)%Z) in H.
assert (Hsl : (2 ^ 127 <= sl < 2 ^ 128)%Z).
{ unfold sl. split.
  - apply Z.div_le_lower_bound; lia.
  - apply Z.div_lt_upper_bound; lia. }
assert (Hsh : (0 <= sh < 2 ^ 128)%Z).
{ unfold sh. split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia. }
pose proof (bpow_gt_0 radix2 (-115)) as Hb115.
pose proof (bpow_gt_0 radix2 (-127)) as Hb127.
pose proof (bpow_gt_0 radix2 (-12)) as Hb12.
(* k ln 2 / 4096 = ±m ln 2 2^-12 is in [cl, ch] at 2^-115. *)
set (c := IZR k * ln 2 * bpow radix2 (-12)).
assert (Hc : IZR cl * bpow radix2 (-115) <= c <= IZR ch * bpow radix2 (-115)).
{ assert (Hm12 : 0 <= IZR m * bpow radix2 (-12)) by (apply Rmult_le_pos; [apply IZR_le; lia | lra]).
  assert (Hdn : IZR cdn * bpow radix2 (-115) <= IZR m * ln 2 * bpow radix2 (-12)).
  { eapply Rle_trans;
      [apply (scale_dn (m * DyadicPow.LN2) _ 25 (-12 + -128)); [lia | lia | apply Z.mul_div_le; lia] |].
    rewrite prod_scaled.
    replace (IZR m * ln 2 * bpow radix2 (-12)) with (IZR m * bpow radix2 (-12) * ln 2) by ring.
    apply Rmult_le_compat_l; lra. }
  assert (Hup : IZR m * ln 2 * bpow radix2 (-12) <= IZR cup * bpow radix2 (-115)).
  { eapply Rle_trans;
      [| apply (scale_up (m * (DyadicPow.LN2 + 1)) _ 25 (-12 + -128)); [lia | lia | apply div_up_ge; lia]].
    rewrite prod_scaled.
    replace (IZR m * ln 2 * bpow radix2 (-12)) with (IZR m * bpow radix2 (-12) * ln 2) by ring.
    apply Rmult_le_compat_l; lra. }
  destruct (signed_correct _ _ _ _ _ Hs) as (_ & _ & Hsg).
  unfold c. destruct (k <? 0)%Z eqn:Hk0.
  - apply Z.ltb_lt in Hk0. destruct Hsg as [-> ->].
    assert (Hkm' : IZR k = - IZR m) by (unfold m; rewrite Z.abs_neq, opp_IZR by lia; ring).
    rewrite Hkm', !opp_IZR. lra.
  - apply Z.ltb_ge in Hk0. destruct Hsg as [-> ->].
    assert (Hkm' : IZR k = IZR m) by (unfold m; rewrite Z.abs_eq by lia; reflexivity).
    rewrite Hkm'. lra. }
(* w = t - k ln 2 / 4096 is in [wl, wh] at 2^-115, so in [0, 2^-12]. *)
set (w := t - c).
assert (Hw : IZR wl * bpow radix2 (-115) <= w <= IZR wh * bpow radix2 (-115)).
{ unfold w. rewrite Hwl, Hwh, !minus_IZR. lra. }
assert (Hwlh : (wl <= wh)%Z) by exact (le_of_scaled _ _ _ _ Hw).
assert (Hw12 : 0 <= w <= bpow radix2 (-12)).
{ split.
  - assert (0 <= IZR wl * bpow radix2 (-115)) by (apply Rmult_le_pos; [apply IZR_le; lia | lra]).
    lra.
  - assert (H103 : IZR wh * bpow radix2 (-115) <= IZR (2 ^ 103) * bpow radix2 (-115))
      by (apply Rmult_le_compat_r; [lra | apply IZR_le; lia]).
    assert (HP : bpow radix2 103 = IZR (2 ^ 103))
      by (symmetry; exact (IZR_Zpower radix2 103 ltac:(lia))).
    rewrite <- HP, <- bpow_plus in H103.
    exact (Rle_trans _ _ _ (proj2 Hw) H103). }
(* e^w is in [pl, ph + 2] at 2^-127. *)
destruct (exp_d_bounds 8 ltac:(lia)) as [Hd8 Hd8r].
destruct (exp_p_bounds 8 wl wh w (conj Hw1 Hwlh) Hw2 Hw ltac:(lia)
            (DyadicPow.exp_d 8) (DyadicPow.exp_d 8 + 1) (/ INR (fact 8)) pl ph
            ltac:(lia) ltac:(lia) Hd8r Hp) as (Hp1 & Hp2 & Hp3 & Hp4).
assert (Hpl : (2 ^ 127 <= pl)%Z) by (apply Hp1; discriminate).
pose proof (exp_w_bounds w Hw12) as Hexw.
assert (Hew : IZR pl * bpow radix2 (-127) <= exp w <= IZR (ph + 2) * bpow radix2 (-127)).
{ rewrite plus_IZR. lra. }
(* 2^(j1/64) 2^(j2/4096) is in [sl, sh] at 2^-127. *)
set (sv := Rexp2 (IZR j1 / 64) * Rexp2 (IZR j2 / 4096)).
assert (Hr1 : 0 < Rexp2 (IZR j1 / 64)) by (unfold Rexp2, Rpower; apply exp_pos).
assert (Hr2 : 0 < Rexp2 (IZR j2 / 4096)) by (unfold Rexp2, Rpower; apply exp_pos).
assert (Hsv0 : 0 < sv) by (apply Rmult_lt_0_compat; assumption).
assert (HS : IZR sl * bpow radix2 (-127) <= sv <= IZR sh * bpow radix2 (-127)).
{ split.
  - eapply Rle_trans;
      [apply (scale_dn (eh * el) _ 127 (-127 + -127)); [lia | lia | apply Z.mul_div_le; lia] |].
    rewrite prod_scaled.
    apply Rmult_le_compat;
      [apply Rmult_le_pos; [apply IZR_le; lia | lra] | apply Rmult_le_pos; [apply IZR_le; lia | lra]
      | lra | lra].
  - eapply Rle_trans;
      [| apply (scale_up ((eh + 1) * (el + 1)) _ 127 (-127 + -127)); [lia | lia | apply div_up_ge; lia]].
    rewrite prod_scaled.
    apply Rmult_le_compat; lra. }
(* e^t = 2^(k >> 12) 2^(j1/64) 2^(j2/4096) e^w. *)
assert (Hexp : exp t = bpow radix2 K * sv * exp w).
{ assert (Et : exp t = exp c * exp w) by (unfold w; rewrite <- exp_plus; f_equal; ring).
  assert (Ec : exp c = bpow radix2 K * sv).
  { apply (f_equal IZR) in Hk. rewrite !plus_IZR, !mult_IZR in Hk.
    assert (E12 : bpow radix2 (-12) = / 4096) by reflexivity.
    unfold c, sv, Rexp2, Rpower. rewrite E12, bpow_exp, <- !exp_plus. f_equal.
    change (IZR (radix_val radix2)) with 2. rewrite Hk. field. }
  rewrite Et, Ec. ring. }
(* The products. *)
assert (Hpl2 : (pl < 2 ^ 128)%Z) by lia.
rewrite (mul_wide_correct sl pl) in H by lia.
rewrite (mul_wide_correct sh (ph + 2)) in H by lia.
cbv beta iota in H.
(* Not [injection], which does not end here. *)
apply (f_equal (fun o => match o with Some p => p | None => (lo, hi, e) end)) in H.
cbv beta iota in H.
apply pair_equal_spec in H as [H He]. apply pair_equal_spec in H as [Hlo Hhi].
subst lo hi e.
assert (Hslpl : (2 ^ 127 * 2 ^ 127 <= sl * pl)%Z) by (apply Z.mul_le_mono_nonneg; lia).
assert (Hslpl' : (sl * pl < 2 ^ 128 * 2 ^ 128)%Z) by (apply Z.mul_lt_mono_nonneg; lia).
assert (Hshph : (sh * (ph + 2) < 2 ^ 128 * (2 ^ 127 + 2 ^ 117 + 3))%Z)
  by (apply Z.mul_lt_mono_nonneg; lia).
assert (Hshph0 : (0 <= sh * (ph + 2))%Z) by (apply Z.mul_nonneg_nonneg; lia).
assert (Hq : (sh * (ph + 2) / 2 ^ 128 < 2 ^ 127 + 2 ^ 117 + 3)%Z)
  by (apply Z.div_lt_upper_bound; lia).
assert (Hq0 : (0 <= sh * (ph + 2) / 2 ^ 128)%Z) by (apply Z.div_pos; lia).
pose proof (div_ceil_ge (sh * (ph + 2))) as Hceil.
set (hb := (if sh * (ph + 2) mod 2 ^ 128 =? 0 then 0 else 1)%Z) in *.
assert (Hhb : (0 <= hb <= 1)%Z) by (unfold hb; destruct (_ =? 0)%Z; lia).
assert (HK : bpow radix2 (K - 126) = bpow radix2 K * bpow radix2 (-126))
  by (rewrite <- bpow_plus; f_equal; lia).
pose proof (bpow_gt_0 radix2 K) as HbK.
split; [split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia |].
split; [lia |].
split.
{ unfold K. rewrite Z.shiftr_div_pow2 by lia. unfold m in Hkm. change (2 ^ 12)%Z with 4096%Z.
  pose proof (Z.div_mod k 4096 ltac:(lia)). pose proof (Z.mod_pos_bound k 4096 ltac:(lia)). lia. }
rewrite Hexp, HK.
split.
- assert (L : IZR (sl * pl / 2 ^ 128) * bpow radix2 (-126) <= sv * exp w).
  { eapply Rle_trans;
      [apply (scale_dn (sl * pl) _ 128 (-127 + -127)); [lia | lia | apply Z.mul_div_le; lia] |].
    rewrite prod_scaled.
    apply Rmult_le_compat;
      [apply Rmult_le_pos; [apply IZR_le; lia | lra] | apply Rmult_le_pos; [apply IZR_le; lia | lra]
      | lra | lra]. }
  replace (IZR (sl * pl / 2 ^ 128) * (bpow radix2 K * bpow radix2 (-126)))
    with (bpow radix2 K * (IZR (sl * pl / 2 ^ 128) * bpow radix2 (-126))) by ring.
  rewrite Rmult_assoc. apply Rmult_le_compat_l; lra.
- assert (U : sv * exp w <= IZR (sh * (ph + 2) / 2 ^ 128 + hb) * bpow radix2 (-126)).
  { eapply Rle_trans;
      [| apply (scale_up (sh * (ph + 2)) _ 128 (-127 + -127)); [lia | lia | exact Hceil]].
    rewrite prod_scaled.
    apply Rmult_le_compat; [left; exact Hsv0 | left; apply exp_pos | lra | lra]. }
  replace (IZR (sh * (ph + 2) / 2 ^ 128 + hb) * (bpow radix2 K * bpow radix2 (-126)))
    with (bpow radix2 K * (IZR (sh * (ph + 2) / 2 ^ 128 + hb) * bpow radix2 (-126))) by ring.
  rewrite Rmult_assoc. apply Rmult_le_compat_l; lra.
Qed.
