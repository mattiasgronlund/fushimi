(** The bounds on [t = y ln x] of the accurate phase of x^y
    ([DyadicPow.acc_t], [fn acc_t] of [src/dyadic/pow/acc.rs]).
    [ln_split] gives [x = 2^e m] and an [i] ([FastLogReduce.v]), [z = r m -
    1] is exact for the [r] of the table at [i], and [y ln x = y e ln 2 + y
    (-ln r) + y z Q(z)] with [Q(z) = ln(1 + z) / z]. [log_q_correct] bounds
    [Q(z)] by Horner's scheme on the Taylor polynomial of degree 13, and
    each of the three terms comes from a product of integers rounded down
    and up to 2^-115 ([AccPowArith.v]) with the tables of
    [AccPowTables.v]. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Fushimi Require Import Model Elementary Encoding AccPowArith AccPowTables FastLogTaylor.
From Fushimi Require FastLogReduce DyPowRules.

Open Scope R_scope.

Lemma pow2_R : forall s, (0 <= s)%Z -> IZR (2 ^ s) = bpow radix2 s.
Proof.
intros s Hs. change (2 ^ s)%Z with (Zpower radix2 s). apply IZR_Zpower. exact Hs.
Qed.

Lemma ceil_div_ge : forall n d, (0 < d)%Z -> (n <= d * ((n + d - 1) / d))%Z.
Proof.
intros n d Hd.
pose proof (Z.div_mod (n + d - 1) d ltac:(lia)).
pose proof (Z.mod_pos_bound (n + d - 1) d Hd). lia.
Qed.

Definition Q_ok (v : Z) : Prop := (2 ^ 123 <= v <= 2 ^ 127 + 2 ^ 120)%Z.

(** [mul_dn] and [mul_up] at 63 of [a <= 2^54] and a [b] of [Q_ok]. *)
Lemma mul_63 :
  forall a b, (0 <= a <= 2 ^ 54)%Z -> Q_ok b ->
  (0 <= DyadicPow.mul_dn a b 63 <= 2 ^ 118 + 2 ^ 111)%Z /\
  (0 <= DyadicPow.mul_up a b 63 <= 2 ^ 118 + 2 ^ 111)%Z /\
  IZR (DyadicPow.mul_dn a b 63) * bpow radix2 63 <= IZR a * IZR b <=
    IZR (DyadicPow.mul_up a b 63) * bpow radix2 63.
Proof.
intros a b Ha Hb. unfold Q_ok in Hb.
assert (Hab : (0 <= a * b <= 2 ^ 54 * (2 ^ 127 + 2 ^ 120))%Z).
{ split; [apply Z.mul_nonneg_nonneg; lia |].
  apply Z.mul_le_mono_nonneg; lia. }
assert (Hlt : (a * b < 2 ^ (128 + 63))%Z).
{ eapply Z.le_lt_trans; [apply Hab |]. apply Z.ltb_lt. vm_compute. reflexivity. }
assert (H128 : (2 ^ 127 + 2 ^ 120 < 2 ^ 128)%Z) by (apply Z.ltb_lt; vm_compute; reflexivity).
assert (H54 : (2 ^ 54 < 2 ^ 128)%Z) by (apply Z.ltb_lt; vm_compute; reflexivity).
rewrite (mul_dn_correct a b 63) by lia.
rewrite (mul_up_correct a b 63) by lia.
assert (HD : (2 ^ 54 * (2 ^ 127 + 2 ^ 120) / 2 ^ 63 = 2 ^ 118 + 2 ^ 111)%Z)
  by (vm_compute; reflexivity).
assert (HU : ((2 ^ 54 * (2 ^ 127 + 2 ^ 120) + 2 ^ 63 - 1) / 2 ^ 63 = 2 ^ 118 + 2 ^ 111)%Z)
  by (vm_compute; reflexivity).
assert (H63 : (0 < 2 ^ 63)%Z) by lia.
split; [split |].
- apply Z.div_pos; lia.
- rewrite <- HD. apply Z.div_le_mono; lia.
- split; [split |].
  + apply Z.div_pos; lia.
  + rewrite <- HU. apply Z.div_le_mono; lia.
  + rewrite <- mult_IZR, <- (pow2_R 63) by lia. rewrite <- !mult_IZR.
    split; apply IZR_le.
    * rewrite (Z.mul_comm _ (2 ^ 63)). apply Z.mul_div_le. exact H63.
    * rewrite (Z.mul_comm _ (2 ^ 63)). apply ceil_div_ge. exact H63.
Qed.

(** [log_c j] is [1 / (j + 1)] rounded down at 2^-127. *)
Lemma log_c_bounds :
  forall j, IZR (DyadicPow.log_c j) * bpow radix2 (-127) <= / INR (S j) <=
    IZR (DyadicPow.log_c j + 1) * bpow radix2 (-127).
Proof.
intros j. unfold DyadicPow.log_c.
set (d := (Z.of_nat j + 1)%Z).
assert (Hd : (0 < d)%Z) by lia.
assert (HD : INR (S j) = IZR d) by (unfold d; rewrite S_INR, INR_IZR_INZ, plus_IZR; reflexivity).
rewrite HD.
pose proof (Z.mul_div_le (2 ^ 127) d Hd) as H1.
pose proof (Z.mul_succ_div_gt (2 ^ 127) d Hd) as H2. unfold Z.succ in H2.
apply IZR_le in H1. apply IZR_lt in H2. rewrite mult_IZR, pow2_R in H1, H2 by lia.
set (c := (2 ^ 127 / d)%Z) in *.
assert (HB : 0 < bpow radix2 127) by apply bpow_gt_0.
assert (HD0 : 0 < IZR d) by (apply IZR_lt; exact Hd).
change (bpow radix2 (-127)) with (/ bpow radix2 127).
split.
- apply Rmult_le_reg_r with (IZR d * bpow radix2 127); [apply Rmult_lt_0_compat; lra |].
  replace (IZR c * / bpow radix2 127 * (IZR d * bpow radix2 127)) with (IZR d * IZR c)
    by (field; lra).
  replace (/ IZR d * (IZR d * bpow radix2 127)) with (bpow radix2 127) by (field; lra). lra.
- apply Rmult_le_reg_r with (IZR d * bpow radix2 127); [apply Rmult_lt_0_compat; lra |].
  replace (IZR (c + 1) * / bpow radix2 127 * (IZR d * bpow radix2 127)) with (IZR d * IZR (c + 1))
    by (field; lra).
  replace (/ IZR d * (IZR d * bpow radix2 127)) with (bpow radix2 127) by (field; lra). lra.
Qed.

Lemma log_c_range : forall j, (j <= 13)%nat -> (2 ^ 123 + 2 ^ 120 <= DyadicPow.log_c j <= 2 ^ 127)%Z.
Proof.
intros j Hj.
do 14 (destruct j as [| j]; [split; apply Z.leb_le; vm_compute; reflexivity |]).
lia.
Qed.

(** Horner's scheme for [ln(1 + z) / z] with exact coefficients, from
    [q] down [n] steps. *)
Fixpoint horner (n : nat) (z q : R) : R :=
  match n with
  | O => q
  | S j => horner j z (/ INR (S j) - z * q)
  end.

Lemma horner_sum :
  forall n z q, z * horner n z q = log1p_sum n z + (-1) ^ n * z ^ S n * q.
Proof.
induction n as [| j IH]; intros z q; cbn [horner].
- cbn [log1p_sum pow]. ring.
- rewrite IH. cbn [log1p_sum pow]. unfold Rdiv. ring.
Qed.

Lemma log_q_step :
  forall j (pos : bool) a ql qh z q, (j <= 13)%nat -> (0 <= a <= 2 ^ 54)%Z ->
  z = IZR (if pos then a else - a) * bpow radix2 (-63) -> Q_ok ql -> Q_ok qh ->
  IZR ql * bpow radix2 (-127) <= q <= IZR qh * bpow radix2 (-127) ->
  let c := DyadicPow.log_c j in
  let '(l, h) :=
    if pos then (c - DyadicPow.mul_up a qh 63, c + 1 - DyadicPow.mul_dn a ql 63)%Z
    else (c + DyadicPow.mul_dn a ql 63, c + 1 + DyadicPow.mul_up a qh 63)%Z in
  Q_ok l /\ Q_ok h /\
  IZR l * bpow radix2 (-127) <= / INR (S j) - z * q <= IZR h * bpow radix2 (-127).
Proof.
intros j pos a ql qh z q Hj Ha Hz Hl Hh Hq. cbv zeta.
pose proof (log_c_range j Hj) as Hc.
pose proof (log_c_bounds j) as HcR. rewrite plus_IZR in HcR.
destruct (mul_63 a ql Ha Hl) as (Hdl & Hul & HRl).
destruct (mul_63 a qh Ha Hh) as (Hdh & Huh & HRh).
set (c := DyadicPow.log_c j) in *.
set (dl := DyadicPow.mul_dn a ql 63) in *. set (ul := DyadicPow.mul_up a ql 63) in *.
set (dh := DyadicPow.mul_dn a qh 63) in *. set (uh := DyadicPow.mul_up a qh 63) in *.
unfold Q_ok in Hl, Hh.
assert (HE1 : bpow radix2 63 * bpow radix2 (-63) = 1) by (rewrite <- bpow_plus; reflexivity).
assert (HB : 0 < bpow radix2 (-127)) by apply bpow_gt_0.
assert (HE0 : 0 < bpow radix2 (-63)) by apply bpow_gt_0.
assert (HA : 0 <= IZR a) by (apply IZR_le; lia).
assert (HEB : 0 <= bpow radix2 (-63) * bpow radix2 (-127)) by (apply Rmult_le_pos; lra).
assert (HX : forall v, IZR v * bpow radix2 63 * (bpow radix2 (-63) * bpow radix2 (-127)) =
                       IZR v * bpow radix2 (-127)).
{ intros v. transitivity (IZR v * (bpow radix2 63 * bpow radix2 (-63)) * bpow radix2 (-127));
    [ring | rewrite HE1; ring]. }
(* [a q 2^-63] is between [a ql] and [a qh] at 2^-190, so between [dl] and
   [uh] at 2^-127. *)
assert (HzQ : IZR dl * bpow radix2 (-127) <= IZR a * bpow radix2 (-63) * q <=
              IZR uh * bpow radix2 (-127)).
{ assert (H1 : IZR a * bpow radix2 (-63) * (IZR ql * bpow radix2 (-127)) <=
               IZR a * bpow radix2 (-63) * q <=
               IZR a * bpow radix2 (-63) * (IZR qh * bpow radix2 (-127))).
  { split; apply Rmult_le_compat_l; try lra; apply Rmult_le_pos; lra. }
  assert (H2 : IZR dl * bpow radix2 63 * (bpow radix2 (-63) * bpow radix2 (-127)) <=
               IZR a * IZR ql * (bpow radix2 (-63) * bpow radix2 (-127)))
    by (apply Rmult_le_compat_r; lra).
  assert (H3 : IZR a * IZR qh * (bpow radix2 (-63) * bpow radix2 (-127)) <=
               IZR uh * bpow radix2 63 * (bpow radix2 (-63) * bpow radix2 (-127)))
    by (apply Rmult_le_compat_r; lra).
  rewrite HX in H2, H3. lra. }
assert (HK : (2 ^ 118 + 2 ^ 111 + 1 < 2 ^ 120 /\ 2 ^ 123 + 2 ^ 120 <= 2 ^ 127)%Z)
  by (split; apply Z.ltb_lt || apply Z.leb_le; vm_compute; reflexivity).
destruct pos; rewrite Hz; [| rewrite opp_IZR]; cbv beta iota; unfold Q_ok.
- split; [lia |]. split; [lia |].
  rewrite !minus_IZR, plus_IZR. lra.
- split; [lia |]. split; [lia |].
  rewrite !plus_IZR. lra.
Qed.

Lemma log_q_inv :
  forall n (pos : bool) a ql qh z q, (n <= 13)%nat -> (0 <= a <= 2 ^ 54)%Z ->
  z = IZR (if pos then a else - a) * bpow radix2 (-63) -> Q_ok ql -> Q_ok qh ->
  IZR ql * bpow radix2 (-127) <= q <= IZR qh * bpow radix2 (-127) ->
  let '(l, h) := DyadicPow.log_q n pos a ql qh in
  Q_ok l /\ Q_ok h /\
  IZR l * bpow radix2 (-127) <= horner n z q <= IZR h * bpow radix2 (-127).
Proof.
induction n as [| j IH]; intros pos a ql qh z q Hn Ha Hz Hl Hh Hq.
- cbn [DyadicPow.log_q horner]. auto.
- cbn [DyadicPow.log_q horner].
  pose proof (log_q_step j pos a ql qh z q ltac:(lia) Ha Hz Hl Hh Hq) as H.
  cbv zeta in H.
  destruct pos; cbv beta iota in H |- *; destruct H as (Hl' & Hh' & Hq').
  + exact (IH true _ _ _ _ _ ltac:(lia) Ha Hz Hl' Hh' Hq').
  + exact (IH false _ _ _ _ _ ltac:(lia) Ha Hz Hl' Hh' Hq').
Qed.

Lemma log_q_rem :
  forall z, z <> 0 -> Rabs z <= bpow radix2 (-9) ->
  Rabs (ln (1 + z) / z - horner 13 z (/ INR 14)) <= bpow radix2 (-127).
Proof.
intros z Hz0 Hz.
change (bpow radix2 (-9)) with (/ 512) in Hz.
pose proof (log1p_taylor 14 z ltac:(lra)) as HT.
assert (HP : z * horner 13 z (/ INR 14) = log1p_sum 14 z).
{ rewrite horner_sum.
  change (log1p_sum 14 z) with (log1p_sum 13 z + (-1) ^ 13 * z ^ 14 / INR 14).
  unfold Rdiv. ring. }
replace (ln (1 + z) / z - horner 13 z (/ INR 14)) with ((ln (1 + z) - log1p_sum 14 z) / z)
  by (rewrite <- HP; field; exact Hz0).
unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
set (w := Rabs z) in *.
assert (Hw : 0 < w) by (apply Rabs_pos_lt; exact Hz0).
set (D := Rabs (ln (1 + z) - log1p_sum 14 z)) in *.
assert (HK : w ^ 14 <= (/ 512) ^ 14) by (apply pow_incr; lra).
assert (HK0 : 0 <= w ^ 14) by (apply pow_le; lra).
assert (HC : (/ 512) ^ 14 = 2 * bpow radix2 (-127)).
{ change (bpow radix2 (-127)) with (/ IZR (Z.pow_pos 2 127)).
  rewrite pow_inv, pow_IZR.
  replace (IZR (Z.pow_pos 2 127)) with (2 * IZR (512 ^ Z.of_nat 14))
    by (rewrite <- mult_IZR; reflexivity).
  field. apply not_0_IZR. discriminate. }
assert (H15 : INR (S 14) = 15) by (cbn; ring).
rewrite H15 in HT.
(* [D / w <= w^14 / (15 (1 - w)) <= 2 w^14 / 15]. *)
assert (HD : D * / w <= w ^ 14 / (15 * (1 - w))).
{ apply Rmult_le_reg_r with w; [exact Hw |].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
  replace (w ^ 14 / (15 * (1 - w)) * w) with (w ^ 15 / (15 * (1 - w))) by (cbn; field; lra).
  exact HT. }
assert (HD2 : w ^ 14 / (15 * (1 - w)) <= 2 * w ^ 14 / 15).
{ apply Rmult_le_reg_r with (15 * (1 - w)); [lra |].
  replace (w ^ 14 / (15 * (1 - w)) * (15 * (1 - w))) with (w ^ 14) by (field; lra).
  replace (2 * w ^ 14 / 15 * (15 * (1 - w))) with (2 * (1 - w) * w ^ 14) by (field; lra).
  nra. }
lra.
Qed.

(** Horner's scheme of [acc_t] at [z = ±a 2^-63], [+] if [pos]: [Q(z)]
    in [[ql - 1, qh + 1]] at 2^-127. *)
Lemma log_q_correct :
  forall a (pos : bool), (0 <= a <= 2 ^ 54)%Z ->
  let '(ql, qh) :=
    DyadicPow.log_q 13 pos a (DyadicPow.log_c 13) (DyadicPow.log_c 13 + 1) in
  (0 < ql - 1 < 2 ^ 128)%Z /\ (0 < qh + 1 < 2 ^ 128)%Z /\
  ((0 < a)%Z ->
   let z := IZR (if pos then a else - a) * bpow radix2 (-63) in
   IZR (ql - 1) * bpow radix2 (-127) <= ln (1 + z) / z <= IZR (qh + 1) * bpow radix2 (-127)).
Proof.
intros a pos Ha.
set (z := IZR (if pos then a else - a) * bpow radix2 (-63)).
pose proof (log_c_range 13 ltac:(lia)) as Hc.
pose proof (log_c_bounds 13) as HcR.
assert (HK : (2 ^ 127 + 1 <= 2 ^ 127 + 2 ^ 120 /\ 2 ^ 127 + 2 ^ 120 + 1 < 2 ^ 128)%Z)
  by (split; apply Z.ltb_lt || apply Z.leb_le; vm_compute; reflexivity).
assert (H0 : Q_ok (DyadicPow.log_c 13)) by (unfold Q_ok; lia).
assert (H1 : Q_ok (DyadicPow.log_c 13 + 1)) by (unfold Q_ok; lia).
pose proof (log_q_inv 13 pos a _ _ z (/ INR 14) ltac:(lia) Ha eq_refl H0 H1 HcR) as HI.
destruct (DyadicPow.log_q 13 pos a (DyadicPow.log_c 13) (DyadicPow.log_c 13 + 1)) as (ql, qh).
destruct HI as (Hl & Hh & Hq). unfold Q_ok in Hl, Hh.
split; [lia |]. split; [lia |].
intros Ha0.
assert (Hz : z <> 0 /\ Rabs z <= bpow radix2 (-9)).
{ assert (HA : 0 < IZR a <= bpow radix2 54)
    by (rewrite <- pow2_R by lia; split; apply IZR_lt || apply IZR_le; lia).
  assert (Hza : Rabs z = IZR a * bpow radix2 (-63)).
  { unfold z. rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0.
    destruct pos; [| rewrite opp_IZR, Rabs_Ropp]; rewrite Rabs_pos_eq by lra; reflexivity. }
  assert (HE : bpow radix2 54 * bpow radix2 (-63) = bpow radix2 (-9))
    by (rewrite <- bpow_plus; reflexivity).
  pose proof (bpow_gt_0 radix2 (-63)) as HE0.
  split.
  - intros Hz0. rewrite Hz0, Rabs_R0 in Hza.
    assert (0 < IZR a * bpow radix2 (-63)) by (apply Rmult_lt_0_compat; lra). lra.
  - rewrite Hza, <- HE. apply Rmult_le_compat_r; lra. }
destruct Hz as (Hz0 & Hz9).
pose proof (log_q_rem z Hz0 Hz9) as HR. apply Rabs_le_inv in HR.
rewrite minus_IZR, plus_IZR. lra.
Qed.

(** ** The terms of [y ln x] *)

Lemma ln_bpow2 : forall e, ln (bpow radix2 e) = IZR e * ln 2.
Proof. intros e. rewrite bpow_exp. apply ln_exp. Qed.

Lemma checked_i_eq : forall w v t, checked_i w v = Some t -> t = v.
Proof. intros w v t H. unfold checked_i in H. destruct (_ && _); congruence. Qed.

(** [u w] is [±|u| |w|], [-] where exactly one of them is negative. *)
Lemma sign_mul :
  forall (nu nw : bool) (u w : R),
  (if nu then u < 0 else 0 <= u) -> (if nw then w <= 0 else 0 <= w) ->
  u * w = if xorb nu nw then - (Rabs u * Rabs w) else Rabs u * Rabs w.
Proof.
intros nu nw u w Hu Hw.
destruct nu, nw; cbn [xorb];
  [rewrite (Rabs_left u), (Rabs_left1 w) by lra | rewrite (Rabs_left u), (Rabs_pos_eq w) by lra
  | rewrite (Rabs_pos_eq u), (Rabs_left1 w) by lra | rewrite (Rabs_pos_eq u), (Rabs_pos_eq w) by lra];
  ring.
Qed.

(** [u 2^ey W] from bounds on [W] at 2^k, at 2^(ey + k). *)
Lemma scale_bounds :
  forall u v1 v2 k ey s (W : R), (- s - 115 = ey + k)%Z -> (0 <= u)%Z ->
  IZR v1 * bpow radix2 k <= W <= IZR v2 * bpow radix2 k ->
  IZR (u * v1) * bpow radix2 (- s - 115) <= IZR u * bpow radix2 ey * W <=
  IZR (u * v2) * bpow radix2 (- s - 115).
Proof.
intros u v1 v2 k ey s W Hs Hu HW.
rewrite Hs, bpow_plus, !mult_IZR.
assert (H0 : 0 <= IZR u * bpow radix2 ey)
  by (apply Rmult_le_pos; [apply IZR_le; exact Hu | apply bpow_ge_0]).
split.
- replace (IZR u * IZR v1 * (bpow radix2 ey * bpow radix2 k)) with
    (IZR u * bpow radix2 ey * (IZR v1 * bpow radix2 k)) by ring.
  apply Rmult_le_compat_l; [exact H0 | apply HW].
- replace (IZR u * IZR v2 * (bpow radix2 ey * bpow radix2 k)) with
    (IZR u * bpow radix2 ey * (IZR v2 * bpow radix2 k)) by ring.
  apply Rmult_le_compat_l; [exact H0 | apply HW].
Qed.

(** A term of [acc_t]: bounds on a magnitude [M] at 2^(-s-115) from the
    products [a b1] and [a b2], shifted to 2^-115 and signed. *)
Lemma term_bounds :
  forall (neg : bool) a b1 b2 s lo hi l h (M : R),
  (0 <= a < 2 ^ 128)%Z -> (0 <= b1 < 2 ^ 128)%Z -> (0 <= b2 < 2 ^ 128)%Z ->
  IZR (a * b1) * bpow radix2 (- s - 115) <= M <= IZR (a * b2) * bpow radix2 (- s - 115) ->
  DyadicPow.shr_dn (DyadicPow.mul_wide a b1) s = Some lo ->
  DyadicPow.shr_up (DyadicPow.mul_wide a b2) s = Some hi ->
  DyadicPow.signed neg lo hi = Some (l, h) ->
  IZR l * bpow radix2 (-115) <= (if neg then - M else M) <= IZR h * bpow radix2 (-115).
Proof.
intros neg a b1 b2 s lo hi l h M Ha Hb1 Hb2 HM Hlo Hhi Hs.
assert (Hw : forall b, (0 <= b < 2 ^ 128)%Z ->
  (0 <= a * b / 2 ^ 128 < 2 ^ 128)%Z /\ (0 <= a * b mod 2 ^ 128 < 2 ^ 128)%Z /\
  (a * b / 2 ^ 128 * 2 ^ 128 + a * b mod 2 ^ 128 = a * b)%Z).
{ intros b Hb.
  assert (H0 : (0 <= a * b < 2 ^ 128 * 2 ^ 128)%Z)
    by (split; [apply Z.mul_nonneg_nonneg | apply Z.mul_lt_mono_nonneg]; lia).
  split; [split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia |].
  split; [apply Z.mod_pos_bound; lia |].
  rewrite Z.mul_comm. symmetry. apply Z.div_mod. lia. }
destruct (Hw b1 Hb1) as (H1h & H1l & H1e). destruct (Hw b2 Hb2) as (H2h & H2l & H2e).
rewrite mul_wide_correct in Hlo, Hhi by lia.
destruct (shr_dn_correct _ _ s lo H1h H1l Hlo) as (Hlo0 & HloR).
destruct (shr_up_correct _ _ s hi H2h H2l Hhi) as (Hhi0 & HhiR).
rewrite H1e in HloR. rewrite H2e in HhiR.
destruct (signed_correct neg lo hi l h Hs) as (_ & _ & Hlh).
assert (HB : bpow radix2 s * bpow radix2 (- s - 115) = bpow radix2 (-115))
  by (rewrite <- bpow_plus; f_equal; ring).
pose proof (bpow_ge_0 radix2 (- s - 115)) as HB0.
assert (HL : IZR lo * bpow radix2 (-115) <= M).
{ rewrite <- HB, <- Rmult_assoc. eapply Rle_trans; [| apply HM].
  apply Rmult_le_compat_r; [exact HB0 | exact HloR]. }
assert (HH : M <= IZR hi * bpow radix2 (-115)).
{ rewrite <- HB, <- Rmult_assoc. eapply Rle_trans; [apply HM |].
  apply Rmult_le_compat_r; [exact HB0 | exact HhiR]. }
destruct neg; destruct Hlh as (-> & ->); [rewrite !opp_IZR |]; lra.
Qed.

(** [B2R m = mm 2^-53] for the [mm] of [acc_t], from the bits of an [m]
    in [[1/2, 2)]. *)
Lemma mm_correct :
  forall m, is_finite m = true -> / 2 <= B2R m < 2 ->
  let b := to_bits m in
  let mm := Z.shiftl (Z.lor (Z.land b DyadicPow.FRAC) (Z.shiftl 1 52)) (Z.shiftr b 52 - 1022) in
  (2 ^ 52 <= mm < 2 ^ 54)%Z /\ B2R m = IZR mm * bpow radix2 (-53).
Proof.
intros m Fm Hm. cbv zeta.
destruct (FastLogReduce.pos_bits m Fm ltac:(lra)) as (c & Hc & Hb & Hv).
rewrite Hb.
destruct (split_52 c ltac:(lia)) as (Hcs & HE & HM).
destruct (magnitude_bounds c ltac:(lia)) as ((_ & Hlt) & Hge).
set (E := (c / 2 ^ 52)%Z) in *. set (M := (c mod 2 ^ 52)%Z) in *.
assert (HE1 : (1022 <= E)%Z).
{ assert (H : bpow radix2 (-1) < bpow radix2 (E - 1022))
    by (change (bpow radix2 (-1)) with (/ 2); lra).
  apply lt_bpow in H. lia. }
assert (HE2 : (E <= 1023)%Z).
{ assert (H : bpow radix2 (E - 1023) < bpow radix2 1)
    by (change (bpow radix2 1) with 2; specialize (Hge ltac:(lia)); lra).
  apply lt_bpow in H. lia. }
assert (Es : Z.shiftr c 52 = E) by (apply Z.shiftr_div_pow2; lia).
assert (Ef : Z.land c DyadicPow.FRAC = M).
{ change DyadicPow.FRAC with (Z.ones 52). apply Z.land_ones. lia. }
rewrite Es, Ef.
rewrite (Z.shiftl_mul_pow2 1 52), Z.lor_comm, Limbs.lor_low by lia.
rewrite Z.shiftl_mul_pow2 by lia.
split.
{ assert (H2 : (1 <= 2 ^ (E - 1022) <= 2)%Z).
  { destruct (Z.eq_dec E 1022) as [-> | HE3]; [| replace E with 1023%Z by lia]; cbn; lia. }
  nia. }
rewrite Hv, Hcs, magnitude_split by lia.
replace (E =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
replace (Z.max E 1) with E by lia.
unfold F2R; cbn [Fnum Fexp].
rewrite mult_IZR, pow2_R by lia.
rewrite Rmult_assoc, <- bpow_plus.
replace (E - 1022 + -53)%Z with (E - 1075)%Z by ring.
f_equal. f_equal. ring.
Qed.

Theorem acc_t_correct :
  forall x y tl th,
  is_finite x = true -> 0 < B2R x -> is_finite y = true -> B2R y <> 0 ->
  DyadicPow.acc_t x y = Some (tl, th) ->
  IZR tl * bpow radix2 (-115) <= B2R y * ln (B2R x) <= IZR th * bpow radix2 (-115).
Proof.
intros x y tl th Fx Hx Fy Hy0 Ht.
pose proof (FastLogReduce.ln_split_correct x Fx Hx) as HS.
unfold DyadicPow.acc_t in Ht.
destruct (DyadicLog.ln_split x) as ((e, m), i).
destruct HS as (Fm & Hi & He & Hxm & Hm1 & Hm2).
cbv beta iota zeta in Ht.
assert (Hi1 : 0 <= IZR i) by (apply IZR_le; lia).
assert (Hi2 : IZR i <= 361) by (apply IZR_le; lia).
rewrite plus_IZR in Hm1, Hm2.
pose proof (mm_correct m Fm ltac:(lra)) as HMM. cbv zeta in HMM.
set (mm := Z.shiftl (Z.lor (Z.land (to_bits m) DyadicPow.FRAC) (Z.shiftl 1 52))
             (Z.shiftr (to_bits m) 52 - 1022)) in Ht, HMM.
destruct HMM as (Hmm & Hmv).
destruct (acc_ln_correct i Hi) as (HR & Hg & HTa & HT0 & HTb).
set (R := DyadicPow.acc_r i) in *. set (g := DyadicPow.acc_g i) in *.
set (T := DyadicPow.acc_ln i) in *.
set (Zz := (mm * R - 2 ^ 63)%Z) in Ht.
destruct (2 ^ 54 <? Z.abs Zz)%Z eqn:Ea; [discriminate Ht |].
apply Z.ltb_ge in Ea.
pose proof (log_q_correct (Z.abs Zz) (0 <? Zz)%Z ltac:(lia)) as HQ.
destruct (DyadicPow.log_q 13 (0 <? Zz) (Z.abs Zz) (DyadicPow.log_c 13) (DyadicPow.log_c 13 + 1))
  as (ql, qh).
destruct HQ as (Hql & Hqh & HQ).
destruct (DyadicPow.odd_parts y) as (my, ey) eqn:Eo.
destruct (DyPowRules.odd_parts_spec y my ey Fy Hy0 Eo) as (_ & Hmy & Hey & Hya).
cbv beta iota in Ht.
destruct (DyadicPow.shr_dn (DyadicPow.mul_wide (my * Z.abs e) DyadicPow.LN2) (13 - ey))
  as [loA |] eqn:EA1; [| discriminate Ht].
destruct (DyadicPow.shr_up (DyadicPow.mul_wide (my * Z.abs e) (DyadicPow.LN2 + 1)) (13 - ey))
  as [hiA |] eqn:EA2; [| discriminate Ht].
destruct (DyadicPow.signed (xorb (lt y zero) (e <? 0)) loA hiA) as [(al, ah) |] eqn:EA3;
  [| discriminate Ht].
destruct (DyadicPow.shr_dn (DyadicPow.mul_wide my (Z.abs T - (if T <? 0 then 1 else 0)%Z))
  (12 + g - ey)) as [loB |] eqn:EB1; [| discriminate Ht].
destruct (DyadicPow.shr_up (DyadicPow.mul_wide my (Z.abs T + (if 0 <? T then 1 else 0)%Z))
  (12 + g - ey)) as [hiB |] eqn:EB2; [| discriminate Ht].
destruct (DyadicPow.signed (xorb (lt y zero) (T <? 0)) loB hiB) as [(bl, bh) |] eqn:EB3;
  [| discriminate Ht].
destruct (DyadicPow.shr_dn (DyadicPow.mul_wide (my * Z.abs Zz) (ql - 1)) (75 - ey))
  as [loC |] eqn:EC1; [| discriminate Ht].
destruct (DyadicPow.shr_up (DyadicPow.mul_wide (my * Z.abs Zz) (qh + 1)) (75 - ey))
  as [hiC |] eqn:EC2; [| discriminate Ht].
destruct (DyadicPow.signed (xorb (lt y zero) (Zz <? 0)) loC hiC) as [(cl, ch) |] eqn:EC3;
  [| discriminate Ht].
destruct (checked_i 128 (al + bl)) as [t1 |] eqn:E1; [| discriminate Ht].
destruct (checked_i 128 (t1 + cl)) as [t2 |] eqn:E2; [| discriminate Ht].
destruct (checked_i 128 (ah + bh)) as [h1 |] eqn:E3; [| discriminate Ht].
destruct (checked_i 128 (h1 + ch)) as [h2 |] eqn:E4; [| discriminate Ht].
injection Ht as Etl Eth. subst tl th.
apply checked_i_eq in E1, E2, E3, E4. subst t1 t2 h1 h2.
(* The reals: the sign of [y], [r] and [z]. *)
assert (Hny : if lt y zero then B2R y < 0 else 0 <= B2R y).
{ unfold lt. rewrite Bltb_correct by easy. change (B2R zero) with 0.
  destruct (Rlt_bool_spec (B2R y) 0) as [H | H]; exact H. }
assert (Hln2 : 0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra).
assert (HR1 : 1 <= IZR R) by (apply IZR_le; lia).
set (r := IZR R * bpow radix2 (-10)) in *.
assert (Hr : 0 < r) by (unfold r; apply Rmult_lt_0_compat; [lra | apply bpow_gt_0]).
set (z := IZR Zz * bpow radix2 (-63)).
assert (Hrm : r * B2R m = 1 + z).
{ unfold r, z, Zz. rewrite Hmv, minus_IZR, mult_IZR, (pow2_R 63) by lia.
  assert (H1 : bpow radix2 63 * bpow radix2 (-63) = 1) by (rewrite <- bpow_plus; reflexivity).
  assert (H2 : bpow radix2 (-10) * bpow radix2 (-53) = bpow radix2 (-63))
    by (rewrite <- bpow_plus; reflexivity).
  transitivity (IZR mm * IZR R * (bpow radix2 (-10) * bpow radix2 (-53))); [ring |].
  rewrite H2, Rmult_minus_distr_r, H1. ring. }
assert (Hza : Rabs z = IZR (Z.abs Zz) * bpow radix2 (-63)).
{ unfold z. rewrite Rabs_mult, abs_IZR, (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0.
  reflexivity. }
assert (Hz9 : Rabs z <= / 512).
{ rewrite Hza. change (/ 512) with (bpow radix2 (-9)).
  replace (-9)%Z with (54 + -63)%Z by reflexivity. rewrite bpow_plus, <- (pow2_R 54) by lia.
  apply Rmult_le_compat_r; [apply bpow_ge_0 | apply IZR_le; exact Ea]. }
assert (Hm0 : 0 < B2R m) by lra.
assert (Hln : ln (B2R x) = IZR e * ln 2 + - ln r + ln (1 + z)).
{ rewrite Hxm, ln_mult by (try apply bpow_gt_0; lra).
  rewrite ln_bpow2, <- Hrm, ln_mult by lra. ring. }
(* y e ln 2 *)
assert (HA : IZR al * bpow radix2 (-115) <= B2R y * (IZR e * ln 2) <=
             IZR ah * bpow radix2 (-115)).
{ assert (Hw : if (e <? 0)%Z then IZR e * ln 2 <= 0 else 0 <= IZR e * ln 2).
  { destruct (Z.ltb_spec e 0) as [H | H].
    - assert (IZR e < 0) by (apply IZR_lt; lia). nra.
    - assert (0 <= IZR e) by (apply IZR_le; lia). nra. }
  rewrite (sign_mul _ _ _ _ Hny Hw), Hya, Rabs_mult, <- abs_IZR, (Rabs_pos_eq (ln 2)) by lra.
  destruct ln2_acc_bounds as (HL1 & HL2 & HL3).
  assert (Hae : (0 <= my * Z.abs e <= 2 ^ 53 * 1074)%Z)
    by (split; [apply Z.mul_nonneg_nonneg | apply Z.mul_le_mono_nonneg]; lia).
  apply (term_bounds _ (my * Z.abs e) DyadicPow.LN2 (DyadicPow.LN2 + 1) (13 - ey) loA hiA);
    try assumption; try lia.
  rewrite <- !Z.mul_assoc. apply (scale_bounds _ _ _ (-128)); [lia | lia |].
  assert (HE : 0 <= IZR (Z.abs e)) by (apply IZR_le; lia).
  rewrite !mult_IZR. split.
  - rewrite Rmult_assoc. apply Rmult_le_compat_l; [exact HE | apply HL3].
  - rewrite Rmult_assoc. apply Rmult_le_compat_l; [exact HE | apply HL3]. }
(* y (-ln r) *)
assert (HB : IZR bl * bpow radix2 (-115) <= B2R y * - ln r <= IZR bh * bpow radix2 (-115)).
{ pose proof (bpow_gt_0 radix2 (- (127 + g))) as HK.
  rewrite plus_IZR in HTb.
  assert (Hw : if (T <? 0)%Z then - ln r <= 0 else 0 <= - ln r).
  { destruct (Z.ltb_spec T 0) as [H | H].
    - assert (IZR T <= -1) by (apply (IZR_le T (-1)); lia). nra.
    - assert (0 <= IZR T) by (apply IZR_le; lia). nra. }
  rewrite (sign_mul _ _ _ _ Hny Hw), Hya.
  apply (term_bounds _ my (Z.abs T - (if T <? 0 then 1 else 0)%Z)
    (Z.abs T + (if 0 <? T then 1 else 0)%Z) (12 + g - ey) loB hiB); try assumption.
  - lia.
  - destruct (Z.ltb_spec T 0); lia.
  - destruct (Z.ltb_spec 0 T); lia.
  - apply (scale_bounds _ _ _ (- (127 + g))); [lia | lia |].
    destruct (Z.lt_trichotomy T 0) as [HT | [HT | HT]].
    + replace (T <? 0)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      replace (0 <? T)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      assert (IZR T <= -1) by (apply (IZR_le T (-1)); lia).
      rewrite Z.abs_neq, Rabs_left1 by (lia || nra).
      rewrite minus_IZR, plus_IZR, opp_IZR. lra.
    + assert (Hr1 : r = 1).
      { unfold r. rewrite (HT0 HT). change (bpow radix2 (-10)) with (/ 1024). lra. }
      rewrite Hr1, ln_1, HT. cbn. rewrite Ropp_0, Rabs_R0. lra.
    + replace (T <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      replace (0 <? T)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      assert (0 <= IZR T) by (apply IZR_le; lia).
      rewrite Z.abs_eq, Rabs_pos_eq by (lia || nra).
      rewrite minus_IZR, plus_IZR. lra. }
(* y ln(1 + z) *)
assert (HC : IZR cl * bpow radix2 (-115) <= B2R y * ln (1 + z) <=
             IZR ch * bpow radix2 (-115)).
{ assert (H1z : 0 < 1 + z) by (apply Rabs_le_inv in Hz9; lra).
  assert (HzZ : (if (Zz <? 0)%Z then z < 0 else 0 <= z)).
  { unfold z. pose proof (bpow_gt_0 radix2 (-63)) as H63.
    destruct (Z.ltb_spec Zz 0) as [H | H].
    - assert (IZR Zz < 0) by (apply IZR_lt; lia). nra.
    - assert (0 <= IZR Zz) by (apply IZR_le; lia). nra. }
  assert (Hw : if (Zz <? 0)%Z then ln (1 + z) <= 0 else 0 <= ln (1 + z)).
  { destruct (Zz <? 0)%Z.
    - rewrite <- ln_1. left. apply ln_increasing; lra.
    - destruct (Req_dec z 0) as [-> | Hz0].
      + rewrite Rplus_0_r, ln_1. lra.
      + rewrite <- ln_1. left. apply ln_increasing; lra. }
  rewrite (sign_mul _ _ _ _ Hny Hw), Hya.
  assert (Hn : (0 <= my * Z.abs Zz <= 2 ^ 53 * 2 ^ 54)%Z)
    by (split; [apply Z.mul_nonneg_nonneg | apply Z.mul_le_mono_nonneg]; lia).
  apply (term_bounds _ (my * Z.abs Zz) (ql - 1) (qh + 1) (75 - ey) loC hiC);
    try assumption; try lia.
  rewrite <- !Z.mul_assoc. apply (scale_bounds _ _ _ (-190)); [lia | lia |].
  destruct (Z.eq_dec Zz 0) as [HZ0 | HZ0].
  - assert (Hz0 : z = 0) by (unfold z; rewrite HZ0; ring).
    rewrite Hz0, Rplus_0_r, ln_1, Rabs_R0, HZ0. cbn [Z.abs]. rewrite !Z.mul_0_l, Rmult_0_l.
    lra.
  - specialize (HQ ltac:(lia)). cbv zeta in HQ.
    assert (Ez : IZR (if (0 <? Zz)%Z then Z.abs Zz else (- Z.abs Zz)%Z) * bpow radix2 (-63) = z).
    { unfold z. f_equal. f_equal. destruct (Z.ltb_spec 0 Zz); lia. }
    rewrite Ez in HQ.
    assert (Hz0 : z <> 0).
    { intros H. rewrite H, Rabs_R0 in Hza.
      assert (0 < IZR (Z.abs Zz)) by (apply IZR_lt; lia).
      pose proof (bpow_gt_0 radix2 (-63)). nra. }
    set (Q := ln (1 + z) / z) in HQ.
    assert (HlnQ : ln (1 + z) = z * Q) by (unfold Q; field; exact Hz0).
    pose proof (bpow_gt_0 radix2 (-127)) as HB0.
    assert (HQ1 : 0 < IZR (ql - 1)) by (apply IZR_lt; lia).
    assert (HQ0 : 0 < Q) by nra.
    rewrite HlnQ, Rabs_mult, Hza, (Rabs_pos_eq Q) by lra.
    assert (HE : bpow radix2 (-190) = bpow radix2 (-63) * bpow radix2 (-127))
      by (rewrite <- bpow_plus; reflexivity).
    assert (HZp : 0 <= IZR (Z.abs Zz) * bpow radix2 (-63))
      by (apply Rmult_le_pos; [apply IZR_le; lia | apply bpow_ge_0]).
    rewrite HE, !mult_IZR. split.
    + replace (IZR (Z.abs Zz) * IZR (ql - 1) * (bpow radix2 (-63) * bpow radix2 (-127))) with
        (IZR (Z.abs Zz) * bpow radix2 (-63) * (IZR (ql - 1) * bpow radix2 (-127))) by ring.
      apply Rmult_le_compat_l; [exact HZp | apply HQ].
    + replace (IZR (Z.abs Zz) * IZR (qh + 1) * (bpow radix2 (-63) * bpow radix2 (-127))) with
        (IZR (Z.abs Zz) * bpow radix2 (-63) * (IZR (qh + 1) * bpow radix2 (-127))) by ring.
      apply Rmult_le_compat_l; [exact HZp | apply HQ]. }
rewrite Hln.
replace (B2R y * (IZR e * ln 2 + - ln r + ln (1 + z))) with
  (B2R y * (IZR e * ln 2) + B2R y * - ln r + B2R y * ln (1 + z)) by ring.
rewrite !plus_IZR. lra.
Qed.
