(** The tables and constants of the accurate phase of x^y
    ([src/dyadic/pow/tables.rs] and [src/dyadic/pow/acc.rs], in
    [ModelPowTable.v] and [Model.v]): at each [i] of [ln_split], [r = R
    2^-10] for [R = DyadicPow.acc_r i], and [-ln r] in [[T, T + 1]] at
    2^-(127 + g) for [T = DyadicPow.acc_ln i] and [g = DyadicPow.acc_g i],
    with [T = 0] only where [r = 1]; [2^(j/64)] and [2^(j/4096)] in
    [[v, v + 1]] at 2^-127 for [v] the entry [j] of [DyadicPow.exp_hi] and
    [DyadicPow.exp_lo]; and ln 2 in [[LN2, LN2 + 1]] at 2^-128.

    Each entry is checked by [vm_compute] on integers, with the methods
    of [FastLogTables.v] and [FastExpTables.v] at a higher precision.
    -ln r = 2 atanh(s) for the rational s = (1024 - R) / (1024 + R), and
    [FastLogTables.lg_lo] and [FastLogTables.lg_hi] bound 2^256 atanh |s|
    by 30 terms of the series in fixed point with 256 fractional bits,
    each quotient rounded down or up; |s| < 0.171 on this table, so the
    remainder bound [2 s^61] of the 30 terms is below 2^-154, far below
    the unit 2^-(127 + g) >= 2^-135 of [T]. An entry [v] of the powers
    of 2 is checked as in [FastExpTables.entry_close]: [t -> t^N] is
    increasing on [t >= 0] and [(2^(j/N))^N = 2^j], so [(v 2^-127)^N <=
    2^j <= ((v + 1) 2^-127)^N], for [N = 64] or [4096], gives the
    enclosure; [FastExpTables.sq_up] and [FastExpTables.sq_dn] bound the
    two [N]-th powers by [n = 6] or [12] squarings at 256 fractional
    bits, rounded up and down. The checks of all 362 + 2 * 64 entries
    take about 15 s in [vm_compute], and as long again at [Qed]. *)

From Stdlib Require Import ZArith Reals Lra Lia List Bool.
From Flocq Require Import Core.Core.
From Fushimi Require Import Model Elementary.
From Fushimi Require FastLogTables FastExpTables DyConst.

Import ListNotations.

Open Scope R_scope.

(** ** Helpers *)

Local Lemma pow2_IZR : forall e, (0 <= e)%Z -> IZR (2 ^ e) = bpow radix2 e.
Proof. intros e He. rewrite <- IZR_Zpower by exact He. reflexivity. Qed.

(** ** The logarithms of [ACC_R]

    -ln r = 2 atanh(s) for [r = R 2^-10] and s = (1 - r) / (1 + r), with
    the sign of [s] taken out of the quotient. *)
Local Lemma ln_atanh :
  forall R, (0 < R)%Z ->
  - ln (IZR R * bpow radix2 (-10)) =
  (if (R <=? 1024)%Z then 1 else -1) *
    (2 * Ratanh (IZR (Z.abs (1024 - R)) / IZR (1024 + R))).
Proof.
intros R HR.
assert (HR0 : 0 < IZR R) by (apply IZR_lt; exact HR).
change (bpow radix2 (-10)) with (/ 1024).
assert (Hr0 : 0 < IZR R * / 1024) by lra.
rewrite plus_IZR.
destruct (Z.leb_spec R 1024) as [Hle | Hgt].
- rewrite Z.abs_eq by lia. rewrite minus_IZR.
  unfold Ratanh.
  replace ((1 + (IZR 1024 - IZR R) / (IZR 1024 + IZR R)) /
           (1 - (IZR 1024 - IZR R) / (IZR 1024 + IZR R)))
    with (/ (IZR R * / 1024)) by (field; lra).
  rewrite ln_Rinv by exact Hr0. field.
- rewrite Z.abs_neq by lia. rewrite opp_IZR, minus_IZR.
  unfold Ratanh.
  replace ((1 + - (IZR 1024 - IZR R) / (IZR 1024 + IZR R)) /
           (1 - - (IZR 1024 - IZR R) / (IZR 1024 + IZR R)))
    with (IZR R * / 1024) by (field; lra).
  field.
Qed.

(** The check of [T 2^-(127 + G) <= 2 atanh(a / b) <= (T + 1) 2^-(127 +
    G)] with 30 terms at 256 fractional bits *)
Local Definition ln_ser_okb (a b G T : Z) : bool :=
  (0 <=? a)%Z && (0 <? b)%Z && (2 * (a * a) <=? b * b)%Z && (0 <=? G)%Z && (G <=? 129)%Z &&
  (T * 2 ^ (129 - G) <=? 2 * FastLogTables.lg_lo 256 30 a b)%Z &&
  (2 * FastLogTables.lg_hi 256 30 a b <=? (T + 1) * 2 ^ (129 - G))%Z.

Local Lemma ln_ser_correct :
  forall a b G T, ln_ser_okb a b G T = true ->
  IZR T * bpow radix2 (- (127 + G)) <= 2 * Ratanh (IZR a / IZR b) <=
  IZR (T + 1) * bpow radix2 (- (127 + G)).
Proof.
intros a b G T Hok. unfold ln_ser_okb in Hok. repeat rewrite andb_true_iff in Hok.
destruct Hok as [[[[[[H1 H2] H3] H4] H5] H6] H7].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
apply Z.leb_le in H5. apply Z.leb_le in H6. apply Z.leb_le in H7.
destruct (FastLogTables.lg_atanh_bounds 256 30 a b ltac:(lia) H1 H2 H3) as [Lo Hi].
change (Z.opp 256) with (-256)%Z in Lo, Hi.
set (lo := FastLogTables.lg_lo 256 30 a b) in *.
set (hi := FastLogTables.lg_hi 256 30 a b) in *.
(* Both checks in the form of [FastLogTables.lg_cmp] at the scale 2^-256 *)
assert (E1 : (- (127 + G) - -256 = 129 - G)%Z) by lia.
assert (E2 : (-256 - -256 = 0)%Z) by lia.
pose proof (FastLogTables.lg_cmp T (2 * lo) (- (127 + G)) (-256) (-256) ltac:(lia) ltac:(lia))
  as K1.
pose proof (FastLogTables.lg_cmp (2 * hi) (T + 1) (-256) (- (127 + G)) (-256) ltac:(lia) ltac:(lia))
  as K2.
rewrite E1, E2, Z.pow_0_r, Z.mul_1_r in K1, K2.
specialize (K1 H6). specialize (K2 H7).
rewrite mult_IZR in K1, K2.
split; lra.
Qed.

(** The check of the entry [(R, G, T)] *)
Local Definition ln_entry_okb (R G T : Z) : bool :=
  (1 <=? R)%Z && (R <? 2 ^ 11)%Z && (0 <=? G)%Z && (G <? 64)%Z && (Z.abs T <? 2 ^ 127)%Z &&
  (negb (T =? 0)%Z || (R =? 1024)%Z) &&
  ln_ser_okb (Z.abs (1024 - R)) (1024 + R) G (if (R <=? 1024)%Z then T else - (T + 1))%Z.

Local Lemma ln_entry_correct :
  forall R G T, ln_entry_okb R G T = true ->
  (1 <= R < 2 ^ 11)%Z /\ (0 <= G < 64)%Z /\ (Z.abs T < 2 ^ 127)%Z /\ (T = 0 -> R = 1024)%Z /\
  IZR T * bpow radix2 (- (127 + G)) <= - ln (IZR R * bpow radix2 (-10)) <=
    IZR (T + 1) * bpow radix2 (- (127 + G)).
Proof.
intros R G T Hok. unfold ln_entry_okb in Hok. repeat rewrite andb_true_iff in Hok.
destruct Hok as [[[[[[H1 H2] H3] H4] H5] H6] H7].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
apply Z.ltb_lt in H5. apply orb_true_iff in H6.
split; [lia|]. split; [lia|]. split; [exact H5|].
split.
{ intros ->. destruct H6 as [H6|H6]; [discriminate H6 | apply Z.eqb_eq; exact H6]. }
apply ln_ser_correct in H7.
rewrite ln_atanh by lia.
destruct (R <=? 1024)%Z.
- lra.
- rewrite opp_IZR, plus_IZR in H7.
  replace (- (T + 1) + 1)%Z with (- T)%Z in H7 by ring.
  rewrite opp_IZR in H7. rewrite (plus_IZR T 1). lra.
Qed.

Local Fixpoint ln_all_okb (rs gs ts : list Z) : bool :=
  match rs, gs, ts with
  | R :: rs, G :: gs, T :: ts => ln_entry_okb R G T && ln_all_okb rs gs ts
  | [], [], [] => true
  | _, _, _ => false
  end.

Local Lemma ln_all_okb_nth :
  forall rs gs ts k, ln_all_okb rs gs ts = true -> (k < length rs)%nat ->
  ln_entry_okb (nth k rs 0%Z) (nth k gs 0%Z) (nth k ts 0%Z) = true.
Proof.
intros rs; induction rs as [|R rs IH]; intros gs ts k H Hk; [cbn [length] in Hk; lia|].
destruct gs as [|G gs]; [cbn [ln_all_okb] in H; discriminate H|].
destruct ts as [|T ts]; [cbn [ln_all_okb] in H; discriminate H|].
cbn [ln_all_okb] in H. apply andb_prop in H as [H1 H2].
destruct k as [|k]; cbn [nth]; [exact H1|].
apply IH; [exact H2 | cbn [length] in Hk; lia].
Qed.

(** The check of all 362 entries ([vm_compute]) *)
Local Lemma ln_table_ok : ln_all_okb DyadicPow.ACC_R DyadicPow.ACC_G DyadicPow.ACC_LN = true.
Proof. vm_compute. reflexivity. Qed.

Local Lemma ln_table_length : length DyadicPow.ACC_R = 362%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem acc_ln_correct :
  forall i, (0 <= i < 362)%Z ->
  (1 <= DyadicPow.acc_r i < 2 ^ 11)%Z /\ (0 <= DyadicPow.acc_g i < 64)%Z /\
  (Z.abs (DyadicPow.acc_ln i) < 2 ^ 127)%Z /\
  (DyadicPow.acc_ln i = 0 -> DyadicPow.acc_r i = 1024)%Z /\
  IZR (DyadicPow.acc_ln i) * bpow radix2 (- (127 + DyadicPow.acc_g i)) <=
    - ln (IZR (DyadicPow.acc_r i) * bpow radix2 (-10)) <=
    IZR (DyadicPow.acc_ln i + 1) * bpow radix2 (- (127 + DyadicPow.acc_g i)).
Proof.
intros i Hi.
pose proof (ln_all_okb_nth _ _ _ (Z.to_nat i) ln_table_ok
              ltac:(rewrite ln_table_length; lia)) as He.
unfold DyadicPow.acc_r, DyadicPow.acc_g, DyadicPow.acc_ln.
exact (ln_entry_correct _ _ _ He).
Qed.

(** ** The powers of 2 *)

(** The check of an entry [v] for [2^(j/2^n)]: [2^127 <= v < 2^128 - 1],
    and the squarings of [v 2^-127] rounded up and of [(v + 1) 2^-127]
    rounded down, at 256 fractional bits, bracket [2^j]. *)
Local Definition exp_entry_okb (n : nat) (j v : Z) : bool :=
  (2 ^ 127 <=? v)%Z && (v + 1 <? 2 ^ 128)%Z && (0 <=? j)%Z &&
  (FastExpTables.sq_up n 256 (v * 2 ^ 129) <=? 2 ^ (256 + j))%Z &&
  (2 ^ (256 + j) <=? FastExpTables.sq_dn n 256 ((v + 1) * 2 ^ 129))%Z.

Local Lemma exp_entry_correct :
  forall n d j v, d = INR (2 ^ n)%nat -> exp_entry_okb n j v = true ->
  (2 ^ 127 <= v)%Z /\ (v + 1 < 2 ^ 128)%Z /\
  IZR v * bpow radix2 (-127) <= Rexp2 (IZR j / d) <= IZR (v + 1) * bpow radix2 (-127).
Proof.
intros n d j v Hd Hok.
unfold exp_entry_okb in Hok. repeat rewrite andb_true_iff in Hok.
destruct Hok as [[[[H1 H2] H3] H4] H5].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
apply Z.leb_le in H4. apply Z.leb_le in H5.
split; [exact H1|]. split; [exact H2|].
assert (P127 : (0 < 2 ^ 127)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (P129 : (0 < 2 ^ 129)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (Hk : (2 ^ n <> 0)%nat) by (apply Nat.pow_nonzero; lia).
set (E := Rexp2 (IZR j / d)).
assert (HE : E ^ (2 ^ n)%nat = bpow radix2 j)
  by (unfold E; apply FastExpTables.rexp2_pow; assumption).
assert (HE0 : 0 < E) by (unfold E, Rexp2, Rpower; apply exp_pos).
assert (Hb : 0 < bpow radix2 (-256)) by apply bpow_gt_0.
assert (H2j : IZR (2 ^ (256 + j)) * bpow radix2 (-256) = bpow radix2 j).
{ rewrite pow2_IZR, <- bpow_plus by lia. f_equal. ring. }
(* [w 2^-127] is [(w 2^129) 2^-256]. *)
assert (Sc : forall w, IZR w * bpow radix2 (-127) = IZR (w * 2 ^ 129) * bpow radix2 (-256)).
{ intros w. rewrite mult_IZR, pow2_IZR, Rmult_assoc, <- bpow_plus by lia. reflexivity. }
split.
- set (x := IZR v * bpow radix2 (-127)).
  assert (Hx : 0 <= x) by (apply Rmult_le_pos; [apply IZR_le; lia | apply bpow_ge_0]).
  destruct (Rle_or_lt x E) as [H|H]; [exact H | exfalso].
  pose proof (FastExpTables.pow_lt_compat E x _ (conj (Rlt_le _ _ HE0) H) Hk) as K1.
  pose proof (FastExpTables.sq_up_correct n 256 (v * 2 ^ 129) x ltac:(lia) Hx
                (Req_le _ _ (Sc v))) as K2.
  change (Z.opp 256) with (-256)%Z in K2.
  apply IZR_le in H4. pose proof (Rmult_le_compat_r _ _ _ (Rlt_le _ _ Hb) H4) as K3.
  lra.
- set (y := IZR (v + 1) * bpow radix2 (-127)).
  assert (Hy : 0 <= y) by (apply Rmult_le_pos; [apply IZR_le; lia | apply bpow_ge_0]).
  destruct (Rle_or_lt E y) as [H|H]; [exact H | exfalso].
  pose proof (FastExpTables.pow_lt_compat y E _ (conj Hy H) Hk) as K1.
  pose proof (FastExpTables.sq_dn_correct n 256 ((v + 1) * 2 ^ 129) y ltac:(lia)
                ltac:(apply Z.mul_nonneg_nonneg; lia) (Req_le _ _ (eq_sym (Sc (v + 1)%Z))))
    as K2.
  change (Z.opp 256) with (-256)%Z in K2.
  apply IZR_le in H5. pose proof (Rmult_le_compat_r _ _ _ (Rlt_le _ _ Hb) H5) as K3.
  lra.
Qed.

Local Fixpoint exp_all_okb (n : nat) (t : list Z) (j : Z) : bool :=
  match t with
  | [] => true
  | v :: t => exp_entry_okb n j v && exp_all_okb n t (j + 1)
  end.

Local Lemma exp_all_okb_nth :
  forall n t j0 k, exp_all_okb n t j0 = true -> (k < length t)%nat ->
  exp_entry_okb n (j0 + Z.of_nat k) (nth k t 0%Z) = true.
Proof.
intros n t; induction t as [|v t IH]; intros j0 k H Hk; [cbn [length] in Hk; lia|].
cbn [exp_all_okb] in H. apply andb_prop in H as [H1 H2].
destruct k as [|k]; cbn [nth].
- replace (j0 + Z.of_nat 0)%Z with j0 by lia. exact H1.
- replace (j0 + Z.of_nat (S k))%Z with ((j0 + 1) + Z.of_nat k)%Z by lia.
  apply IH; [exact H2 | cbn [length] in Hk; lia].
Qed.

(** The checks of the 64 entries of each table ([vm_compute]) *)
Local Lemma exp_hi_ok : exp_all_okb 6 DyadicPow.EXP_HI 0 = true.
Proof. vm_compute. reflexivity. Qed.

Local Lemma exp_lo_ok : exp_all_okb 12 DyadicPow.EXP_LO 0 = true.
Proof. vm_compute. reflexivity. Qed.

Local Lemma exp_hi_length : length DyadicPow.EXP_HI = 64%nat.
Proof. vm_compute. reflexivity. Qed.

Local Lemma exp_lo_length : length DyadicPow.EXP_LO = 64%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem exp_hi_correct :
  forall j, (0 <= j < 64)%Z ->
  (2 ^ 127 <= DyadicPow.exp_hi j)%Z /\ (DyadicPow.exp_hi j + 1 < 2 ^ 128)%Z /\
  IZR (DyadicPow.exp_hi j) * bpow radix2 (-127) <= Rexp2 (IZR j / 64) <=
    IZR (DyadicPow.exp_hi j + 1) * bpow radix2 (-127).
Proof.
intros j Hj.
pose proof (exp_all_okb_nth 6 DyadicPow.EXP_HI 0 (Z.to_nat j) exp_hi_ok
              ltac:(rewrite exp_hi_length; lia)) as He.
rewrite Z.add_0_l, Z2Nat.id in He by lia.
unfold DyadicPow.exp_hi.
apply (exp_entry_correct 6); [rewrite INR_IZR_INZ; reflexivity | exact He].
Qed.

Theorem exp_lo_correct :
  forall j, (0 <= j < 64)%Z ->
  (2 ^ 127 <= DyadicPow.exp_lo j)%Z /\ (DyadicPow.exp_lo j + 1 < 2 ^ 128)%Z /\
  IZR (DyadicPow.exp_lo j) * bpow radix2 (-127) <= Rexp2 (IZR j / 4096) <=
    IZR (DyadicPow.exp_lo j + 1) * bpow radix2 (-127).
Proof.
intros j Hj.
pose proof (exp_all_okb_nth 12 DyadicPow.EXP_LO 0 (Z.to_nat j) exp_lo_ok
              ltac:(rewrite exp_lo_length; lia)) as He.
rewrite Z.add_0_l, Z2Nat.id in He by lia.
unfold DyadicPow.exp_lo.
apply (exp_entry_correct 12); [rewrite INR_IZR_INZ; reflexivity | exact He].
Qed.

(** Every entry of [t] is at most [M] (the default of [nth] too). *)
Local Lemma nth_le_max :
  forall t k M, forallb (fun v => (v <=? M)%Z) t = true -> (0 <= M)%Z -> (nth k t 0 <= M)%Z.
Proof.
intros t; induction t as [|v t IH]; intros k M H HM; destruct k as [|k]; cbn [nth];
  try exact HM; cbn [forallb] in H; apply andb_prop in H as [H1 H2].
- apply Z.leb_le. exact H1.
- apply IH; assumption.
Qed.

(** The largest entries of the two tables, and their product *)
Local Definition prod_okb (Mh Ml : Z) : bool :=
  forallb (fun v => (v <=? Mh)%Z) DyadicPow.EXP_HI &&
  forallb (fun v => (v <=? Ml)%Z) DyadicPow.EXP_LO &&
  (0 <=? Mh)%Z && (0 <=? Ml)%Z && ((Mh + 1) * (Ml + 1) <? 2 ^ 255 - 2 ^ 127)%Z.

Local Lemma prod_ok : prod_okb (nth 63 DyadicPow.EXP_HI 0%Z) (nth 63 DyadicPow.EXP_LO 0%Z) = true.
Proof. vm_compute. reflexivity. Qed.

(** The product of the upper bounds of two entries is below 2^255 - 2^127,
    as 2^(63/64 + 63/4096) < 2, so that [mul_up] at 127 takes it and
    rounds it up to below 2^128. *)
Lemma exp_prod_bound :
  forall j1 j2, (0 <= j1 < 64)%Z -> (0 <= j2 < 64)%Z ->
  ((DyadicPow.exp_hi j1 + 1) * (DyadicPow.exp_lo j2 + 1) < 2 ^ 255 - 2 ^ 127)%Z.
Proof.
intros j1 j2 H1 H2.
pose proof prod_ok as Hok. unfold prod_okb in Hok. repeat rewrite andb_true_iff in Hok.
destruct Hok as [[[[Fh Fl] Zh] Zl] Hp].
apply Z.leb_le in Zh. apply Z.leb_le in Zl. apply Z.ltb_lt in Hp.
pose proof (nth_le_max _ (Z.to_nat j1) _ Fh Zh) as Ah.
pose proof (nth_le_max _ (Z.to_nat j2) _ Fl Zl) as Al.
destruct (exp_hi_correct j1 H1) as [Bh _]. destruct (exp_lo_correct j2 H2) as [Bl _].
unfold DyadicPow.exp_hi, DyadicPow.exp_lo in *.
assert (P127 : (0 < 2 ^ 127)%Z) by (apply Z.pow_pos_nonneg; lia).
eapply Z.le_lt_trans; [| exact Hp].
apply Z.mul_le_mono_nonneg; lia.
Qed.

(** ** ln 2 *)

Theorem ln2_acc_bounds :
  (2 ^ 127 <= DyadicPow.LN2)%Z /\ (DyadicPow.LN2 + 1 < 2 ^ 128)%Z /\
  IZR DyadicPow.LN2 * bpow radix2 (-128) <= ln 2 <= IZR (DyadicPow.LN2 + 1) * bpow radix2 (-128).
Proof.
destruct DyConst.LN2_bounds as [L U].
(* The bounds of [DyConst.v] at 2^-4224 against [LN2] at 2^-128 *)
assert (H1 : (2 ^ 127 <=? DyadicPow.LN2)%Z = true) by (vm_compute; reflexivity).
assert (H2 : (DyadicPow.LN2 + 1 <? 2 ^ 128)%Z = true) by (vm_compute; reflexivity).
assert (H3 : (DyadicPow.LN2 * 2 ^ (-128 - -4224) <=?
              Limbs.val DyadicConsts.LN2 * 2 ^ (-4224 - -4224))%Z = true)
  by (vm_compute; reflexivity).
assert (H4 : ((Limbs.val DyadicConsts.LN2 + 1) * 2 ^ (-4224 - -4224) <=?
              (DyadicPow.LN2 + 1) * 2 ^ (-128 - -4224))%Z = true)
  by (vm_compute; reflexivity).
apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
split; [exact H1|]. split; [exact H2|].
pose proof (FastLogTables.lg_cmp _ _ (-128) (-4224) (-4224) ltac:(lia) ltac:(lia) H3) as K3.
pose proof (FastLogTables.lg_cmp _ _ (-4224) (-128) (-4224) ltac:(lia) ltac:(lia) H4) as K4.
rewrite plus_IZR in K4.
split; lra.
Qed.
