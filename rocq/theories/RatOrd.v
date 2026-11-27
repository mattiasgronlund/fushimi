(** * [impl Ord for Rat] compares the values of two [Rat]s

    [rat_cmp_correct] shows that [impl Ord for Rat] in
    [src/parse/rat.rs] compares the values [rat_R] of two [Rat]s with
    [rat_ok], for [num] and [den] below [2 ^ 2 ^ 61], under which the [u64]
    sum of bit counts in [cmp_pow5] cannot overflow. [log2_5_bounds]
    bounds [m * log2 5] by integers ([log2_5_bounds_correct]), from the
    bounds of [ln 2] and [ln 10] of [ConstLn.v], as [log2 5] is
    [ln 10 / ln 2 - 1]. [cmp_abs_with] decides from the numbers of bits and
    the exponents where they differ by enough, and otherwise by
    [cmp_pow5] ([RatPow5.v]). *)

From Stdlib Require Import ZArith Reals Lra Lia QArith Qreals.
From Flocq Require Import Core.Core.
From Fushimi Require Import Model NatOps ConstLn RatPow5.

Open Scope R_scope.

(** ** Checked integer operations that cannot overflow *)

Lemma checked_u_some : forall w z, (0 <= z < 2 ^ w)%Z -> checked_u w z = Some z.
Proof.
  intros w z Hz. unfold checked_u.
  replace ((0 <=? z) && (z <? 2 ^ w))%Z with true; [reflexivity|].
  symmetry. apply Bool.andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma checked_i_128 : forall z, (- 2 ^ 100 <= z <= 2 ^ 100)%Z -> checked_i 128 z = Some z.
Proof.
  intros z Hz. unfold checked_i.
  replace ((- 2 ^ (128 - 1) <=? z) && (z <? 2 ^ (128 - 1)))%Z with true; [reflexivity|].
  symmetry. apply Bool.andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(** ** Bounds of [log2 5] *)

Lemma Q2R_Z : forall z, Q2R (z # 1) = IZR z.
Proof. intros z. unfold Q2R; simpl. rewrite Rinv_1. ring. Qed.

Lemma ln2_pos : 0 < ln 2.
Proof. rewrite <- ln_1. apply ln_increasing; lra. Qed.

Lemma ln2_neq : ln 2 <> 0.
Proof. apply Rgt_not_eq. exact ln2_pos. Qed.

Lemma ln5_eq : ln 5 = ln 10 - ln 2.
Proof. replace 10 with (2 * 5) by lra. rewrite ln_mult by lra. ring. Qed.

(** [LOG2_5_LO <= 2 ^ 64 * log2 5 <= LOG2_5_LO + 1], with [log2 5] as
    [(ln 10 - ln 2) / ln 2], from rational bounds of [ln 2] and [ln 10]
    whose margins [vm_compute] checks. *)
Lemma log2_5_lo_hi :
  IZR 42832013323943160825 <= IZR (2 ^ 64) * (ln 5 / ln 2) <= IZR 42832013323943160826.
Proof.
  assert (Q1 : ((42832013323943160825 # 1) * ln2_hi
                <= (18446744073709551616 # 1) * (ln10_lo - ln2_hi))%Q)
    by (vm_compute; intro H; discriminate H).
  assert (Q2 : ((18446744073709551616 # 1) * (ln10_hi - ln2_lo)
                <= (42832013323943160826 # 1) * ln2_lo)%Q)
    by (vm_compute; intro H; discriminate H).
  apply Qle_Rle in Q1, Q2.
  rewrite !Q2R_mult, Q2R_minus, !Q2R_Z in Q1.
  rewrite !Q2R_mult, Q2R_minus, !Q2R_Z in Q2.
  pose proof LN_2_Q as [A B]. pose proof LN_10_Q as [C D]. pose proof ln2_pos as L2.
  change (2 ^ 64)%Z with 18446744073709551616%Z.
  rewrite ln5_eq. split.
  - apply (Rmult_le_reg_r (ln 2)); [exact L2|].
    replace (IZR 18446744073709551616 * ((ln 10 - ln 2) / ln 2) * ln 2)
      with (IZR 18446744073709551616 * (ln 10 - ln 2)) by (field; exact ln2_neq).
    lra.
  - apply (Rmult_le_reg_r (ln 2)); [exact L2|].
    replace (IZR 18446744073709551616 * ((ln 10 - ln 2) / ln 2) * ln 2)
      with (IZR 18446744073709551616 * (ln 10 - ln 2)) by (field; exact ln2_neq).
    lra.
Qed.

Theorem log2_5_bounds_correct :
  forall m, (0 <= m < 2 ^ 32)%Z ->
  exists lo hi, rat_log2_5_bounds m = Some (lo, hi) /\
  IZR lo <= IZR m * (ln 5 / ln 2) <= IZR hi /\
  (hi - lo <= 2)%Z /\ (0 <= lo)%Z /\ (hi < 2 ^ 35)%Z.
Proof.
  intros m Hm.
  assert (HLO : LOG2_5_LO = 42832013323943160825%Z) by reflexivity.
  assert (HHI : LOG2_5_HI = 42832013323943160826%Z) by reflexivity.
  unfold rat_log2_5_bounds. rewrite HLO, HHI.
  rewrite (checked_u_some 128 (m * 42832013323943160825)) by lia.
  rewrite (checked_u_some 128 (m * 42832013323943160826 + (2 ^ 64 - 1))) by lia.
  cbv beta iota zeta.
  rewrite !Z.shiftr_div_pow2 by lia.
  (* The quotients [q0] and [q1] by [2 ^ 64], with their remainders. *)
  pose proof (Z.div_mod (m * 42832013323943160825) (2 ^ 64) ltac:(lia)) as D0.
  pose proof (Z.mod_pos_bound (m * 42832013323943160825) (2 ^ 64) ltac:(lia)) as R0.
  pose proof (Z.div_mod (m * 42832013323943160826 + (2 ^ 64 - 1)) (2 ^ 64) ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (m * 42832013323943160826 + (2 ^ 64 - 1)) (2 ^ 64) ltac:(lia))
    as R1.
  set (q0 := (m * 42832013323943160825 / 2 ^ 64)%Z) in *.
  set (r0 := ((m * 42832013323943160825) mod 2 ^ 64)%Z) in *.
  set (q1 := ((m * 42832013323943160826 + (2 ^ 64 - 1)) / 2 ^ 64)%Z) in *.
  set (r1 := ((m * 42832013323943160826 + (2 ^ 64 - 1)) mod 2 ^ 64)%Z) in *.
  clearbody q0 r0 q1 r1.
  exists q0, q1. split.
  { rewrite !Z.mod_small by lia. rewrite !Z.add_simpl_r. reflexivity. }
  split; [|lia].
  (* [2 ^ 64 q0 <= m LO] and [m (LO + 1) <= 2 ^ 64 q1], and
     [LO <= 2 ^ 64 log2 5 <= LO + 1]. *)
  assert (Z0 : (2 ^ 64 * q0 <= m * 42832013323943160825)%Z) by lia.
  assert (Z1 : (m * 42832013323943160826 <= 2 ^ 64 * q1)%Z) by lia.
  apply IZR_le in Z0, Z1. rewrite !mult_IZR in Z0, Z1.
  pose proof log2_5_lo_hi as [A0 A1].
  assert (HT : 0 < IZR (2 ^ 64)) by (apply IZR_lt; lia).
  assert (Hm0 : 0 <= IZR m) by (apply IZR_le; lia).
  split.
  - apply (Rmult_le_reg_l (IZR (2 ^ 64))); [exact HT|].
    apply Rle_trans with (IZR m * IZR 42832013323943160825); [exact Z0|].
    replace (IZR (2 ^ 64) * (IZR m * (ln 5 / ln 2)))
      with (IZR m * (IZR (2 ^ 64) * (ln 5 / ln 2))) by ring.
    apply Rmult_le_compat_l; [exact Hm0 | exact A0].
  - apply (Rmult_le_reg_l (IZR (2 ^ 64))); [exact HT|].
    apply Rle_trans with (IZR m * IZR 42832013323943160826); [|exact Z1].
    replace (IZR (2 ^ 64) * (IZR m * (ln 5 / ln 2)))
      with (IZR m * (IZR (2 ^ 64) * (ln 5 / ln 2))) by ring.
    apply Rmult_le_compat_l; [exact Hm0 | exact A1].
Qed.

(** ** Powers of 2 and 5 *)

Lemma IZR_pow2 : forall k, (0 <= k)%Z -> IZR (2 ^ k) = bpow radix2 k.
Proof. intros [|p|p] Hk; [reflexivity|reflexivity|lia]. Qed.

Lemma exp_le_mono : forall a b, a <= b -> exp a <= exp b.
Proof.
  intros a b [H|H]; [apply Rlt_le, exp_increasing, H | rewrite H; apply Rle_refl].
Qed.

(** Integer bounds of [a * log2 5] bound [5 ^ a] by powers of 2, as
    [bpow r e = exp (e * ln r)]. *)
Lemma pow5_bpow2 : forall a lo hi,
  IZR lo <= IZR a * (ln 5 / ln 2) <= IZR hi ->
  bpow radix2 lo <= bpow radix5 a <= bpow radix2 hi.
Proof.
  intros a lo hi [H1 H2]. pose proof ln2_pos as L2.
  rewrite !bpow_exp.
  change (IZR (radix_val radix2)) with 2. change (IZR (radix_val radix5)) with 5.
  assert (E : IZR a * ln 5 = IZR a * (ln 5 / ln 2) * ln 2) by (field; exact ln2_neq).
  split; apply exp_le_mono; rewrite E; apply Rmult_le_compat_r; lra.
Qed.

(** A nonzero [n] of [b] bits has [2 ^ (b - 1) <= n < 2 ^ b]. *)
Lemma nat_bits_pos_bounds : forall n, (0 < n)%Z ->
  (1 <= nat_bits n)%Z /\
  bpow radix2 (nat_bits n - 1) <= IZR n < bpow radix2 (nat_bits n).
Proof.
  intros n Hn.
  assert (E : nat_bits n = (Z.log2 n + 1)%Z)
    by (unfold nat_bits; rewrite (proj2 (Z.eqb_neq n 0)) by lia; reflexivity).
  rewrite E. pose proof (Z.log2_nonneg n) as H0. destruct (Z.log2_spec n Hn) as [H1 H2].
  replace (Z.log2 n + 1 - 1)%Z with (Z.log2 n) by ring.
  rewrite <- !IZR_pow2 by lia.
  split; [lia|]. split; [apply IZR_le; exact H1 | apply IZR_lt; exact H2].
Qed.

Lemma nat_bits_le : forall n k, (0 < n)%Z -> (0 <= k)%Z -> (n < 2 ^ k)%Z ->
  (nat_bits n <= k)%Z.
Proof.
  intros n k Hn Hk H.
  assert (E : nat_bits n = (Z.log2 n + 1)%Z)
    by (unfold nat_bits; rewrite (proj2 (Z.eqb_neq n 0)) by lia; reflexivity).
  assert (Hl : (Z.log2 n < k)%Z) by (apply Z.log2_lt_pow2; assumption).
  lia.
Qed.

Lemma two_61_nonneg : (0 <= 2 ^ 61)%Z.
Proof. lia. Qed.

(** [2 ^ 2 ^ (k + 1) = (2 ^ 2 ^ k) ^ 2], for an abstract [k], so that
    nothing computes [2 ^ 2 ^ 61]. *)
Lemma pow_pow_succ : forall k, (0 <= k)%Z -> (2 ^ 2 ^ (k + 1) = 2 ^ 2 ^ k * 2 ^ 2 ^ k)%Z.
Proof.
  intros k Hk. rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r.
  replace (2 ^ k * 2)%Z with (2 ^ k + 2 ^ k)%Z by ring.
  apply Z.pow_add_r; apply Z.pow_nonneg; lia.
Qed.

Lemma mul_lt_2_2_62 : forall u v, (0 < u < 2 ^ 2 ^ 61)%Z -> (0 < v < 2 ^ 2 ^ 61)%Z ->
  (0 < u * v < 2 ^ 2 ^ 62)%Z.
Proof.
  assert (E := pow_pow_succ 61 ltac:(lia)). change (61 + 1)%Z with 62%Z in E.
  intros u v [Hu0 Hu] [Hv0 Hv]. rewrite E. split.
  - apply Z.mul_pos_pos; assumption.
  - apply Z.mul_lt_mono_nonneg; [apply Z.lt_le_incl; exact Hu0 | exact Hu |
      apply Z.lt_le_incl; exact Hv0 | exact Hv].
Qed.

(** ** The values of [Rat]s *)

Lemma rat_R_eq : forall x, rat_R x =
  if rat_neg x
  then - (IZR (rat_num x) * bpow radix2 (rat_e2 x) * bpow radix5 (rat_e5 x) / IZR (rat_den x))
  else IZR (rat_num x) * bpow radix2 (rat_e2 x) * bpow radix5 (rat_e5 x) / IZR (rat_den x).
Proof. reflexivity. Qed.

Lemma rat_mag_nonneg : forall x, (0 <= rat_num x)%Z -> (0 < rat_den x)%Z ->
  0 <= IZR (rat_num x) * bpow radix2 (rat_e2 x) * bpow radix5 (rat_e5 x) / IZR (rat_den x).
Proof.
  intros x Hn Hd. unfold Rdiv.
  apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
  - apply IZR_le; exact Hn.
  - apply bpow_ge_0.
  - apply bpow_ge_0.
  - apply Rlt_le, Rinv_0_lt_compat, IZR_lt; exact Hd.
Qed.

Lemma rat_mag_pos : forall x, (0 < rat_num x)%Z -> (0 < rat_den x)%Z ->
  0 < IZR (rat_num x) * bpow radix2 (rat_e2 x) * bpow radix5 (rat_e5 x) / IZR (rat_den x).
Proof.
  intros x Hn Hd. unfold Rdiv.
  apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]|].
  - apply IZR_lt; exact Hn.
  - apply bpow_gt_0.
  - apply bpow_gt_0.
  - apply Rinv_0_lt_compat, IZR_lt; exact Hd.
Qed.

Lemma rat_R_abs : forall x, (0 <= rat_num x)%Z -> (0 < rat_den x)%Z ->
  Rabs (rat_R x) =
  IZR (rat_num x) * bpow radix2 (rat_e2 x) * bpow radix5 (rat_e5 x) / IZR (rat_den x).
Proof.
  intros x Hn Hd. pose proof (rat_mag_nonneg x Hn Hd) as P.
  rewrite rat_R_eq. destruct (rat_neg x); cbv beta iota.
  - rewrite Rabs_Ropp. apply Rabs_pos_eq; exact P.
  - apply Rabs_pos_eq; exact P.
Qed.

Lemma rat_R_zero : forall x, rat_num x = 0%Z -> rat_R x = 0.
Proof. intros x H. rewrite rat_R_eq, H. destruct (rat_neg x); cbv beta iota; unfold Rdiv; ring. Qed.

Lemma rat_R_pos : forall x, (0 < rat_num x)%Z -> (0 < rat_den x)%Z ->
  rat_neg x = false -> 0 < rat_R x.
Proof. intros x Hn Hd N. rewrite rat_R_eq, N. apply rat_mag_pos; assumption. Qed.

Lemma rat_R_neg : forall x, (0 < rat_num x)%Z -> (0 < rat_den x)%Z ->
  rat_neg x = true -> rat_R x < 0.
Proof.
  intros x Hn Hd N. pose proof (rat_mag_pos x Hn Hd) as P. rewrite rat_R_eq, N.
  cbv beta iota. lra.
Qed.

(** [|x|] against [|y|] is [X * 5 ^ (x.e5 - y.e5) * 2 ^ (x.e2 - y.e2)]
    against [Y], for [X = x.num * y.den] and [Y = y.num * x.den], as both
    sides are multiplied by [x.den * y.den * 2 ^ -y.e2 * 5 ^ -y.e5 > 0]. *)
Lemma abs_cmp_cross : forall x y,
  (0 <= rat_num x)%Z -> (0 < rat_den x)%Z -> (0 <= rat_num y)%Z -> (0 < rat_den y)%Z ->
  Rcompare (Rabs (rat_R x)) (Rabs (rat_R y)) =
  Rcompare
    (IZR (rat_num x * rat_den y) * bpow radix5 (rat_e5 x - rat_e5 y) *
     bpow radix2 (rat_e2 x - rat_e2 y))
    (IZR (rat_num y * rat_den x)).
Proof.
  intros x y Nx Dx Ny Dy.
  rewrite (rat_R_abs x Nx Dx), (rat_R_abs y Ny Dy).
  assert (Px : 0 < IZR (rat_den x)) by (apply IZR_lt; exact Dx).
  assert (Py : 0 < IZR (rat_den y)) by (apply IZR_lt; exact Dy).
  pose proof (bpow_gt_0 radix2 (rat_e2 y)) as B2.
  pose proof (bpow_gt_0 radix5 (rat_e5 y)) as B5.
  rewrite <- (Rcompare_mult_r
    (IZR (rat_den x) * IZR (rat_den y) / bpow radix2 (rat_e2 y) / bpow radix5 (rat_e5 y))).
  2: { unfold Rdiv. repeat apply Rmult_lt_0_compat; try apply Rinv_0_lt_compat; assumption. }
  f_equal.
  - rewrite mult_IZR. unfold Z.sub. rewrite !bpow_plus, !bpow_opp.
    field. repeat split; apply Rgt_not_eq; assumption.
  - rewrite mult_IZR. field. repeat split; apply Rgt_not_eq; assumption.
Qed.

(** [|x| > |y|] from the numbers of bits: [X >= 2 ^ (bits(x.num) - 1 +
    bits(y.den) - 1)] and [Y < 2 ^ (bits(y.num) + bits(x.den))]. *)
Lemma cmp_bits_gt : forall nx dx ny dy a b lo,
  (0 < nx)%Z -> (0 < dx)%Z -> (0 < ny)%Z -> (0 < dy)%Z ->
  bpow radix2 lo <= bpow radix5 a ->
  (0 <= nat_bits nx - nat_bits dx - nat_bits ny + nat_bits dy + b - 2 + lo)%Z ->
  IZR (ny * dx) < IZR (nx * dy) * bpow radix5 a * bpow radix2 b.
Proof.
  intros nx dx ny dy a b lo Nx Dx Ny Dy H5 Hc.
  destruct (nat_bits_pos_bounds nx Nx) as [_ [Lnx _]].
  destruct (nat_bits_pos_bounds dx Dx) as [_ [_ Udx]].
  destruct (nat_bits_pos_bounds ny Ny) as [_ [_ Uny]].
  destruct (nat_bits_pos_bounds dy Dy) as [_ [Ldy _]].
  rewrite !mult_IZR.
  apply Rlt_le_trans with (bpow radix2 (nat_bits ny) * bpow radix2 (nat_bits dx)).
  { apply Rmult_le_0_lt_compat; [apply IZR_le; lia | apply IZR_le; lia | exact Uny | exact Udx]. }
  rewrite <- bpow_plus.
  apply Rle_trans with (bpow radix2 (nat_bits nx - 1 + (nat_bits dy - 1) + lo + b)).
  { apply bpow_le. lia. }
  rewrite !bpow_plus.
  apply Rmult_le_compat_r; [apply bpow_ge_0|].
  apply Rmult_le_compat; [apply Rmult_le_pos; apply bpow_ge_0 | apply bpow_ge_0 | | exact H5].
  apply Rmult_le_compat; [apply bpow_ge_0 | apply bpow_ge_0 | exact Lnx | exact Ldy].
Qed.

(** [|x| < |y|] from the numbers of bits: [X < 2 ^ (bits(x.num) +
    bits(y.den))] and [Y >= 2 ^ (bits(y.num) - 1 + bits(x.den) - 1)]. *)
Lemma cmp_bits_lt : forall nx dx ny dy a b hi,
  (0 < nx)%Z -> (0 < dx)%Z -> (0 < ny)%Z -> (0 < dy)%Z ->
  bpow radix5 a <= bpow radix2 hi ->
  (nat_bits nx - nat_bits dx - nat_bits ny + nat_bits dy + b + 2 + hi <= 0)%Z ->
  IZR (nx * dy) * bpow radix5 a * bpow radix2 b < IZR (ny * dx).
Proof.
  intros nx dx ny dy a b hi Nx Dx Ny Dy H5 Hc.
  destruct (nat_bits_pos_bounds nx Nx) as [_ [_ Unx]].
  destruct (nat_bits_pos_bounds dx Dx) as [_ [Ldx _]].
  destruct (nat_bits_pos_bounds ny Ny) as [_ [Lny _]].
  destruct (nat_bits_pos_bounds dy Dy) as [_ [_ Udy]].
  rewrite !mult_IZR.
  apply Rlt_le_trans with
    (bpow radix2 (nat_bits nx) * bpow radix2 (nat_bits dy) * bpow radix2 hi * bpow radix2 b).
  { apply Rmult_lt_compat_r; [apply bpow_gt_0|].
    apply Rle_lt_trans with (IZR nx * IZR dy * bpow radix2 hi).
    { apply Rmult_le_compat_l; [apply Rmult_le_pos; apply IZR_le; lia | exact H5]. }
    apply Rmult_lt_compat_r; [apply bpow_gt_0|].
    apply Rmult_le_0_lt_compat; [apply IZR_le; lia | apply IZR_le; lia | exact Unx | exact Udy]. }
  rewrite <- !bpow_plus.
  apply Rle_trans with (bpow radix2 (nat_bits ny - 1 + (nat_bits dx - 1))).
  { apply bpow_le. lia. }
  rewrite bpow_plus.
  apply Rmult_le_compat; [apply bpow_ge_0 | apply bpow_ge_0 | exact Lny | exact Ldx].
Qed.

(** Rewrites the first [checked_i 128] of the goal whose argument is
    closed, and takes the [Some] branch. *)
Local Ltac ci := rewrite checked_i_128 by lia; cbv beta iota zeta.

Lemma cmp_abs_with_correct :
  forall x y loop_only, rat_ok x -> rat_ok y ->
  (rat_num x < 2 ^ 2 ^ 61)%Z -> (rat_den x < 2 ^ 2 ^ 61)%Z ->
  (rat_num y < 2 ^ 2 ^ 61)%Z -> (rat_den y < 2 ^ 2 ^ 61)%Z ->
  (0 < rat_num x)%Z -> (0 < rat_num y)%Z ->
  rat_cmp_abs_with x y loop_only = Some (Rcompare (Rabs (rat_R x)) (Rabs (rat_R y))).
Proof.
  intros x y loop_only Hx Hy Hnx Hdx Hny Hdy Pnx Pny.
  destruct Hx as [[Nx0 _] [[Pdx _] [E2x E5x]]].
  destruct Hy as [[Ny0 _] [[Pdy _] [E2y E5y]]].
  (* Everything that needs the bounds [2 ^ 2 ^ 61] first, then those
     bounds are cleared, as [lia] would compute [2 ^ 2 ^ 61]. *)
  pose proof (nat_bits_le _ _ Pnx two_61_nonneg Hnx) as Unx.
  pose proof (nat_bits_le _ _ Pdx two_61_nonneg Hdx) as Udx.
  pose proof (nat_bits_le _ _ Pny two_61_nonneg Hny) as Uny.
  pose proof (nat_bits_le _ _ Pdy two_61_nonneg Hdy) as Udy.
  assert (C1 : forall a b, (0 <= a < 2 ^ 32)%Z -> (Z.abs b < 2 ^ 32)%Z ->
    rat_cmp_pow5 (rat_num x * rat_den y) a b (rat_num y * rat_den x) loop_only =
    Some (Rcompare (IZR (rat_num x * rat_den y) * bpow radix5 a * bpow radix2 b)
      (IZR (rat_num y * rat_den x)))).
  { intros a b Ha Hb.
    apply cmp_pow5_correct; [| |exact Ha|exact Hb]; apply mul_lt_2_2_62; split; assumption. }
  assert (C2 : forall a b, (0 <= a < 2 ^ 32)%Z -> (Z.abs b < 2 ^ 32)%Z ->
    rat_cmp_pow5 (rat_num y * rat_den x) a b (rat_num x * rat_den y) loop_only =
    Some (Rcompare (IZR (rat_num y * rat_den x) * bpow radix5 a * bpow radix2 b)
      (IZR (rat_num x * rat_den y)))).
  { intros a b Ha Hb.
    apply cmp_pow5_correct; [| |exact Ha|exact Hb]; apply mul_lt_2_2_62; split; assumption. }
  clear Hnx Hdx Hny Hdy.
  pose proof (abs_cmp_cross x y Nx0 Pdx Ny0 Pdy) as Kxy.
  pose proof (abs_cmp_cross y x Ny0 Pdy Nx0 Pdx) as Kyx.
  destruct (nat_bits_pos_bounds _ Pnx) as [Lnx _].
  destruct (nat_bits_pos_bounds _ Pdx) as [Ldx _].
  destruct (nat_bits_pos_bounds _ Pny) as [Lny _].
  destruct (nat_bits_pos_bounds _ Pdy) as [Ldy _].
  assert (Ha : (0 <= Z.abs (rat_e5 x - rat_e5 y) < 2 ^ 32)%Z) by lia.
  destruct (log2_5_bounds_correct _ Ha) as (lo & hi & Elh & Rlh & Dlh & Plo & Phi).
  assert (Llh : (lo <= hi)%Z) by (apply le_IZR; lra).
  unfold rat_cmp_abs_with.
  rewrite !bits_z_correct by lia.
  repeat ci.
  rewrite Elh. cbv beta iota zeta.
  destruct (Z.leb_spec (rat_e5 y) (rat_e5 x)) as [H5|H5]; cbv beta iota zeta.
  - (* [x.e5 >= y.e5]: [lo5 = lo] and [hi5 = hi]. *)
    rewrite (Z.abs_eq (rat_e5 x - rat_e5 y)) in Rlh |- * by lia.
    destruct (pow5_bpow2 _ _ _ Rlh) as [P5l P5h].
    repeat ci.
    match goal with |- context [ (0 <=? ?g)%Z ] => destruct (Z.leb_spec 0 g) as [G|G] end;
      cbv beta iota zeta.
    { rewrite Kxy. f_equal. symmetry. apply Rcompare_Gt.
      apply cmp_bits_gt with (lo := lo); try assumption. lia. }
    repeat ci.
    match goal with |- context [ (?l <=? 0)%Z ] => destruct (Z.leb_spec l 0) as [G'|G'] end;
      cbv beta iota zeta.
    { rewrite Kxy. f_equal. symmetry. apply Rcompare_Lt.
      apply cmp_bits_lt with (hi := hi); try assumption. lia. }
    rewrite !mul_z_correct by lia. cbv beta iota zeta.
    repeat ci. rewrite C1 by lia. rewrite Kxy. reflexivity.
  - (* [x.e5 < y.e5]: [lo5 = -hi] and [hi5 = -lo]. *)
    rewrite (Z.abs_neq (rat_e5 x - rat_e5 y)) in Rlh |- * by lia.
    assert (Rlh' : IZR (- hi) <= IZR (rat_e5 x - rat_e5 y) * (ln 5 / ln 2) <= IZR (- lo)).
    { rewrite opp_IZR in Rlh. rewrite !opp_IZR. lra. }
    destruct (pow5_bpow2 _ _ _ Rlh') as [P5l P5h].
    repeat ci.
    repeat ci.
    match goal with |- context [ (0 <=? ?g)%Z ] => destruct (Z.leb_spec 0 g) as [G|G] end;
      cbv beta iota zeta.
    { rewrite Kxy. f_equal. symmetry. apply Rcompare_Gt.
      apply cmp_bits_gt with (lo := (- hi)%Z); try assumption. lia. }
    repeat ci.
    match goal with |- context [ (?l <=? 0)%Z ] => destruct (Z.leb_spec l 0) as [G'|G'] end;
      cbv beta iota zeta.
    { rewrite Kxy. f_equal. symmetry. apply Rcompare_Lt.
      apply cmp_bits_lt with (hi := (- lo)%Z); try assumption. lia. }
    rewrite !mul_z_correct by lia. cbv beta iota zeta.
    repeat ci. rewrite C2 by lia. cbv beta iota zeta.
    rewrite (Rcompare_sym (Rabs (rat_R x))), Kyx.
    replace (- (rat_e5 x - rat_e5 y))%Z with (rat_e5 y - rat_e5 x)%Z by ring.
    replace (- (rat_e2 x - rat_e2 y))%Z with (rat_e2 y - rat_e2 x)%Z by ring.
    reflexivity.
Qed.

(** Reduces the comparisons of the signs [-1], [0] and [1] in [rat_cmp]. *)
Local Ltac red_sign :=
  cbv beta iota zeta delta [negb orb Z.eqb Z.ltb Z.compare Pos.eqb Pos.compare Pos.compare_cont
    CompOpp].

(** [x.cmp(&y)] of [impl Ord for Rat] *)
Theorem rat_cmp_correct :
  forall x y, rat_ok x -> rat_ok y ->
  (rat_num x < 2 ^ 2 ^ 61)%Z -> (rat_den x < 2 ^ 2 ^ 61)%Z ->
  (rat_num y < 2 ^ 2 ^ 61)%Z -> (rat_den y < 2 ^ 2 ^ 61)%Z ->
  rat_cmp x y = Some (Rcompare (rat_R x) (rat_R y)).
Proof.
  intros x y Hx Hy Hnx Hdx Hny Hdy.
  assert (Cxy : (0 < rat_num x)%Z -> (0 < rat_num y)%Z ->
    rat_cmp_abs x y = Some (Rcompare (Rabs (rat_R x)) (Rabs (rat_R y)))).
  { intros Px Py. apply cmp_abs_with_correct; assumption. }
  assert (Cyx : (0 < rat_num x)%Z -> (0 < rat_num y)%Z ->
    rat_cmp_abs y x = Some (Rcompare (Rabs (rat_R y)) (Rabs (rat_R x)))).
  { intros Px Py. apply cmp_abs_with_correct; assumption. }
  clear Hnx Hdx Hny Hdy.
  destruct Hx as [[Nx0 _] [[Dx0 _] _]]. destruct Hy as [[Ny0 _] [[Dy0 _] _]].
  unfold rat_cmp, rat_sign.
  rewrite (is_zero_z_correct _ Nx0), (is_zero_z_correct _ Ny0).
  destruct (Z.eqb_spec (rat_num x) 0) as [Zx|Zx];
    destruct (Z.eqb_spec (rat_num y) 0) as [Zy|Zy].
  - red_sign. f_equal. symmetry. apply Rcompare_Eq.
    rewrite (rat_R_zero x Zx), (rat_R_zero y Zy). reflexivity.
  - pose proof (rat_R_zero x Zx) as Rx.
    destruct (rat_neg y) eqn:Ngy; red_sign; f_equal; symmetry.
    + apply Rcompare_Gt. pose proof (rat_R_neg y ltac:(lia) Dy0 Ngy). lra.
    + apply Rcompare_Lt. pose proof (rat_R_pos y ltac:(lia) Dy0 Ngy). lra.
  - pose proof (rat_R_zero y Zy) as Ry.
    destruct (rat_neg x) eqn:Ngx; red_sign; f_equal; symmetry.
    + apply Rcompare_Lt. pose proof (rat_R_neg x ltac:(lia) Dx0 Ngx). lra.
    + apply Rcompare_Gt. pose proof (rat_R_pos x ltac:(lia) Dx0 Ngx). lra.
  - assert (Px : (0 < rat_num x)%Z) by lia. assert (Py : (0 < rat_num y)%Z) by lia.
    destruct (rat_neg x) eqn:Ngx; destruct (rat_neg y) eqn:Ngy; red_sign.
    + (* both negative: [cmp_abs(other, self)] *)
      rewrite (Cyx Px Py). f_equal.
      rewrite (Rabs_left (rat_R x)) by (apply rat_R_neg; assumption).
      rewrite (Rabs_left (rat_R y)) by (apply rat_R_neg; assumption).
      apply Rcompare_opp.
    + f_equal. symmetry. apply Rcompare_Lt.
      pose proof (rat_R_neg x Px Dx0 Ngx). pose proof (rat_R_pos y Py Dy0 Ngy). lra.
    + f_equal. symmetry. apply Rcompare_Gt.
      pose proof (rat_R_pos x Px Dx0 Ngx). pose proof (rat_R_neg y Py Dy0 Ngy). lra.
    + (* both positive: [cmp_abs(self, other)] *)
      rewrite (Cxy Px Py). f_equal.
      rewrite (Rabs_pos_eq (rat_R x)) by (apply Rlt_le, rat_R_pos; assumption).
      rewrite (Rabs_pos_eq (rat_R y)) by (apply Rlt_le, rat_R_pos; assumption).
      reflexivity.
Qed.
