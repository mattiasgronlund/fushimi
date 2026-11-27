(** * [cmp_shifted], [pow5_bound] and [cmp_pow5] of [src/parse/rat.rs]

    [cmp_pow5_correct] shows that [cmp_pow5] compares [x * 5 ^ a * 2 ^ b]
    with [y]. Up to its limit it computes [5 ^ a] exactly; above it, each
    pass of its [loop] bounds [5 ^ a] from below and from above by
    [pow5_bound] ([pow5_bound_correct]) and returns only an answer that
    these bounds decide, and the loop returns at the latest once [p]
    reaches the number of bits of [5 ^ a], where the lower bound is exact:
    within the 64 passes of fuel of [rat_cmp_pow5_loop], for both values
    of [loop_only]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core.
From Fushimi Require Import Model NatOps.

Open Scope R_scope.

(** ** Integer facts *)

(** [checked_i 128] keeps a [z] that fits an [i128]. *)
Local Lemma checked_i_128_some :
  forall z, (- 2 ^ 127 <= z < 2 ^ 127)%Z -> checked_i 128 z = Some z.
Proof.
intros z Hz. unfold checked_i.
replace ((- 2 ^ (128 - 1) <=? z) && (z <? 2 ^ (128 - 1)))%Z with true; [reflexivity|].
symmetry. apply Bool.andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(** A positive [n] lies in [[2 ^ (nat_bits n - 1), 2 ^ nat_bits n)]. *)
Local Lemma nat_bits_pos_spec : forall n, (0 < n)%Z ->
  (1 <= nat_bits n)%Z /\ (2 ^ (nat_bits n - 1) <= n < 2 ^ nat_bits n)%Z.
Proof.
intros n Hn. unfold nat_bits.
destruct (Z.eqb_spec n 0) as [->|_]; [lia|].
pose proof (Z.log2_spec n Hn) as [H1 H2]. pose proof (Z.log2_nonneg n).
unfold Z.succ in H2. replace (Z.log2 n + 1 - 1)%Z with (Z.log2 n) by lia.
split; [lia | split; assumption].
Qed.

(** A positive [n < 2 ^ k] has at most [k] bits. *)
Local Lemma nat_bits_lt_pow : forall n k, (0 < n)%Z -> (n < 2 ^ k)%Z -> (nat_bits n <= k)%Z.
Proof.
intros n k Hn Hk. unfold nat_bits.
destruct (Z.eqb_spec n 0) as [->|_]; [lia|].
apply (Z.log2_lt_pow2 n k Hn) in Hk. lia.
Qed.

Local Lemma nat_bits_mono : forall u v, (0 < u <= v)%Z -> (nat_bits u <= nat_bits v)%Z.
Proof.
intros u v H. unfold nat_bits.
destruct (Z.eqb_spec u 0), (Z.eqb_spec v 0); try lia.
pose proof (Z.log2_le_mono u v ltac:(lia)). lia.
Qed.

(** The bits of a product are at most the bits of its factors. *)
Local Lemma nat_bits_mul : forall u v, (0 < u)%Z -> (0 < v)%Z ->
  (nat_bits (u * v) <= nat_bits u + nat_bits v)%Z.
Proof.
intros u v Hu Hv.
destruct (nat_bits_pos_spec u Hu) as (U1 & _ & U), (nat_bits_pos_spec v Hv) as (V1 & _ & V).
apply nat_bits_lt_pow; [lia|].
rewrite Z.pow_add_r by lia. apply Z.mul_lt_mono_nonneg; lia.
Qed.

(** [5 ^ a <= 8 ^ a = 2 ^ (3 * a)]. *)
Local Lemma nat_bits_pow5 : forall a, (0 <= a)%Z -> (nat_bits (5 ^ a) <= 3 * a + 1)%Z.
Proof.
intros a Ha. apply nat_bits_lt_pow; [apply Z.pow_pos_nonneg; lia|].
rewrite Z.pow_add_r, Z.pow_mul_r, Z.pow_1_r by lia. change (2 ^ 3)%Z with 8%Z.
assert (H58 : (5 ^ a <= 8 ^ a)%Z) by (apply Z.pow_le_mono_l; lia).
assert (H8 : (0 < 8 ^ a)%Z) by (apply Z.pow_pos_nonneg; lia).
lia.
Qed.

(** ** Reals *)

Local Lemma IZR_pow2 : forall n, (0 <= n)%Z -> IZR (2 ^ n) = bpow radix2 n.
Proof. intros n Hn. rewrite <- IZR_Zpower by exact Hn. reflexivity. Qed.

Local Lemma IZR_pow5 : forall n, (0 <= n)%Z -> IZR (5 ^ n) = bpow radix5 n.
Proof. intros n Hn. rewrite <- IZR_Zpower by exact Hn. reflexivity. Qed.

Local Lemma scale_pow2 : forall x m b k, (0 <= k)%Z ->
  IZR (x * m) * bpow radix2 (b + k) = IZR x * bpow radix2 b * IZR (m * 2 ^ k).
Proof. intros x m b k Hk. rewrite bpow_plus, !mult_IZR, IZR_pow2 by exact Hk. ring. Qed.

(** If [c * u] is above [w], so is [c * v] for [v >= u]; and the same
    below. *)
Local Lemma cmp_gt_mono : forall c u v w, 0 < c -> (u <= v)%Z ->
  Rcompare (c * IZR u) w = Gt -> Rcompare (c * IZR v) w = Gt.
Proof.
intros c u v w Hc Huv H. apply Rcompare_Gt_inv in H. apply Rcompare_Gt.
apply IZR_le in Huv. apply Rlt_le_trans with (1 := H). apply Rmult_le_compat_l; lra.
Qed.

Local Lemma cmp_lt_mono : forall c u v w, 0 < c -> (v <= u)%Z ->
  Rcompare (c * IZR u) w = Lt -> Rcompare (c * IZR v) w = Lt.
Proof.
intros c u v w Hc Hvu H. apply Rcompare_Lt_inv in H. apply Rcompare_Lt.
apply IZR_le in Hvu. apply Rle_lt_trans with (2 := H). apply Rmult_le_compat_l; lra.
Qed.

(** ** [cmp_shifted] *)

Lemma cmp_shifted_correct :
  forall x e y, (0 < x)%Z -> (0 < y)%Z -> (nat_bits x < 2 ^ 64)%Z -> (nat_bits y < 2 ^ 64)%Z ->
  (Z.abs e < 2 ^ 126)%Z ->
  rat_cmp_shifted x e y = Some (Rcompare (IZR x * bpow radix2 e) (IZR y)).
Proof.
intros x e y Hx Hy Bx By He. unfold rat_cmp_shifted.
rewrite !bits_z_correct by lia.
destruct (nat_bits_pos_spec x Hx) as (Bx1 & Lx & Ux).
destruct (nat_bits_pos_spec y Hy) as (By1 & Ly & Uy).
rewrite (checked_i_128_some (nat_bits x + e)) by lia. cbv beta iota.
assert (Rx : bpow radix2 (nat_bits x - 1) <= IZR x < bpow radix2 (nat_bits x)).
{ rewrite <- !IZR_pow2 by lia. split; [apply IZR_le | apply IZR_lt]; lia. }
assert (Ry : bpow radix2 (nat_bits y - 1) <= IZR y < bpow radix2 (nat_bits y)).
{ rewrite <- !IZR_pow2 by lia. split; [apply IZR_le | apply IZR_lt]; lia. }
pose proof (bpow_gt_0 radix2 e) as Pe.
destruct (Z.compare_spec (nat_bits x + e) (nat_bits y)) as [Heq|Hlt|Hgt]; cbv beta iota.
- (* The same number of bits: [e = bits y - bits x], so [|e| < 2 ^ 64]. *)
  destruct (Z.leb_spec 0 e) as [He0|He0].
  + rewrite Z.mod_small by lia. rewrite shl_z_correct by lia. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite cmp_z_correct by (try apply Z.mul_nonneg_nonneg; try apply Z.pow_nonneg; lia).
    f_equal. rewrite <- Rcompare_IZR, mult_IZR, IZR_pow2 by lia. reflexivity.
  + rewrite (checked_i_128_some (- e)) by lia. cbv beta iota.
    rewrite Z.mod_small by lia. rewrite shl_z_correct by lia. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite cmp_z_correct by (try apply Z.mul_nonneg_nonneg; try apply Z.pow_nonneg; lia).
    f_equal. rewrite <- Rcompare_IZR, mult_IZR, IZR_pow2 by lia.
    rewrite <- (Rcompare_mult_r (bpow radix2 e)) by exact Pe.
    rewrite Rmult_assoc, <- bpow_plus. replace (- e + e)%Z with 0%Z by lia.
    change (bpow radix2 0) with 1. rewrite Rmult_1_r. reflexivity.
- (* [x * 2 ^ e < 2 ^ (bits x + e) <= 2 ^ (bits y - 1) <= y]. *)
  f_equal. symmetry. apply Rcompare_Lt.
  apply Rlt_le_trans with (bpow radix2 (nat_bits x) * bpow radix2 e).
  { apply Rmult_lt_compat_r; [exact Pe | lra]. }
  rewrite <- bpow_plus. apply Rle_trans with (bpow radix2 (nat_bits y - 1)); [apply bpow_le; lia | lra].
- (* [y < 2 ^ bits y <= 2 ^ (bits x - 1 + e) <= x * 2 ^ e]. *)
  f_equal. symmetry. apply Rcompare_Gt.
  apply Rlt_le_trans with (bpow radix2 (nat_bits y)); [lra|].
  apply Rle_trans with (bpow radix2 (nat_bits x - 1) * bpow radix2 e).
  { rewrite <- bpow_plus. apply bpow_le. lia. }
  apply Rmult_le_compat_r; lra.
Qed.

(** ** [pow5_bound] *)

(** The state [(m, k, exact)] of [pow5_bound a p up] once it has read the
    bits of [a] whose value is [A]: [m * 2 ^ k] is below [5 ^ A], or above
    it if [up], and equal to it exactly when [exact]; [m] has at most
    [p + 1] bits, [k] grows at most like [A], and [exact] stays true if
    [5 ^ a] has at most [p] bits. *)
Local Definition bound_inv (a p : Z) (up : bool) (A : Z) (st : Z * Z * bool) : Prop :=
  let '(m, k, exact) := st in
  (0 < m)%Z /\ (nat_bits m <= p + 1)%Z /\ (0 <= k)%Z /\ (k = 0 \/ k + 2 ^ 35 <= 2 ^ 36 * A)%Z /\
  (if exact then m * 2 ^ k = 5 ^ A else if up then 5 ^ A < m * 2 ^ k else m * 2 ^ k < 5 ^ A)%Z /\
  (nat_bits (5 ^ a) <= p -> exact = true)%Z.

(** One pass of the [for] loop reads the bit [i] of [a]: the prefix
    [a / 2 ^ (i + 1)] of [a] becomes [a / 2 ^ i]. Squares and products of
    lower (upper) bounds of positive numbers are lower (upper) bounds of
    theirs, and the cut [m = q * 2 ^ s + r] keeps the bound, exactly when
    [r = 0]. *)
Local Lemma pow5_bound_step_inv :
  forall a p up i st, (0 <= a < 2 ^ 32)%Z -> (1 <= p <= 2 ^ 34)%Z -> (0 <= i < 32)%Z ->
  (1 <= a / 2 ^ i)%Z -> bound_inv a p up (a / 2 ^ (i + 1)) st ->
  exists st', rat_pow5_bound_step a p up i st = Some st' /\ bound_inv a p up (a / 2 ^ i) st'.
Proof.
intros a p up i [[m k] ex] Ha Hp Hi HA' Inv.
cbn [bound_inv] in Inv. destruct Inv as (Hm & Bm & Hk0 & Hk & R & X).
assert (Hpi : (0 < 2 ^ i)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (HA : (a / 2 ^ (i + 1) = a / 2 ^ i / 2)%Z)
  by (rewrite Z.pow_add_r, Z.pow_1_r, Z.div_div by lia; reflexivity).
rewrite HA in Hk, R.
assert (HA'a : (a / 2 ^ i <= a)%Z) by (apply Z.div_le_upper_bound; nia).
assert (Esh : shr 32 a i = Some (a / 2 ^ i)%Z).
{ unfold shr. replace ((0 <=? i) && (i <? 32))%Z with true.
  - rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  - symmetry. apply Bool.andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
set (A' := (a / 2 ^ i)%Z) in *.
assert (Hland : Z.land A' 1 = (A' mod 2)%Z).
{ change (Z.land A' 1) with (Z.land A' (Z.ones 1)). rewrite Z.land_ones by lia. reflexivity. }
assert (HAA : (A' = 2 * (A' / 2) + A' mod 2)%Z) by (apply Z.div_mod; lia).
assert (Hbit : (0 <= A' mod 2 < 2)%Z) by (apply Z.mod_pos_bound; lia).
assert (HA0 : (0 <= A' / 2)%Z) by (apply Z.div_pos; lia).
set (A := (A' / 2)%Z) in *. set (bit := (A' mod 2)%Z) in *.
clearbody A bit. clearbody A'.
unfold rat_pow5_bound_step. cbv beta iota zeta.
rewrite (mul_z_correct m m) by lia. cbv beta iota.
rewrite (checked_i_128_some (k * 2)) by lia. cbv beta iota.
rewrite Esh. cbv beta iota. rewrite Hland.
rewrite !from_u64_z_correct by lia.
(* [m' = m * m * 5 ^ bit], and [5 ^ A' = 5 ^ A * 5 ^ A * 5 ^ bit]. *)
assert (EM : exists m' : Z, (if bit =? 1 then NatLimbs.mul_z (m * m) 5 else Some (m * m))%Z = Some m' /\
  m' = (m * m * 5 ^ bit)%Z).
{ destruct (Z.eqb_spec bit 1) as [B|B].
  - exists (m * m * 5)%Z. rewrite mul_z_correct by nia. rewrite B. split; reflexivity.
  - exists (m * m)%Z. split; [reflexivity|]. replace bit with 0%Z by lia. rewrite Z.pow_0_r. ring. }
destruct EM as (m' & EM & Hm'). rewrite EM. cbv beta iota.
assert (Hf : (1 <= 5 ^ bit <= 5)%Z)
  by (destruct (Z.eq_dec bit 0) as [->|B]; [cbn; lia | replace bit with 1%Z by lia; cbn; lia]).
assert (Hm'0 : (0 < m')%Z) by (rewrite Hm'; apply Z.mul_pos_pos; [apply Z.mul_pos_pos|]; lia).
assert (Bm' : (nat_bits m' <= 2 * p + 5)%Z).
{ rewrite Hm'. pose proof (nat_bits_mul (m * m) (5 ^ bit) ltac:(nia) ltac:(lia)).
  pose proof (nat_bits_mul m m Hm Hm).
  assert (nat_bits (5 ^ bit) <= 3)%Z by (apply nat_bits_lt_pow; lia).
  lia. }
assert (EP : (5 ^ A' = 5 ^ A * 5 ^ A * 5 ^ bit)%Z).
{ rewrite HAA. replace (2 * A + bit)%Z with (A + A + bit)%Z by ring.
  rewrite !Z.pow_add_r by lia. ring. }
assert (EV : (m' * 2 ^ (k * 2) = (m * 2 ^ k) * (m * 2 ^ k) * 5 ^ bit)%Z).
{ rewrite Hm'. replace (k * 2)%Z with (k + k)%Z by ring. rewrite Z.pow_add_r by lia. ring. }
assert (R' : if ex then (m' * 2 ^ (k * 2) = 5 ^ A')%Z
  else if up then (5 ^ A' < m' * 2 ^ (k * 2))%Z else (m' * 2 ^ (k * 2) < 5 ^ A')%Z).
{ rewrite EV, EP.
  assert (P0 : (0 < 5 ^ A)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (V0 : (0 < m * 2 ^ k)%Z) by (apply Z.mul_pos_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  revert R P0 V0 Hf. generalize (m * 2 ^ k)%Z (5 ^ A)%Z (5 ^ bit)%Z. intros V P f R P0 V0 Hf.
  destruct ex; cbv beta iota in R |- *; [rewrite R; reflexivity|].
  destruct up; cbv beta iota in R |- *.
  - assert (P * P < V * V)%Z by nia. nia.
  - assert (V * V < P * P)%Z by nia. nia. }
assert (HE : (1 <= 2 ^ (k * 2))%Z) by (assert (0 < 2 ^ (k * 2))%Z by (apply Z.pow_pos_nonneg; lia); lia).
rewrite (bits_z_correct m') by lia.
assert (Hsdef : exists s, s = Z.max 0 (nat_bits m' - p)) by (eexists; reflexivity).
destruct Hsdef as (s & Hsdef). rewrite <- Hsdef.
destruct (Z.ltb_spec 0 s) as [Hs|Hs].
- (* A cut: [m' = q * 2 ^ s + r] with [s = bits m' - p]. *)
  (* If [5 ^ a] has at most [p] bits, [exact] is still true, so [m' <= 5 ^ A' <= 5 ^ a]
     has at most [p] bits, and there is no cut. *)
  assert (X' : (nat_bits (5 ^ a) <= p)%Z -> False).
  { intros H5. specialize (X H5). subst ex. cbv beta iota in R'.
    assert (Hm5 : (m' <= 5 ^ A')%Z) by (rewrite <- R'; nia).
    assert (H55 : (5 ^ A' <= 5 ^ a)%Z) by (apply Z.pow_le_mono_r; lia).
    assert (nat_bits m' <= nat_bits (5 ^ a))%Z by (apply nat_bits_mono; lia).
    lia. }
  assert (Hps : (0 < 2 ^ s)%Z) by (apply Z.pow_pos_nonneg; lia).
  rewrite (shl_z_correct 1 s) by lia. rewrite Z.shiftl_1_l.
  rewrite (div_rem_z_correct m' (2 ^ s)) by lia. cbv beta iota.
  pose proof (Z.mod_pos_bound m' (2 ^ s) Hps) as Hr.
  rewrite (is_zero_z_correct (m' mod 2 ^ s)) by lia.
  destruct (nat_bits_pos_spec m' Hm'0) as (_ & Lm' & Um').
  assert (Hq : (m' / 2 ^ s < 2 ^ p)%Z).
  { apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia.
    replace (s + p)%Z with (nat_bits m') by lia. exact Um'. }
  assert (Hq1 : (1 <= m' / 2 ^ s)%Z).
  { apply Z.div_le_lower_bound; [lia|]. rewrite Z.mul_1_r.
    eapply Z.le_trans; [|exact Lm']. apply Z.pow_le_mono_r; lia. }
  assert (Hdiv : (m' = 2 ^ s * (m' / 2 ^ s) + m' mod 2 ^ s)%Z) by (apply Z.div_mod; lia).
  rewrite (add_z_correct (m' / 2 ^ s) 1) by lia.
  rewrite (checked_i_128_some (k * 2 + s)) by lia. cbv beta iota.
  eexists. split; [reflexivity|]. cbn [bound_inv].
  rewrite Z.pow_add_r by lia.
  assert (Hp1 : (2 ^ (p + 1) = 2 * 2 ^ p)%Z) by (rewrite Z.pow_add_r, Z.pow_1_r by lia; ring).
  revert Hq Hq1 Hdiv Hr. generalize (m' / 2 ^ s)%Z (m' mod 2 ^ s)%Z. intros q r Hq Hq1 Hdiv Hr.
  assert (HqS : (q * (2 ^ (k * 2) * 2 ^ s) = m' * 2 ^ (k * 2) - r * 2 ^ (k * 2))%Z)
    by (rewrite Hdiv; ring).
  assert (HrE : (0 <= r * 2 ^ (k * 2) < 2 ^ s * 2 ^ (k * 2))%Z) by nia.
  assert (HSE : (2 ^ (k * 2) * 2 ^ s = 2 ^ s * 2 ^ (k * 2))%Z) by ring.
  split; [destruct (up && negb (r =? 0)); lia|].
  split.
  { apply nat_bits_lt_pow; [destruct (up && negb (r =? 0)); lia|].
    rewrite Hp1. destruct (up && negb (r =? 0)); lia. }
  split; [lia|]. split; [lia|]. split; [|intros H5; exfalso; exact (X' H5)].
  destruct (Z.eqb_spec r 0) as [Hr0|Hr0].
  + subst r. destruct ex, up; cbn [andb negb]; cbv beta iota in R' |- *; lia.
  + assert (HrE0 : (0 < r * 2 ^ (k * 2))%Z) by nia.
    destruct ex, up; cbn [andb negb]; cbv beta iota in R' |- *; lia.
- (* No cut: [m'] has at most [p] bits. *)
  eexists. split; [reflexivity|]. cbn [bound_inv].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact R' | exact X].
Qed.

(** The [for] loop, for [i] from [j - 1] down to 0, reads the bits of [a]
    below its prefix [a / 2 ^ j]. *)
Local Lemma pow5_bound_loop_inv :
  forall a p up j st, (0 <= a < 2 ^ 32)%Z -> (1 <= p <= 2 ^ 34)%Z ->
  (Z.of_nat j <= nat_bits a)%Z -> bound_inv a p up (a / 2 ^ Z.of_nat j) st ->
  exists st', rat_pow5_bound_loop j a p up st = Some st' /\ bound_inv a p up a st'.
Proof.
intros a p up j. induction j as [|j IH]; intros st Ha Hp Hj Inv.
- exists st. split; [reflexivity|]. change (2 ^ Z.of_nat 0)%Z with 1%Z in Inv.
  rewrite Z.div_1_r in Inv. exact Inv.
- cbn [rat_pow5_bound_loop].
  rewrite Nat2Z.inj_succ, <- Z.add_1_r in Hj, Inv.
  assert (Ha0 : (0 < a)%Z).
  { destruct (Z.eq_dec a 0) as [->|Ha0]; [|lia]. change (nat_bits 0) with 0%Z in Hj. lia. }
  destruct (nat_bits_pos_spec a Ha0) as (B1 & BL & BU).
  assert (H32 : (nat_bits a <= 32)%Z) by (apply nat_bits_lt_pow; lia).
  (* Below the top bit of [a], the prefix [a / 2 ^ j] is at least 1. *)
  assert (Hj1 : (1 <= a / 2 ^ Z.of_nat j)%Z).
  { apply Z.div_le_lower_bound; [apply Z.pow_pos_nonneg; lia|]. rewrite Z.mul_1_r.
    eapply Z.le_trans; [|exact BL]. apply Z.pow_le_mono_r; lia. }
  destruct (pow5_bound_step_inv a p up (Z.of_nat j) st Ha Hp ltac:(lia) Hj1 Inv) as (st' & E & Inv').
  rewrite E. cbv beta iota. apply IH; [exact Ha | exact Hp | lia | exact Inv'].
Qed.

(** [pow5_bound a p up] returns [(m, k, exact)] with [m * 2 ^ k <= 5 ^ a],
    or [>=] if [up], equal exactly when [exact], which it is if [5 ^ a] has
    at most [p] bits; [m] has at most [p + 1] bits and [0 <= k < 2 ^ 68]. *)
Lemma pow5_bound_correct :
  forall a p up, (0 <= a < 2 ^ 32)%Z -> (1 <= p <= 2 ^ 34)%Z ->
  exists m k exact, rat_pow5_bound a p up = Some (m, k, exact) /\
  (0 < m)%Z /\ (nat_bits m <= p + 1)%Z /\ (0 <= k < 2 ^ 68)%Z /\
  (if up then 5 ^ a <= m * 2 ^ k else m * 2 ^ k <= 5 ^ a)%Z /\
  (exact = true <-> m * 2 ^ k = 5 ^ a)%Z /\
  (nat_bits (5 ^ a) <= p -> exact = true)%Z.
Proof.
intros a p up Ha Hp. unfold rat_pow5_bound.
assert (Hnb : (32 - leading_zeros 32 a = nat_bits a)%Z)
  by (unfold leading_zeros, nat_bits; destruct (Z.eqb_spec a 0); lia).
rewrite Hnb, (from_u64_z_correct 1) by lia.
assert (Hnb0 : (0 <= nat_bits a)%Z)
  by (unfold nat_bits; destruct (Z.eqb_spec a 0); [lia | pose proof (Z.log2_nonneg a); lia]).
assert (Hj0 : (Z.of_nat (Z.to_nat (nat_bits a)) <= nat_bits a)%Z) by (rewrite Z2Nat.id by lia; lia).
assert (Inv0 : bound_inv a p up (a / 2 ^ Z.of_nat (Z.to_nat (nat_bits a))) (1, 0, true)%Z).
{ rewrite Z2Nat.id by lia.
  assert (H0 : (a / 2 ^ nat_bits a = 0)%Z).
  { apply Z.div_small. destruct (Z.eq_dec a 0) as [->|Ha0]; [cbn; lia|].
    destruct (nat_bits_pos_spec a ltac:(lia)); lia. }
  rewrite H0. cbn [bound_inv].
  split; [lia|]. split; [unfold nat_bits; cbn; lia|]. split; [lia|]. split; [now left|].
  split; [reflexivity | intros _; reflexivity]. }
destruct (pow5_bound_loop_inv a p up _ _ Ha Hp Hj0 Inv0) as ([[m k] ex] & E & Inv).
exists m, k, ex. split; [exact E|].
cbn [bound_inv] in Inv. destruct Inv as (Hm & Bm & Hk0 & Hk & R & X).
split; [exact Hm|]. split; [exact Bm|]. split; [lia|].
split; [destruct ex, up; cbv beta iota in R |- *; lia|].
split; [|exact X].
destruct ex; cbv beta iota in R.
- split; [intros _; exact R | reflexivity].
- split; [intros H; discriminate H|]. intros Heq. destruct up; cbv beta iota in R; lia.
Qed.

(** ** [cmp_pow5] *)

(** The [loop] of [cmp_pow5], from [p = 2 ^ (7 + j)]: each answer it
    returns is right, and it returns at the latest at [j = 27], where
    [p = 2 ^ 34] is at least the [3 * a + 1] bits of [5 ^ a]. *)
Local Lemma cmp_pow5_loop_correct :
  forall x a b y n j, (0 < x)%Z -> (nat_bits x <= 2 ^ 62)%Z -> (0 < y)%Z ->
  (nat_bits y <= 2 ^ 62)%Z -> (0 <= a < 2 ^ 32)%Z -> (Z.abs b < 2 ^ 32)%Z ->
  (0 <= j <= 27)%Z -> (27 - j < Z.of_nat n)%Z ->
  rat_cmp_pow5_loop n x a b y (2 ^ (7 + j)) =
  Some (Rcompare (IZR x * bpow radix2 b * IZR (5 ^ a)) (IZR y)).
Proof.
intros x a b y n. induction n as [|n IH]; intros j Hx Bx Hy By Ha Hb Hj Hn; [lia|].
assert (Hp : (1 <= 2 ^ (7 + j) <= 2 ^ 34)%Z).
{ split; [assert (0 < 2 ^ (7 + j))%Z by (apply Z.pow_pos_nonneg; lia); lia|].
  apply Z.pow_le_mono_r; lia. }
assert (Hc : 0 < IZR x * bpow radix2 b)
  by (apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0]).
cbn [rat_cmp_pow5_loop].
destruct (pow5_bound_correct a (2 ^ (7 + j)) false Ha Hp)
  as (lo & k & ex & E & Hlo & Blo & Hk & Rlo & Elo & Xlo).
rewrite E. cbv beta iota.
rewrite (mul_z_correct x lo) by lia. cbv beta iota.
rewrite (checked_i_128_some (b + k)) by lia. cbv beta iota.
assert (Bxl : (nat_bits (x * lo) < 2 ^ 64)%Z) by (pose proof (nat_bits_mul x lo Hx Hlo); lia).
rewrite (cmp_shifted_correct (x * lo) (b + k) y) by (try apply Z.mul_pos_pos; lia).
cbv beta iota. rewrite scale_pow2 by lia.
destruct ex.
{ cbn [orb]. rewrite (proj1 Elo eq_refl). reflexivity. }
(* Not exact: [p < 2 ^ 34], as [5 ^ a] has fewer bits. *)
assert (Hj27 : (j < 27)%Z).
{ destruct (Z.eq_dec j 27) as [Ej|Ej]; [|lia]. exfalso. subst j.
  change (2 ^ (7 + 27))%Z with (2 ^ 34)%Z in Xlo.
  pose proof (nat_bits_pow5 a (proj1 Ha)).
  assert (H5 : (nat_bits (5 ^ a) <= 2 ^ 34)%Z) by lia.
  discriminate (Xlo H5). }
destruct (Rcompare (IZR x * bpow radix2 b * IZR (lo * 2 ^ k)) (IZR y)) eqn:O; cbn [orb].
3: { f_equal. symmetry. exact (cmp_gt_mono _ _ _ _ Hc Rlo O). }
all: destruct (pow5_bound_correct a (2 ^ (7 + j)) true Ha Hp)
  as (hi & k' & ex' & E' & Hhi & Bhi & Hk' & Rhi & _ & _).
all: rewrite E'; cbv beta iota.
all: rewrite (mul_z_correct x hi) by lia; cbv beta iota.
all: rewrite (checked_i_128_some (b + k')) by lia; cbv beta iota.
all: assert (Bxh : (nat_bits (x * hi) < 2 ^ 64)%Z) by (pose proof (nat_bits_mul x hi Hx Hhi); lia).
all: rewrite (cmp_shifted_correct (x * hi) (b + k') y) by (try apply Z.mul_pos_pos; lia).
all: cbv beta iota; rewrite scale_pow2 by lia.
all: destruct (Rcompare (IZR x * bpow radix2 b * IZR (hi * 2 ^ k')) (IZR y)) eqn:O'; cbv beta iota.
2, 5: (f_equal; symmetry; exact (cmp_lt_mono _ _ _ _ Hc Rhi O')).
all: rewrite (checked_u_some 64 (2 ^ (7 + j) * 2)) by lia; cbv beta iota.
all: replace (2 ^ (7 + j) * 2)%Z with (2 ^ (7 + (j + 1)))%Z
  by (rewrite Z.add_assoc, Z.pow_add_r, Z.pow_1_r by lia; reflexivity).
all: apply IH; lia.
Qed.

Lemma cmp_pow5_correct :
  forall x a b y loop_only,
  (0 < x < 2 ^ 2 ^ 62)%Z -> (0 < y < 2 ^ 2 ^ 62)%Z -> (0 <= a < 2 ^ 32)%Z ->
  (Z.abs b < 2 ^ 32)%Z ->
  rat_cmp_pow5 x a b y loop_only =
  Some (Rcompare (IZR x * bpow radix5 a * bpow radix2 b) (IZR y)).
Proof.
intros x a b y loop_only Hx Hy Ha Hb.
(* Keep [2 ^ 2 ^ 62] away from [lia]: only the bit counts are used. *)
assert (Bx : (nat_bits x <= 2 ^ 62)%Z) by (apply nat_bits_lt_pow; [exact (proj1 Hx) | exact (proj2 Hx)]).
assert (By : (nat_bits y <= 2 ^ 62)%Z) by (apply nat_bits_lt_pow; [exact (proj1 Hy) | exact (proj2 Hy)]).
destruct Hx as [Hx _]. destruct Hy as [Hy _].
pose proof (nat_bits_pos_spec x Hx) as (Bx1 & _).
pose proof (nat_bits_pos_spec y Hy) as (By1 & _).
replace (IZR x * bpow radix5 a * bpow radix2 b) with (IZR x * bpow radix2 b * IZR (5 ^ a))
  by (rewrite IZR_pow5 by lia; ring).
unfold rat_cmp_pow5.
destruct loop_only; cbv beta iota.
2: (rewrite !bits_z_correct by lia;
    rewrite (checked_u_some 64 (nat_bits x + nat_bits y)) by lia; cbv beta iota;
    rewrite checked_u_some by lia; cbv beta iota).
(* A [match goal] pattern under [all:] cannot name the hypothesis [a]. *)
all: match goal with |- context [(?A <=? ?L)%Z] => destruct (Z.leb_spec A L) as [HaL|HaL] end.
all: cbv beta iota.
1, 3: (rewrite (pow5_z_correct a) by lia; cbv beta iota;
       assert (H5 : (0 < 5 ^ a)%Z) by (apply Z.pow_pos_nonneg; lia);
       rewrite (mul_z_correct x (5 ^ a)) by lia; cbv beta iota;
       pose proof (nat_bits_mul x (5 ^ a) Hx H5); pose proof (nat_bits_pow5 a (proj1 Ha));
       rewrite (cmp_shifted_correct (x * 5 ^ a) b y) by (try apply Z.mul_pos_pos; lia);
       rewrite mult_IZR; f_equal; f_equal; ring).
all: change 128%Z with (2 ^ (7 + 0))%Z.
all: apply cmp_pow5_loop_correct; [exact Hx | exact Bx | exact Hy | exact By | exact Ha | exact Hb | lia
  | reflexivity].
Qed.
