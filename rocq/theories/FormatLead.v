(** * [format_lead] gives the exponent of the leading decimal digit

    [format_lead m e] is the [l] with [10^l <= m * 2^e < 10^(l + 1)] for
    the [(m, e)] that [format_decompose] gives a finite nonzero [f64]. It
    estimates [l] from the exponent [b] of the leading bit of [m * 2^e] as
    [floor(b * 315653 / 2^20)], which is [floor(b log10 2)] for each [b] of
    an [f64] ([floor_log10_pow2]), and tells [l] from the estimate and the
    one above it by comparing [m * 2^e] with a power of 10, which
    [format_ge_pow10] does exactly with the [Nat]s of [NatLimbs]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core.
From Fushimi Require Import Model.
From Fushimi Require NatOps.

Open Scope Z_scope.

(** The checked [i64] operations of [format_lead] and [format_ge_pow10]
    see only exponents of a few thousand at most in magnitude, and the
    product [b * 315653], below [2^29] in magnitude. *)
Lemma checked_i_64_lead :
  forall z, -1000000000000 <= z <= 1000000000000 -> checked_i 64 z = Some z.
Proof.
intros z Hz. unfold checked_i.
replace (- 2 ^ (64 - 1) <=? z) with true by (symmetry; apply Z.leb_le; lia).
replace (z <? 2 ^ (64 - 1)) with true by (symmetry; apply Z.ltb_lt; lia).
reflexivity.
Qed.

(** [Nat::pow5(k as u32)] and [&a << (s as u64)] for small [k, s >= 0]. *)
Lemma pow5_small :
  forall k, 0 <= k <= 1000000 -> NatLimbs.pow5_z (k mod 2 ^ 32) = Some (5 ^ k).
Proof.
intros k Hk. rewrite Z.mod_small by lia. apply NatOps.pow5_z_correct. lia.
Qed.

Lemma shl_small :
  forall a s, 0 <= a -> 0 <= s <= 1000000 ->
  NatLimbs.shl_z a (s mod 2 ^ 64) = a * 2 ^ s.
Proof.
intros a s Ha Hs. rewrite Z.mod_small by lia.
rewrite NatOps.shl_z_correct by lia. apply Z.shiftl_mul_pow2. lia.
Qed.

(** [a >= b] of [Nat]s, as [format_ge_pow10] reads [cmp_z a b]. *)
Lemma cmp_ge :
  forall a b,
  match Z.compare a b with Lt => Some false | _ => Some true end =
  Some (b <=? a).
Proof.
intros a b. destruct (Z.compare_spec a b) as [H | H | H]; cbv iota;
  f_equal; symmetry.
- apply Z.leb_le. lia.
- apply Z.leb_gt. lia.
- apply Z.leb_le. lia.
Qed.

(** [Rle_bool] of integers, and of reals scaled by the same [c > 0]. *)
Lemma Rle_bool_IZR : forall a b, Rle_bool (IZR a) (IZR b) = (a <=? b).
Proof.
intros a b. destruct (Z.leb_spec a b) as [H | H].
- apply Rle_bool_true. now apply IZR_le.
- apply Rle_bool_false. now apply IZR_lt.
Qed.

Lemma Rle_bool_mult_pos :
  forall x y c, (0 < c)%R -> Rle_bool (x * c) (y * c) = Rle_bool x y.
Proof.
intros x y c Hc. destruct (Rle_bool_spec x y) as [H | H].
- apply Rle_bool_true. apply Rmult_le_compat_r; lra.
- apply Rle_bool_false. now apply Rmult_lt_compat_r.
Qed.

(** Powers of 2 and 10 with exponents [e >= 0] are integers, and each
    power is the inverse of the one with exponent [-e]. *)
Lemma bpow2_IZR : forall e, 0 <= e -> bpow radix2 e = IZR (2 ^ e).
Proof. intros e He. now rewrite <- IZR_Zpower. Qed.

Lemma bpow10_IZR : forall e, 0 <= e -> bpow radix10 e = IZR (10 ^ e).
Proof. intros e He. now rewrite <- IZR_Zpower. Qed.

Lemma bpow_inv : forall (r : radix) e, bpow r e = (/ bpow r (- e))%R.
Proof. intros r e. now rewrite bpow_opp, Rinv_inv. Qed.

(** [10^k = 5^k * 2^k] for [k >= 0]. *)
Lemma bpow10_split :
  forall k, 0 <= k -> bpow radix10 k = (IZR (5 ^ k) * bpow radix2 k)%R.
Proof.
intros k Hk.
rewrite bpow10_IZR, bpow2_IZR, <- mult_IZR, <- Z.pow_mul_l by exact Hk.
reflexivity.
Qed.

(** The check of [floor_log10_pow2] for one [b], on integers. For [b < 0]
    the exponents [g] and [g + 1] are at most 0, and [10^g <= 2^b] and
    [2^b < 10^(g + 1)] are [2^-b <= 10^-g] and [10^-(g + 1) < 2^-b]. Each
    case computes one power [p] of 10 and takes the other as [10 * p], so
    that [lead_check_all] computes one power of 10 per [b], not two. *)
Definition lead_check (b : Z) : bool :=
  let g := Z.shiftr (b * 315653) 20 in
  if 0 <=? b then
    let p := 10 ^ g in
    (0 <=? g) && (p <=? 2 ^ b) && (2 ^ b <? 10 * p)
  else
    let p := 10 ^ (- (g + 1)) in
    (g <? 0) && (2 ^ (- b) <=? 10 * p) && (p <? 2 ^ (- b)).

(** [lead_check] of the [n] exponents from [b] on. *)
Fixpoint lead_check_from (b : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n => lead_check b && lead_check_from (b + 1) n
  end.

Lemma lead_check_from_spec :
  forall n b c, lead_check_from b n = true -> b <= c < b + Z.of_nat n ->
  lead_check c = true.
Proof.
induction n as [| n IH]; intros b c H Hc; [lia |].
cbn [lead_check_from] in H. apply andb_prop in H as [H1 H2].
destruct (Z.eq_dec c b) as [-> | Hcb]; [exact H1 |].
apply (IH (b + 1)); [exact H2 | lia].
Qed.

(** The 2098 exponents of an [f64]'s leading bit, by computation. *)
Lemma lead_check_all : lead_check_from (-1074) 2098 = true.
Proof. vm_compute. reflexivity. Qed.

(** [10^g <= 2^b < 10^(g + 1)] for [g = floor(b * 315653 / 2^20)] and each
    [b] from [-1074] to [1023]: the leading bits of the smallest subnormal
    to those of the largest [f64]. *)
Lemma floor_log10_pow2 :
  forall b, -1074 <= b <= 1023 ->
  (bpow radix10 (Z.shiftr (b * 315653) 20) <= bpow radix2 b <
   bpow radix10 (Z.shiftr (b * 315653) 20 + 1))%R.
Proof.
intros b Hb.
assert (H : lead_check b = true).
{ apply (lead_check_from_spec 2098 (-1074)); [exact lead_check_all | lia]. }
unfold lead_check in H. cbv zeta in H.
set (g := Z.shiftr (b * 315653) 20) in *.
destruct (0 <=? b) eqn:Eb.
- apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1, H2. apply Z.ltb_lt in H3. apply Z.leb_le in Eb.
  assert (E : 10 ^ (g + 1) = 10 * 10 ^ g)
    by (rewrite Z.pow_add_r, Z.pow_1_r by lia; ring).
  rewrite (bpow10_IZR g), (bpow2_IZR b), (bpow10_IZR (g + 1)), E by lia.
  split; [now apply IZR_le | now apply IZR_lt].
- apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1, H3. apply Z.leb_le in H2. apply Z.leb_gt in Eb.
  assert (E : 10 ^ (- g) = 10 * 10 ^ (- (g + 1))).
  { replace (- g) with (- (g + 1) + 1) by ring.
    rewrite Z.pow_add_r, Z.pow_1_r by lia. ring. }
  (* Both sides are inverses of powers with exponents [-g], [-b] and
     [-(g + 1)], all at least 0. *)
  rewrite (bpow_inv radix10 g), (bpow_inv radix2 b), (bpow_inv radix10 (g + 1)).
  split.
  + apply Rinv_le_contravar; [apply bpow_gt_0 |].
    rewrite bpow2_IZR, bpow10_IZR, E by lia. now apply IZR_le.
  + apply Rinv_lt_contravar.
    * apply Rmult_lt_0_compat; apply bpow_gt_0.
    * rewrite bpow2_IZR, bpow10_IZR by lia. now apply IZR_lt.
Qed.

(** For [k >= 0], [10^k <= m * 2^e] is [5^k <= m * 2^(e - k)], after
    dividing both sides by [2^k]. *)
Lemma ge_pow10_pos :
  forall m e k, 0 <= k ->
  Rle_bool (bpow radix10 k) (IZR m * bpow radix2 e) =
  Rle_bool (IZR (5 ^ k)) (IZR m * bpow radix2 (e - k)).
Proof.
intros m e k Hk.
rewrite <- (Rle_bool_mult_pos (IZR (5 ^ k)) (IZR m * bpow radix2 (e - k))
  (bpow radix2 k)) by apply bpow_gt_0.
rewrite bpow10_split by exact Hk. f_equal.
rewrite Rmult_assoc, <- bpow_plus. now replace (e - k + k) with e by ring.
Qed.

(** For [k < 0], [10^k <= m * 2^e] is [1 <= m * 5^-k * 2^(e - k)], after
    multiplying both sides by [10^-k = 5^-k * 2^-k]. *)
Lemma ge_pow10_neg :
  forall m e k, k < 0 ->
  Rle_bool (bpow radix10 k) (IZR m * bpow radix2 e) =
  Rle_bool 1 (IZR (m * 5 ^ (- k)) * bpow radix2 (e - k)).
Proof.
intros m e k Hk.
rewrite <- (Rle_bool_mult_pos (bpow radix10 k) (IZR m * bpow radix2 e)
  (bpow radix10 (- k))) by apply bpow_gt_0.
rewrite <- bpow_plus, Z.add_opp_diag_r. change (bpow radix10 0) with 1%R.
f_equal. rewrite bpow10_split by lia. rewrite mult_IZR.
replace (e - k) with (e + - k) by ring. rewrite bpow_plus. ring.
Qed.

(** [format_ge_pow10 m e k] tells whether [10^k <= m * 2^e]. *)
Lemma format_ge_pow10_correct :
  forall m e k, 0 < m < 2^64 -> -1074 <= e <= 971 -> -400 <= k <= 400 ->
  format_ge_pow10 m e k = Some (Rle_bool (bpow radix10 k) (IZR m * bpow radix2 e)).
Proof.
intros m e k Hm He Hk.
unfold format_ge_pow10.
rewrite NatOps.from_u64_z_correct by lia. cbv zeta.
destruct (0 <=? k) eqn:Ek.
- apply Z.leb_le in Ek.
  rewrite pow5_small by lia. cbv beta iota.
  rewrite ge_pow10_pos by exact Ek.
  assert (H5 : 0 <= 5 ^ k) by (apply Z.pow_nonneg; lia).
  destruct (k <=? e) eqn:Eke.
  + (* [m << (e - k) >= 5^k] *)
    apply Z.leb_le in Eke.
    rewrite (checked_i_64_lead (e - k)) by lia. cbv beta iota.
    rewrite shl_small by lia.
    assert (H2 : 0 <= 2 ^ (e - k)) by (apply Z.pow_nonneg; lia).
    rewrite NatOps.cmp_z_correct by nia. rewrite cmp_ge. f_equal.
    rewrite (bpow2_IZR (e - k)) by lia. now rewrite <- mult_IZR, Rle_bool_IZR.
  + (* [m >= 5^k << (k - e)], after multiplying both sides by
       [2^(k - e)] *)
    apply Z.leb_gt in Eke.
    rewrite (checked_i_64_lead (k - e)) by lia. cbv beta iota.
    rewrite shl_small by lia.
    assert (H2 : 0 <= 2 ^ (k - e)) by (apply Z.pow_nonneg; lia).
    rewrite NatOps.cmp_z_correct by nia. rewrite cmp_ge. f_equal.
    rewrite <- (Rle_bool_mult_pos _ _ (bpow radix2 (k - e))) by apply bpow_gt_0.
    rewrite Rmult_assoc, <- bpow_plus.
    replace (e - k + (k - e)) with 0 by ring.
    change (bpow radix2 0) with 1%R. rewrite Rmult_1_r.
    rewrite (bpow2_IZR (k - e)) by lia. now rewrite <- mult_IZR, Rle_bool_IZR.
- apply Z.leb_gt in Ek.
  rewrite ge_pow10_neg by exact Ek.
  assert (H5 : 1 <= 5 ^ (- k)).
  { assert (0 < 5 ^ (- k)) by (apply Z.pow_pos_nonneg; lia). lia. }
  destruct (k <=? e) eqn:Eke.
  + (* [m], [5^-k] and [2^(e - k)] are at least 1: [m * 2^e >= 2^k > 10^k] *)
    apply Z.leb_le in Eke. f_equal. symmetry. apply Rle_bool_true.
    rewrite (bpow2_IZR (e - k)) by lia. rewrite <- mult_IZR. apply IZR_le.
    assert (H2 : 1 <= 2 ^ (e - k)).
    { assert (0 < 2 ^ (e - k)) by (apply Z.pow_pos_nonneg; lia). lia. }
    nia.
  + (* [m * 5^-k >= 2^(k - e)], which is whether [m * 5^-k] has more
       than [k - e] bits, after multiplying both sides by [2^(k - e)] *)
    apply Z.leb_gt in Eke.
    rewrite (checked_i_64_lead (- k)) by lia. cbv beta iota.
    rewrite pow5_small by lia. cbv beta iota.
    rewrite NatOps.mul_z_correct by lia. cbv beta iota.
    rewrite (checked_i_64_lead (k - e)) by lia. cbv beta iota.
    rewrite (Z.mod_small (k - e)) by lia.
    rewrite NatOps.bits_z_correct by nia. unfold nat_bits.
    replace (m * 5 ^ (- k) =? 0) with false by (symmetry; apply Z.eqb_neq; nia).
    f_equal.
    rewrite <- (Rle_bool_mult_pos _ _ (bpow radix2 (k - e))) by apply bpow_gt_0.
    rewrite Rmult_1_l, Rmult_assoc, <- bpow_plus.
    replace (e - k + (k - e)) with 0 by ring.
    change (bpow radix2 0) with 1%R. rewrite Rmult_1_r.
    rewrite (bpow2_IZR (k - e)) by lia. rewrite Rle_bool_IZR.
    apply Bool.eq_true_iff_eq. rewrite Z.ltb_lt, Z.leb_le.
    rewrite Z.log2_le_pow2 by nia. lia.
Qed.

(** [format_lead m e] is the exponent of the leading decimal digit of
    [m * 2^e]. *)
Lemma format_lead_correct :
  forall m e, 0 < m < 2^53 -> -1074 <= e <= 971 ->
  exists l, format_lead m e = Some l /\
  (bpow radix10 l <= IZR m * bpow radix2 e < bpow radix10 (l + 1))%R.
Proof.
intros m e Hm He.
assert (Hl : 0 <= Z.log2 m < 53).
{ split; [apply Z.log2_nonneg | apply Z.log2_lt_pow2; lia]. }
unfold format_lead.
rewrite (checked_i_64_lead (e + 63)) by lia. cbv beta iota.
(* [b = e + 63 - m.leading_zeros()] is the exponent [e + log2 m] of the
   leading bit of [m * 2^e], from [-1074] to [1023]. *)
unfold leading_zeros.
replace (m =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
replace (e + 63 - (64 - 1 - Z.log2 m)) with (e + Z.log2 m) by ring.
set (b := e + Z.log2 m).
assert (Hb : -1074 <= b <= 1023) by (unfold b; lia).
assert (Hx : (bpow radix2 b <= IZR m * bpow radix2 e < bpow radix2 (b + 1))%R).
{ destruct (Z.log2_spec m) as [H1 H2]; [lia |].
  replace (b + 1) with (Z.succ (Z.log2 m) + e) by (unfold b; lia).
  replace b with (Z.log2 m + e) by (unfold b; lia).
  rewrite !bpow_plus.
  rewrite (bpow2_IZR (Z.log2 m)), (bpow2_IZR (Z.succ (Z.log2 m))) by lia.
  pose proof (bpow_gt_0 radix2 e).
  split; [apply Rmult_le_compat_r | apply Rmult_lt_compat_r]; try lra.
  - now apply IZR_le.
  - now apply IZR_lt. }
rewrite (checked_i_64_lead b) by lia. cbv beta iota.
rewrite (checked_i_64_lead (b * 315653)) by lia. cbv beta iota zeta.
destruct (floor_log10_pow2 b Hb) as [Hlo Hhi].
set (g := Z.shiftr (b * 315653) 20) in *.
(* [g] lies in [-324, 307], so [g + 1] fits [format_ge_pow10_correct]. *)
assert (Hg : -401 <= g <= 399).
{ unfold g. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. }
rewrite (checked_i_64_lead (g + 1)) by lia. cbv beta iota.
rewrite format_ge_pow10_correct by lia. cbv beta iota.
destruct (Rle_bool_spec (bpow radix10 (g + 1)) (IZR m * bpow radix2 e))
  as [H | H].
- (* [m * 2^e < 2^(b + 1) = 2 * 2^b < 2 * 10^(g + 1) < 10^(g + 2)] *)
  exists (g + 1). split; [reflexivity |]. split; [exact H |].
  assert (E2 : bpow radix2 (b + 1) = (2 * bpow radix2 b)%R).
  { rewrite bpow_plus. change (bpow radix2 1) with 2%R. ring. }
  assert (E10 : bpow radix10 (g + 1 + 1) = (10 * bpow radix10 (g + 1))%R).
  { rewrite (bpow_plus radix10 (g + 1) 1). change (bpow radix10 1) with 10%R.
    ring. }
  pose proof (bpow_gt_0 radix10 (g + 1)). lra.
- (* [10^g <= 2^b <= m * 2^e < 10^(g + 1)] *)
  exists g. split; [reflexivity |]. split; [lra | exact H].
Qed.
