(** The integer operations of the accurate phase of x^y
    ([src/dyadic/pow/acc.rs]): [DyadicPow.mul_wide] is the product of two
    integers below 2^128 as its high and low 128 bits, [DyadicPow.mul_dn]
    and [DyadicPow.mul_up] are that product divided by 2^s and rounded
    down and up, [DyadicPow.shr_dn] and [DyadicPow.shr_up] give bounds
    below and above the 256-bit number [hi 2^128 + lo] times 2^-s for any
    [s], and [DyadicPow.signed] turns bounds on a magnitude into bounds on
    a signed number. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core.
From Fushimi Require Import Model.
From Fushimi Require Limbs.

Open Scope Z_scope.

(** ** Helpers on [Z] *)

(** [Z.land x (2 ^ s - 1)] keeps the low [s] bits of [x]. *)
Local Lemma land_pow2 : forall x s, 0 <= s -> Z.land x (2 ^ s - 1) = x mod 2 ^ s.
Proof.
  intros x s Hs. rewrite Z.sub_1_r, <- Z.ones_equiv. apply Z.land_ones. exact Hs.
Qed.

Local Lemma land_m64 : forall x, Z.land x DyadicPow.m64 = x mod 2 ^ 64.
Proof. intros x. unfold DyadicPow.m64. apply land_pow2. lia. Qed.

Local Lemma split_div : forall x d, 0 < d -> x = x / d * d + x mod d /\ 0 <= x mod d < d.
Proof.
  intros x d Hd. split.
  - rewrite Z.mul_comm. apply Z.div_mod. lia.
  - apply Z.mod_pos_bound. exact Hd.
Qed.

(** A quotient and a remainder determine the division. *)
Local Lemma pair_divmod :
  forall x B q r, 0 <= r < B -> x = q * B + r -> (q, r) = (x / B, x mod B).
Proof.
  intros x B q r Hr ->. f_equal.
  - rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. ring.
  - rewrite Z.add_comm, Z.mod_add by lia. symmetry. apply Z.mod_small. exact Hr.
Qed.

(** [mid << 64] of a [u128] keeps the low 64 bits of [mid]. *)
Local Lemma mul64_mod128 : forall x, (x * 2 ^ 64) mod 2 ^ 128 = x mod 2 ^ 64 * 2 ^ 64.
Proof.
  intros x. change (2 ^ 128) with (2 ^ 64 * 2 ^ 64). apply Z.mul_mod_distr_r; lia.
Qed.

(** The low [s] bits of [x mod 2 ^ t] are those of [x] for [s <= t]. *)
Local Lemma mod_mod_pow2 : forall x s t, 0 <= s <= t -> x mod 2 ^ t mod 2 ^ s = x mod 2 ^ s.
Proof.
  intros x s t Hst. apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i s) as [Hlt | Hge].
  - rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(** The quotient rounded up is the quotient rounded down plus 1 unless
    the remainder is 0. *)
Local Lemma ceil_div :
  forall x d, 0 < d -> (x + d - 1) / d = x / d + (if x mod d =? 0 then 0 else 1).
Proof.
  intros x d Hd. destruct (split_div x d Hd) as [E R].
  set (q := x / d) in *. set (r := x mod d) in *. clearbody q r.
  destruct (Z.eqb_spec r 0) as [R0 | R0]; cbn [negb]; symmetry.
  - apply Z.div_unique with (r := d - 1); lia.
  - apply Z.div_unique with (r := r - 1); lia.
Qed.

(** [hi << (128 - s) | lo >> s] is [(hi 2^128 + lo) / 2^s] where [hi] has
    no bits from [s] up. *)
Local Lemma shr_combine :
  forall hi lo s, 0 < s < 128 -> 0 <= hi < 2 ^ s -> 0 <= lo < 2 ^ 128 ->
  Z.lor (Z.shiftl hi (128 - s) mod 2 ^ 128) (Z.shiftr lo s) = (hi * 2 ^ 128 + lo) / 2 ^ s.
Proof.
  intros hi lo s Hs Hh Hl.
  assert (P : 2 ^ 128 = 2 ^ (128 - s) * 2 ^ s) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (P1 : 0 < 2 ^ (128 - s)) by (apply Z.pow_pos_nonneg; lia).
  assert (P2 : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (rewrite P; nia).
  rewrite Limbs.lor_low by
    (lia || (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia)).
  rewrite P. replace (hi * (2 ^ (128 - s) * 2 ^ s) + lo) with (hi * 2 ^ (128 - s) * 2 ^ s + lo)
    by ring.
  rewrite Z.div_add_l by lia. reflexivity.
Qed.

(** [Some x = Some y] gives [x = y] with [x] as it is: [injection] unfolds
    [128 - s] and [2 ^ 128] in [x], and then a [rewrite] finds no match. *)
Local Lemma some_eq : forall (A : Type) (x y : A), Some x = Some y -> x = y.
Proof. intros A x y H. injection H. intros E. exact E. Qed.

Local Lemma checked_u_inv : forall w z q, checked_u w z = Some q -> q = z /\ 0 <= z.
Proof.
  intros w z q. unfold checked_u.
  destruct (Z.leb_spec 0 z) as [Z0 | Z0], (z <? 2 ^ w); cbn [andb]; intros H;
    try discriminate H.
  injection H as <-. split; [reflexivity | exact Z0].
Qed.

Local Lemma checked_i_inv :
  forall z q, checked_i 128 z = Some q -> q = z /\ - 2 ^ 127 <= z < 2 ^ 127.
Proof.
  intros z q. unfold checked_i. change (128 - 1) with 127.
  destruct (Z.leb_spec (- 2 ^ 127) z) as [Z0 | Z0], (Z.ltb_spec z (2 ^ 127)) as [Z1 | Z1];
    cbn [andb]; intros H; try discriminate H.
  injection H as <-. split; [reflexivity | lia].
Qed.

(** ** From [Z] to [R] *)

Local Lemma le_pos : forall q n s, 0 <= s -> q * 2 ^ s <= n -> (IZR q * bpow radix2 s <= IZR n)%R.
Proof.
  intros q n s Hs H. rewrite <- (IZR_Zpower radix2 s Hs), <- mult_IZR. apply IZR_le. exact H.
Qed.

Local Lemma ge_pos : forall q n s, 0 <= s -> n <= q * 2 ^ s -> (IZR n <= IZR q * bpow radix2 s)%R.
Proof.
  intros q n s Hs H. rewrite <- (IZR_Zpower radix2 s Hs), <- mult_IZR. apply IZR_le. exact H.
Qed.

(** [bpow radix2 s * 2 ^ -s = 1] for [s < 0]. *)
Local Lemma bpow_neg_inv :
  forall s, s < 0 -> (bpow radix2 s * IZR (2 ^ (- s)) = 1)%R.
Proof.
  intros s Hs.
  assert (E : IZR (2 ^ (- s)) = bpow radix2 (- s)) by exact (IZR_Zpower radix2 (- s) ltac:(lia)).
  rewrite E, <- bpow_plus. replace (s + - s) with 0 by ring. reflexivity.
Qed.

Local Lemma le_neg :
  forall q n s, s < 0 -> q <= n * 2 ^ (- s) -> (IZR q * bpow radix2 s <= IZR n)%R.
Proof.
  intros q n s Hs H. apply IZR_le in H. rewrite mult_IZR in H.
  pose proof (bpow_gt_0 radix2 s) as B. pose proof (bpow_neg_inv s Hs) as I.
  apply Rle_trans with (IZR n * IZR (2 ^ (- s)) * bpow radix2 s)%R.
  - apply Rmult_le_compat_r; lra.
  - right. rewrite Rmult_assoc, (Rmult_comm (IZR (2 ^ (- s)))), I. ring.
Qed.

Local Lemma ge_neg :
  forall q n s, s < 0 -> n * 2 ^ (- s) <= q -> (IZR n <= IZR q * bpow radix2 s)%R.
Proof.
  intros q n s Hs H. apply IZR_le in H. rewrite mult_IZR in H.
  pose proof (bpow_gt_0 radix2 s) as B. pose proof (bpow_neg_inv s Hs) as I.
  apply Rle_trans with (IZR n * IZR (2 ^ (- s)) * bpow radix2 s)%R.
  - right. rewrite Rmult_assoc, (Rmult_comm (IZR (2 ^ (- s)))), I. ring.
  - apply Rmult_le_compat_r; lra.
Qed.

(** ** The operations *)

Lemma mul_wide_correct :
  forall a b, 0 <= a < 2 ^ 128 -> 0 <= b < 2 ^ 128 ->
  DyadicPow.mul_wide a b = (a * b / 2 ^ 128, a * b mod 2 ^ 128).
Proof.
  intros a b Ha Hb. unfold DyadicPow.mul_wide. cbv beta zeta.
  assert (P64 : 0 < 2 ^ 64) by lia.
  rewrite !land_m64, !Z.shiftr_div_pow2, Z.shiftl_mul_pow2, mul64_mod128 by lia.
  rewrite Limbs.lor_low by (lia || (apply Z.mod_pos_bound; lia)).
  (* The digits of [a] and [b] in base 2^64, and the four products. *)
  destruct (split_div a (2 ^ 64) P64) as [Ea _].
  destruct (split_div b (2 ^ 64) P64) as [Eb _].
  set (a0 := a mod 2 ^ 64) in *. set (a1 := a / 2 ^ 64) in *.
  set (b0 := b mod 2 ^ 64) in *. set (b1 := b / 2 ^ 64) in *.
  clearbody a0 a1 b0 b1. subst a b.
  remember (a0 * b0) as p00. remember (a0 * b1) as p01.
  remember (a1 * b0) as p10. remember (a1 * b1) as p11.
  remember (p00 / 2 ^ 64 + p01 mod 2 ^ 64 + p10 mod 2 ^ 64) as mid.
  destruct (split_div p00 (2 ^ 64) P64) as [E00 R00].
  destruct (split_div p01 (2 ^ 64) P64) as [E01 _].
  destruct (split_div p10 (2 ^ 64) P64) as [E10 _].
  destruct (split_div mid (2 ^ 64) P64) as [Em Rm].
  apply pair_divmod; [lia |].
  (* [a b = p11 2^128 + (p01 + p10) 2^64 + p00], and [mid] carries the
     middle digit. *)
  assert (Eab : (a1 * 2 ^ 64 + a0) * (b1 * 2 ^ 64 + b0) =
                p11 * 2 ^ 128 + (p01 + p10) * 2 ^ 64 + p00) by (subst; ring).
  rewrite Eab. lia.
Qed.

Lemma mul_dn_correct :
  forall a b s, 0 <= a < 2 ^ 128 -> 0 <= b < 2 ^ 128 -> 0 < s < 128 -> a * b < 2 ^ (128 + s) ->
  DyadicPow.mul_dn a b s = a * b / 2 ^ s.
Proof.
  intros a b s Ha Hb Hs Hab. unfold DyadicPow.mul_dn. rewrite mul_wide_correct by assumption.
  cbv beta iota.
  assert (P : 2 ^ (128 + s) = 2 ^ 128 * 2 ^ s) by (apply Z.pow_add_r; lia).
  assert (P2 : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (A0 : 0 <= a * b) by nia.
  rewrite shr_combine.
  - destruct (split_div (a * b) (2 ^ 128) ltac:(lia)) as [E _]. rewrite <- E. reflexivity.
  - exact Hs.
  - split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
  - apply Z.mod_pos_bound. lia.
Qed.

Lemma mul_up_correct :
  forall a b s, 0 <= a < 2 ^ 128 -> 0 <= b < 2 ^ 128 -> 0 < s < 128 -> a * b < 2 ^ (128 + s) ->
  DyadicPow.mul_up a b s = (a * b + 2 ^ s - 1) / 2 ^ s.
Proof.
  intros a b s Ha Hb Hs Hab. unfold DyadicPow.mul_up. rewrite mul_wide_correct by assumption.
  cbv beta iota.
  assert (P : 2 ^ (128 + s) = 2 ^ 128 * 2 ^ s) by (apply Z.pow_add_r; lia).
  assert (P2 : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (A0 : 0 <= a * b) by nia.
  rewrite shr_combine.
  - destruct (split_div (a * b) (2 ^ 128) ltac:(lia)) as [E _]. rewrite <- E.
    (* The dropped bits of [lo] are those of [a b]. *)
    rewrite Z.shiftl_1_l, land_pow2, mod_mod_pow2 by lia.
    rewrite ceil_div by exact P2. reflexivity.
  - exact Hs.
  - split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
  - apply Z.mod_pos_bound. lia.
Qed.

Lemma shr_dn_correct :
  forall hi lo s q, 0 <= hi < 2 ^ 128 -> 0 <= lo < 2 ^ 128 ->
  DyadicPow.shr_dn (hi, lo) s = Some q ->
  0 <= q /\ (IZR q * bpow radix2 s <= IZR (hi * 2 ^ 128 + lo))%R.
Proof.
  intros hi lo s q Hh Hl. unfold DyadicPow.shr_dn. cbv beta iota.
  destruct (Z.leb_spec 256 s) as [S1 | S1]; cbn [negb andb].
  { (* [q = 0]. *)
    intros H. apply some_eq in H. subst q. split; [lia |]. apply le_pos; lia. }
  destruct (Z.leb_spec 128 s) as [S2 | S2]; cbn [negb andb].
  { (* [q = hi / 2^(s - 128)]. *)
    intros H. apply some_eq in H. subst q. rewrite Z.shiftr_div_pow2 by lia.
    assert (P : 2 ^ s = 2 ^ (s - 128) * 2 ^ 128)
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (P1 : 0 < 2 ^ (s - 128)) by (apply Z.pow_pos_nonneg; lia).
    pose proof (Z.mul_div_le hi (2 ^ (s - 128)) P1).
    split; [apply Z.div_pos; lia |]. apply le_pos; [lia |]. rewrite P. lia. }
  destruct (Z.ltb_spec 0 s) as [S3 | S3]; cbn [negb andb].
  { (* [q = (hi 2^128 + lo) / 2^s] where [hi < 2^s]. *)
    destruct (Z.eqb_spec (Z.shiftr hi s) 0) as [S4 | S4]; cbn [negb]; intros H;
      [| discriminate H].
    apply some_eq in H. subst q.
    assert (P2 : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
    rewrite Z.shiftr_div_pow2 in S4 by lia.
    pose proof (proj1 (Z.div_small_iff hi (2 ^ s) ltac:(lia)) S4).
    rewrite shr_combine by lia.
    pose proof (Z.mul_div_le (hi * 2 ^ 128 + lo) (2 ^ s) P2).
    split; [apply Z.div_pos; lia |]. apply le_pos; lia. }
  (* [s <= 0], where [hi = 0]. *)
  destruct (Z.eqb_spec hi 0) as [H0 | H0]; cbn [negb]; [| intros H; discriminate H].
  subst hi.
  destruct (Z.eqb_spec s 0) as [S5 | S5]; cbn [negb andb].
  { intros H. apply some_eq in H. subst q. subst s. split; [lia |]. apply le_pos; lia. }
  destruct (Z.ltb_spec (-128) s) as [S6 | S6]; cbn [negb andb].
  - destruct (Z.eqb_spec (Z.shiftr lo (128 + s)) 0) as [S7 | S7]; cbn [negb andb].
    + (* [q = lo 2^-s], where [lo < 2^(128 + s)]. *)
      intros H. apply some_eq in H. subst q.
      assert (P : 2 ^ 128 = 2 ^ (128 + s) * 2 ^ (- s))
        by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (P1 : 0 < 2 ^ (128 + s)) by (apply Z.pow_pos_nonneg; lia).
      assert (P2 : 0 < 2 ^ (- s)) by (apply Z.pow_pos_nonneg; lia).
      rewrite Z.shiftr_div_pow2 in S7 by lia.
      pose proof (proj1 (Z.div_small_iff lo (2 ^ (128 + s)) ltac:(lia)) S7).
      rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (rewrite P; nia).
      split; [nia |]. apply le_neg; lia.
    + destruct (Z.eqb_spec lo 0) as [L0 | L0]; cbn [negb andb]; intros H; [| discriminate H].
      apply some_eq in H. subst q. subst lo. split; [lia |]. apply le_neg; lia.
  - destruct (Z.eqb_spec lo 0) as [L0 | L0]; cbn [negb andb]; intros H; [| discriminate H].
    apply some_eq in H. subst q. subst lo. split; [lia |]. apply le_neg; lia.
Qed.

Lemma shr_up_correct :
  forall hi lo s q, 0 <= hi < 2 ^ 128 -> 0 <= lo < 2 ^ 128 ->
  DyadicPow.shr_up (hi, lo) s = Some q ->
  0 <= q /\ (IZR (hi * 2 ^ 128 + lo) <= IZR q * bpow radix2 s)%R.
Proof.
  intros hi lo s q Hh Hl. unfold DyadicPow.shr_up, DyadicPow.shr_dn. cbv beta iota zeta.
  destruct (Z.leb_spec 256 s) as [S1 | S1]; cbn [negb orb].
  { (* [q] is 0 or 1, and [hi 2^128 + lo < 2^256 <= 2^s]. *)
    intros H. apply checked_u_inv in H. destruct H as [-> Hq]. split; [exact Hq |].
    apply ge_pos; [lia |].
    assert (P : 2 ^ 256 <= 2 ^ s) by (apply Z.pow_le_mono_r; lia).
    destruct (Z.eqb_spec (Z.lor hi lo) 0) as [L0 | L0]; cbn [negb].
    - apply Z.lor_eq_0_iff in L0. lia.
    - lia. }
  destruct (Z.leb_spec 128 s) as [S2 | S2]; cbn [negb orb].
  { (* [q = hi / 2^(s - 128)] plus 1 where bits are dropped. *)
    intros H. apply checked_u_inv in H. destruct H as [-> Hq]. split; [exact Hq |].
    apply ge_pos; [lia |].
    rewrite Z.shiftr_div_pow2, Z.shiftl_1_l, land_pow2 by lia.
    assert (P : 2 ^ s = 2 ^ (s - 128) * 2 ^ 128)
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (P1 : 0 < 2 ^ (s - 128)) by (apply Z.pow_pos_nonneg; lia).
    rewrite P. destruct (split_div hi (2 ^ (s - 128)) P1) as [E R].
    set (D := 2 ^ (s - 128)) in *. clearbody D.
    destruct (Z.eqb_spec lo 0), (Z.eqb_spec (hi mod D) 0); cbn [negb orb]; lia. }
  destruct (Z.ltb_spec 0 s) as [S3 | S3]; cbn [negb orb].
  { (* [q = (hi 2^128 + lo) / 2^s] plus 1 where bits are dropped. *)
    destruct (Z.eqb_spec (Z.shiftr hi s) 0) as [S4 | S4]; cbn [negb]; intros H;
      [| discriminate H].
    apply checked_u_inv in H. destruct H as [-> Hq]. split; [exact Hq |].
    apply ge_pos; [lia |].
    assert (P : 2 ^ 128 = 2 ^ (128 - s) * 2 ^ s) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (P2 : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
    rewrite Z.shiftr_div_pow2 in S4 by lia.
    pose proof (proj1 (Z.div_small_iff hi (2 ^ s) ltac:(lia)) S4).
    rewrite shr_combine, Z.shiftl_1_l, land_pow2 by lia.
    (* The dropped bits of [lo] are those of [hi 2^128 + lo]. *)
    assert (M : lo mod 2 ^ s = (hi * 2 ^ 128 + lo) mod 2 ^ s).
    { replace (hi * 2 ^ 128 + lo) with (lo + hi * 2 ^ (128 - s) * 2 ^ s) by (rewrite P; ring).
      rewrite Z.mod_add by lia. reflexivity. }
    rewrite M. destruct (split_div (hi * 2 ^ 128 + lo) (2 ^ s) P2) as [E R].
    set (N := hi * 2 ^ 128 + lo) in *. clearbody N.
    destruct (Z.eqb_spec (N mod 2 ^ s) 0); cbn [negb]; lia. }
  (* [s <= 0], where [hi = 0] and no bits are dropped. *)
  destruct (Z.eqb_spec hi 0) as [H0 | H0]; cbn [negb]; [| intros H; discriminate H].
  subst hi.
  destruct (Z.eqb_spec s 0) as [S5 | S5]; cbn [negb andb].
  { intros H. apply checked_u_inv in H. destruct H as [-> Hq]. subst s.
    split; [exact Hq |]. apply ge_pos; lia. }
  destruct (Z.ltb_spec (-128) s) as [S6 | S6]; cbn [negb andb].
  - destruct (Z.eqb_spec (Z.shiftr lo (128 + s)) 0) as [S7 | S7]; cbn [negb andb].
    + (* [q = lo 2^-s], where [lo < 2^(128 + s)]. *)
      intros H. apply checked_u_inv in H. destruct H as [-> Hq]. split; [exact Hq |].
      assert (P : 2 ^ 128 = 2 ^ (128 + s) * 2 ^ (- s))
        by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (P1 : 0 < 2 ^ (128 + s)) by (apply Z.pow_pos_nonneg; lia).
      assert (P2 : 0 < 2 ^ (- s)) by (apply Z.pow_pos_nonneg; lia).
      rewrite Z.shiftr_div_pow2 in S7 by lia.
      pose proof (proj1 (Z.div_small_iff lo (2 ^ (128 + s)) ltac:(lia)) S7).
      rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (rewrite P; nia).
      apply ge_neg; lia.
    + destruct (Z.eqb_spec lo 0) as [L0 | L0]; cbn [negb andb]; intros H; [| discriminate H].
      apply checked_u_inv in H. destruct H as [-> Hq]. subst lo. split; [exact Hq |].
      apply ge_neg; lia.
  - destruct (Z.eqb_spec lo 0) as [L0 | L0]; cbn [negb andb]; intros H; [| discriminate H].
    apply checked_u_inv in H. destruct H as [-> Hq]. subst lo. split; [exact Hq |].
    apply ge_neg; lia.
Qed.

Lemma signed_correct :
  forall neg lo hi l h, DyadicPow.signed neg lo hi = Some (l, h) ->
  - 2 ^ 127 <= lo < 2 ^ 127 /\ - 2 ^ 127 <= hi < 2 ^ 127 /\
  (if neg then l = - hi /\ h = - lo else l = lo /\ h = hi).
Proof.
  intros neg lo hi l h. unfold DyadicPow.signed.
  destruct (checked_i 128 lo) as [lo' |] eqn:L; cbv beta iota; [| intros H; discriminate H].
  destruct (checked_i 128 hi) as [hi' |] eqn:K; cbv beta iota; [| intros H; discriminate H].
  intros H. apply checked_i_inv in L, K. destruct L as [-> L]. destruct K as [-> K].
  split; [exact L | split; [exact K |]].
  destruct neg; cbv beta iota in H |- *; apply some_eq, pair_equal_spec in H; lia.
Qed.
