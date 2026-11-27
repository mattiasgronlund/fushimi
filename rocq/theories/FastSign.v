(** * The rounding tests of the fast paths for results of either sign

    [Fast.round_dir_signed] and [Fast.round_near_signed] of [Model.v]
    take an [h] of either sign with [1/2 < |h| < 2], with no branch on
    the sign of [h]: [Fast.round_dir_signed] steps from the bits of [h]
    by the sign bits of [h] and [l], and [Fast.round_near_signed] tests
    [l], with its sign bit xored with that of [h], against the gaps of
    [|h|] and returns [h 2^e]. For [h < 0] that is rounding [-y 2^e]
    from [-h] and [-l] with [Fast.round_dir] in the other direction, or
    with [Fast.round_near], and negating the result
    ([round_dir_signed_eq], [round_near_signed_eq]). That is the
    rounding of [y 2^e], as rounding toward -inf is the negation of
    rounding toward +inf of the negation, and rounding to nearest is odd
    ([round_dir_signed_correct], [round_near_signed_correct]).
    [Fast.round_dir_signed_branch] and [Fast.round_near_signed_branch]
    branch on [h < 0] and do that rounding and negation themselves
    ([round_dir_signed_branch_correct], [round_near_signed_branch_correct]).
    Which fast path calls which form is in [Model.v]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Fushimi Require Import Model Mpfr Encoding TwoSum DyDriver NearF64 NearCells FastRound.
From Fushimi Require RoundOpp FastRoundSubBits.

Open Scope R_scope.

(** [lt h zero] as a comparison of reals, for a finite [h]. *)
Lemma lt_zero_R :
  forall h, is_finite h = true -> if lt h zero then B2R h < 0 else 0 <= B2R h.
Proof.
intros h Fh. unfold lt. rewrite Bltb_correct by easy.
change (B2R zero) with 0.
destruct (Rlt_bool_spec (B2R h) 0) as [H | H]; exact H.
Qed.

(** For [h < 0], [-h], [-l] and [-y] satisfy the hypotheses of
    [round_dir_correct] and [round_near_correct], as rounding to nearest
    is odd. *)
Lemma opp_pair :
  forall h l y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < Rabs (B2R h) < 2 -> B2R h < 0 ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  is_finite (opp h) = true /\ is_finite (opp l) = true /\
  B2R (opp h) = RN (B2R (opp h) + B2R (opp l)) /\ / 2 < B2R (opp h) < 2 /\
  Rabs (- y - (B2R (opp h) + B2R (opp l))) <= bpow radix2 (-68).
Proof.
intros h l y Fh Fl Hrn Hh Hn Hy. unfold opp.
rewrite !is_finite_Bopp, !B2R_Bopp.
rewrite Rabs_left in Hh by exact Hn.
split; [exact Fh |]. split; [exact Fl |].
split; [rewrite <- Ropp_plus_distr, round_NE_opp, <- Hrn; reflexivity |].
split; [lra |].
replace (- y - (- B2R h + - B2R l)) with (- (y - (B2R h + B2R l))) by ring.
rewrite Rabs_Ropp. exact Hy.
Qed.

(** Bit 63 of a finite [x] is its sign, as its other bits are below
    [2047 * 2^52 < 2^63]. *)
Local Lemma sign_shiftr :
  forall x, is_finite x = true -> Z.shiftr (to_bits x) 63 = Z.b2z (Bsign x).
Proof.
intros x Fx.
destruct (to_bits_finite x Fx) as (c & Hc & Hb).
rewrite Hb, Z.shiftr_div_pow2 by lia. unfold sign_bit.
simpl Z.pow in Hc |- *.
destruct (Bsign x); cbn [Z.b2z].
- symmetry. apply Z.div_unique with (r := c); lia.
- apply Z.div_small. lia.
Qed.

(** Setting the sign bit of a finite pattern [k] negates its float. *)
Local Lemma from_bits_neg :
  forall k, (0 <= k < 2047 * 2^52)%Z ->
  is_finite (from_bits k) = true /\ from_bits (sign_bit true + k) = opp (from_bits k).
Proof.
intros k Hk.
destruct (from_bits_finite true k Hk) as (F1 & S1 & R1).
destruct (from_bits_finite false k Hk) as (F0 & S0 & R0).
cbn [sign_bit] in F0, S0, R0. rewrite Z.add_0_l in F0, S0, R0.
split; [exact F0 |].
apply B2R_Bsign_inj.
- exact F1.
- unfold opp. rewrite is_finite_Bopp. exact F0.
- unfold opp. rewrite B2R_Bopp, R1, R0. reflexivity.
- unfold opp. rewrite Bsign_Bopp, S1, S0 by (destruct (from_bits k); easy). reflexivity.
Qed.

(** [Fast.scale] is odd, as [2^e] is a positive [f64] and rounding to
    nearest, and its overflow, are odd. *)
Local Lemma scale_opp :
  forall r e, is_finite r = true -> (-1021 <= e <= 1022)%Z ->
  Fast.scale (opp r) e = opp (Fast.scale r e).
Proof.
intros r e Fr He.
destruct (pow2_bits e ltac:(lia)) as (Fp & Rp).
unfold Fast.scale, mul, opp.
set (p := from_bits _) in *.
assert (Sp : Bsign p = false).
{ rewrite (StepUp.Bsign_B2R p Fp) by (rewrite Rp; apply Rgt_not_eq, bpow_gt_0).
  rewrite Rp. apply Rlt_bool_false. apply Rlt_le, bpow_gt_0. }
assert (Nr : is_nan r = false) by (destruct r; easy).
generalize (@Bmult_correct 53 1024 _ _ mode_NE (Bopp r) p).
generalize (@Bmult_correct 53 1024 _ _ mode_NE r p).
rewrite B2R_Bopp, Rp, (Bsign_Bopp _ _ r Nr), Sp, is_finite_Bopp, Fr, Fp.
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE)) with RN.
replace (- B2R r * bpow radix2 e) with (- (B2R r * bpow radix2 e)) by ring.
rewrite round_NE_opp, Rabs_Ropp.
destruct Rlt_bool.
- intros (R0 & F0 & S0) (R1 & F1 & S1).
  assert (N0 : is_nan (Bmult mode_NE r p) = false)
    by (revert F0; destruct (Bmult mode_NE r p); easy).
  assert (N1 : is_nan (Bmult mode_NE (Bopp r) p) = false)
    by (revert F1; destruct (Bmult mode_NE (Bopp r) p); easy).
  apply B2R_Bsign_inj.
  + exact F1.
  + rewrite is_finite_Bopp. exact F0.
  + rewrite B2R_Bopp, R1, R0. reflexivity.
  + rewrite (Bsign_Bopp _ _ _ N0), (S1 N1), (S0 N0). destruct (Bsign r); reflexivity.
- (* Overflow: both are infinities, of opposite signs. *)
  intros H0 H1. apply B2SF_inj. rewrite H1.
  destruct (Bmult mode_NE r p) as [s|s| |s m e' Hm]; try discriminate H0.
  cbn in H0 |- *. injection H0 as ->. destruct (Bsign r); reflexivity.
Qed.

(** [Fast.round_dir_signed], which steps from the bits of [h] by the sign
    bits of [h] and [l], is [Fast.round_dir] of [h] and [l] where [h > 0],
    and the negative of [Fast.round_dir] of [-h] and [-l] in the other
    direction where [h < 0]. [Fast.scale] then keeps the sign, as [2^e]
    is a positive [f64] for [-1021 <= e <= 1022]. *)
Local Lemma round_dir_signed_eq :
  forall h l e up,
  is_finite h = true -> is_finite l = true -> / 2 < Rabs (B2R h) < 2 ->
  (-1021 <= e <= 1022)%Z ->
  Fast.round_dir_signed h l e up =
  if lt h zero then
    match Fast.round_dir (opp h) (opp l) e (negb up) with Some r => Some (opp r) | None => None end
  else Fast.round_dir h l e up.
Proof.
intros h l e up Fh Fl Hh He.
assert (Sh : Bsign h = lt h zero).
{ apply Encoding.Bsign_lt_zero; [exact Fh |]. intros H0. rewrite H0, Rabs_R0 in Hh. lra. }
rewrite <- Sh.
unfold Fast.round_dir_signed, Fast.round_dir.
assert (Al : fabs (opp l) = fabs l) by exact (Babs_Bopp _ _ l).
rewrite Al.
destruct (gt (fabs l) Fast.err); [| destruct (Bsign h); reflexivity].
(* Bit 63 of [l ^ h] is the xor of the signs of [l] and [h]. *)
rewrite Z.shiftr_lxor, (sign_shiftr l Fl), (sign_shiftr h Fh).
destruct (to_bits_finite h Fh) as (c & Hc & Hb).
destruct (Bsign h) eqn:Bh; cbv beta iota.
- (* [h < 0]: the bits of [h] are [2^63 + c], and [-h] is the pattern
     [c]. For [k = c + !up - sign(-l)], the left side scales the pattern
     [2^63 + k], the negative of the pattern [k] that the right side
     scales, and [Fast.scale] is odd. *)
  destruct (from_bits_finite true c Hc) as (_ & _ & Rh).
  rewrite <- Hb, from_to_bits in Rh. cbv beta iota in Rh.
  destruct (magnitude_bounds c (proj1 Hc)) as ((Hm0 & _) & Hge).
  rewrite Rh, Rabs_Ropp, (Rabs_pos_eq _ Hm0) in Hh.
  (* [1/2 < |h|] keeps [c - 1] nonnegative, and [|h| < 2] keeps the
     biased exponent of [c] below 2046, so [c + 1] is a finite pattern. *)
  assert (Hc0 : c <> 0%Z) by (intros ->; rewrite magnitude_0 in Hh; lra).
  assert (H2 : bpow radix2 1 <= bpow radix2 1023) by (apply bpow_le; lia).
  change (bpow radix2 1) with 2 in H2.
  assert (Hc2 : (c + 1 < 2047 * 2^52)%Z).
  { destruct (Z_lt_le_dec (c / 2^52) 2046) as [Hl|Hl]; [zlia|].
    exfalso.
    assert (H3 : bpow radix2 1023 <= bpow radix2 (c / 2^52 - 1023)) by (apply bpow_le; lia).
    specialize (Hge ltac:(lia)). lra. }
  assert (Oh : opp h = from_bits c).
  { rewrite <- (from_to_bits h), Hb, (proj2 (from_bits_neg c Hc)).
    unfold opp. apply Bopp_involutive. }
  assert (Fol : is_finite (opp l) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fl).
  assert (Sl : Bsign (opp l) = negb (Bsign l))
    by (apply Bsign_Bopp; destruct l; easy).
  rewrite (sign_shiftr (opp l) Fol), Sl, Oh, (FastRoundSubBits.to_from_bits c Hc), Hb,
    Bool.xorb_true_r.
  replace (Z.lxor (Z.b2z (Bsign l)) (Z.b2z true)) with (Z.b2z (negb (Bsign l)))
    by (destruct (Bsign l); reflexivity).
  replace (sign_bit true + c + Z.b2z (negb up) - Z.b2z (negb (Bsign l)))%Z
    with (sign_bit true + (c + Z.b2z (negb up) - Z.b2z (negb (Bsign l))))%Z by ring.
  assert (Hk : (0 <= c + Z.b2z (negb up) - Z.b2z (negb (Bsign l)) < 2047 * 2^52)%Z)
    by (destruct up, (Bsign l); cbn [Z.b2z negb]; lia).
  destruct (from_bits_neg _ Hk) as (Fk & ->).
  rewrite (scale_opp _ e Fk He). reflexivity.
- (* [h > 0]: the sign bit of [h] is clear, and the step is that of
     [Fast.round_dir]. *)
  change (Z.b2z false) with 0%Z. rewrite Bool.xorb_false_r, Z.lxor_0_r. reflexivity.
Qed.

(** The same for [Fast.round_near_signed], which tests [l] with its sign
    bit xored with that of [h] against the gaps of [|h|]. *)
Local Lemma round_near_signed_eq :
  forall h l e,
  is_finite h = true -> is_finite l = true -> / 2 < Rabs (B2R h) < 2 ->
  (-1021 <= e <= 1022)%Z ->
  Fast.round_near_signed h l e =
  if lt h zero then
    match Fast.round_near (opp h) (opp l) e with Some r => Some (opp r) | None => None end
  else Fast.round_near h l e.
Proof.
intros h l e Fh Fl Hh He.
assert (Sh : Bsign h = lt h zero).
{ apply Encoding.Bsign_lt_zero; [exact Fh |]. intros H0. rewrite H0, Rabs_R0 in Hh. lra. }
rewrite <- Sh.
unfold Fast.round_near_signed, Fast.round_near. cbv zeta.
rewrite Encoding.xor_sign_eq.
destruct (Bsign h) eqn:Bh; cbv beta iota.
- (* [h < 0]: [|h|] is [-h], so the tests are those of [Fast.round_near]
     of [-h] and [-l], and [h 2^e] is the negative of [-h 2^e]. *)
  assert (Ah : fabs h = opp h).
  { unfold fabs, opp. destruct h as [s|s| |s m e' Hm]; cbn [Bsign] in Bh;
      try discriminate Bh; subst s; reflexivity. }
  rewrite Ah.
  destruct (_ && _); [cbv beta iota | reflexivity].
  assert (Fo : is_finite (opp h) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fh).
  rewrite <- (scale_opp (opp h) e Fo He).
  unfold opp. rewrite Bopp_involutive. reflexivity.
- (* [h > 0]: [|h|] is [h], and the sign bit of [l] is kept. *)
  assert (Ah : fabs h = h).
  { unfold fabs. destruct h as [s|s| |s m e' Hm]; cbn [Bsign] in Bh; subst; reflexivity. }
  rewrite Ah. reflexivity.
Qed.

(** If [|y - (h + l)| <= 2^-68], with [h] the rounding of [h + l] to
    nearest and [1/2 < |h| < 2], then where [round_dir_signed] returns,
    it returns [y 2^e] rounded toward +inf if [up] and toward -inf
    otherwise. *)
Theorem round_dir_signed_correct :
  forall h l e up v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < Rabs (B2R h) < 2 -> (-1021 <= e <= 1022)%Z ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  Fast.round_dir_signed h l e up = Some v ->
  rounds up (y * bpow radix2 e) v.
Proof.
intros h l e up v y Fh Fl Hrn Hh He Hy Hv.
rewrite (round_dir_signed_eq h l e up Fh Fl Hh He) in Hv.
pose proof (lt_zero_R h Fh) as Hs.
destruct (lt h zero).
- (* [h < 0]: [w] is [-y 2^e] rounded the other way, and [-w] is [y 2^e]
     rounded in the direction [up]. *)
  destruct (Fast.round_dir (opp h) (opp l) e (negb up)) as [w |] eqn:Hw; [| discriminate].
  injection Hv as <-.
  destruct (opp_pair h l y Fh Fl Hrn Hh Hs Hy) as (Fh' & Fl' & Hrn' & Hh' & Hy').
  pose proof (round_dir_correct _ _ e (negb up) w (- y) Fh' Fl' Hrn' Hh' He Hy' Hw) as R.
  unfold rounds in R |- *. apply RoundOpp.pown_rnd_opp.
  replace (- (y * bpow radix2 e)) with (- y * bpow radix2 e) by ring. exact R.
- rewrite Rabs_pos_eq in Hh by exact Hs.
  exact (round_dir_correct h l e up v y Fh Fl Hrn Hh He Hy Hv).
Qed.

(** The same for [round_near_signed] and rounding to nearest. *)
Theorem round_near_signed_correct :
  forall h l e v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < Rabs (B2R h) < 2 -> (-1021 <= e <= 1022)%Z ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  Fast.round_near_signed h l e = Some v ->
  near_round (y * bpow radix2 e) v.
Proof.
intros h l e v y Fh Fl Hrn Hh He Hy Hv.
rewrite (round_near_signed_eq h l e Fh Fl Hh He) in Hv.
pose proof (lt_zero_R h Fh) as Hs.
destruct (lt h zero).
- (* [h < 0]: [w] is [-y 2^e] rounded to nearest, and [-w] is [y 2^e]
     rounded to nearest. *)
  destruct (Fast.round_near (opp h) (opp l) e) as [w |] eqn:Hw; [| discriminate].
  injection Hv as <-.
  destruct (opp_pair h l y Fh Fl Hrn Hh Hs Hy) as (Fh' & Fl' & Hrn' & Hh' & Hy').
  pose proof (round_near_correct _ _ e w (- y) Fh' Fl' Hrn' Hh' He Hy' Hw) as R.
  apply NearCells.near_opp in R.
  replace (- (- y * bpow radix2 e)) with (y * bpow radix2 e) in R by ring. exact R.
- rewrite Rabs_pos_eq in Hh by exact Hs.
  exact (round_near_correct h l e v y Fh Fl Hrn Hh He Hy Hv).
Qed.

(** The same for [Fast.round_dir_signed_branch], which branches on
    [h < 0] and rounds [-y 2^e] from [-h] and [-l] there. *)
Theorem round_dir_signed_branch_correct :
  forall h l e up v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < Rabs (B2R h) < 2 -> (-1021 <= e <= 1022)%Z ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  Fast.round_dir_signed_branch h l e up = Some v ->
  rounds up (y * bpow radix2 e) v.
Proof.
intros h l e up v y Fh Fl Hrn Hh He Hy Hv.
unfold Fast.round_dir_signed_branch in Hv.
pose proof (lt_zero_R h Fh) as Hs.
destruct (lt h zero).
- (* [h < 0]: [w] is [-y 2^e] rounded the other way, and [-w] is [y 2^e]
     rounded in the direction [up]. *)
  destruct (Fast.round_dir (opp h) (opp l) e (negb up)) as [w |] eqn:Hw; [| discriminate].
  injection Hv as <-.
  destruct (opp_pair h l y Fh Fl Hrn Hh Hs Hy) as (Fh' & Fl' & Hrn' & Hh' & Hy').
  pose proof (round_dir_correct _ _ e (negb up) w (- y) Fh' Fl' Hrn' Hh' He Hy' Hw) as R.
  unfold rounds in R |- *. apply RoundOpp.pown_rnd_opp.
  replace (- (y * bpow radix2 e)) with (- y * bpow radix2 e) by ring. exact R.
- rewrite Rabs_pos_eq in Hh by exact Hs.
  exact (round_dir_correct h l e up v y Fh Fl Hrn Hh He Hy Hv).
Qed.

(** The same for [Fast.round_near_signed_branch] and rounding to nearest. *)
Theorem round_near_signed_branch_correct :
  forall h l e v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < Rabs (B2R h) < 2 -> (-1021 <= e <= 1022)%Z ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  Fast.round_near_signed_branch h l e = Some v ->
  near_round (y * bpow radix2 e) v.
Proof.
intros h l e v y Fh Fl Hrn Hh He Hy Hv.
unfold Fast.round_near_signed_branch in Hv.
pose proof (lt_zero_R h Fh) as Hs.
destruct (lt h zero).
- (* [h < 0]: [w] is [-y 2^e] rounded to nearest, and [-w] is [y 2^e]
     rounded to nearest. *)
  destruct (Fast.round_near (opp h) (opp l) e) as [w |] eqn:Hw; [| discriminate].
  injection Hv as <-.
  destruct (opp_pair h l y Fh Fl Hrn Hh Hs Hy) as (Fh' & Fl' & Hrn' & Hh' & Hy').
  pose proof (round_near_correct _ _ e w (- y) Fh' Fl' Hrn' Hh' He Hy' Hw) as R.
  apply NearCells.near_opp in R.
  replace (- (- y * bpow radix2 e)) with (y * bpow radix2 e) in R by ring. exact R.
- rewrite Rabs_pos_eq in Hh by exact Hs.
  exact (round_near_correct h l e v y Fh Fl Hrn Hh He Hy Hv).
Qed.
