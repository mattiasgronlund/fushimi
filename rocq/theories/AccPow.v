(** The accurate phase of x^y ([src/dyadic/pow/acc.rs]), which
    [DyadicPow.pow_dir_with] and [DyadicPow.pow_near_with] try before
    [ziv] at a [y] that is not an integer of [i32]: [acc_pow_correct]
    bounds x^y by [lo 2^e] and [hi 2^e] from the bounds on [y ln x] of
    [AccPowLn.acc_t_correct] and those on [e^t] of
    [AccPowExp.acc_exp_correct], and [acc_pow_dir_correct] and
    [acc_pow_near_correct] show that where both bounds, made [Dyadic<2>]s
    exactly, round to the same [f64], that [f64] is the rounding of x^y,
    as in the rounding test of [ziv] ([DyDriver.round_between]). *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr MpfrRound Limbs Elementary DyRound DyConv DyDriver NearF64
  DyConvNear DyDriverNear AccPowLn AccPowExp.
From Inari Require Encoding.

Open Scope R_scope.

Theorem acc_pow_correct :
  forall x y lo hi e,
  is_finite x = true -> 0 < B2R x -> is_finite y = true -> B2R y <> 0 ->
  DyadicPow.acc_pow x y = Some (lo, hi, e) ->
  (2 ^ 126 <= lo < 2 ^ 128)%Z /\ (0 <= hi < 2 ^ 128)%Z /\ (Z.abs e < 2 ^ 20)%Z /\
  IZR lo * bpow radix2 e <= Rpower (B2R x) (B2R y) <= IZR hi * bpow radix2 e.
Proof.
intros x y lo hi e Fx Px Fy Y0 A.
unfold DyadicPow.acc_pow in A.
destruct (DyadicPow.acc_t x y) as [[tl th]|] eqn:T; [| discriminate A].
cbv beta iota in A.
(* [x^y = e^t] at [t = y ln x], which [acc_t] bounds. *)
pose proof (acc_t_correct x y tl th Fx Px Fy Y0 T) as Ht.
unfold Rpower. exact (acc_exp_correct tl th lo hi e _ A Ht).
Qed.

(** The two limbs [[m mod 2^64, m >> 64]] of a [u128] [m] stand for [m],
    and [Dyadic.round] at 2 limbs of them and an exponent [e] with
    [|e| < 2^20], without a sticky bit, is [dround 2 up (m 2^e)]. *)
Lemma acc_round_correct :
  forall m e up,
  (0 <= m < 2 ^ 128)%Z -> (Z.abs e < 2 ^ 20)%Z ->
  exists d,
  Dyadic.round 2 false (m mod 2 ^ 64 :: Z.shiftr m 64 :: nil) e false up = Some d /\
  dy_ok 2 d /\ Dyadic.dy_R d = dround 2 up (IZR m * bpow radix2 e).
Proof.
intros m e up Hm He.
assert (L2 : level_ok 2) by (unfold level_ok; lia).
rewrite Z.shiftr_div_pow2 by lia.
assert (Hlo : (0 <= m mod 2 ^ 64 < 2 ^ 64)%Z) by (apply Z.mod_pos_bound; lia).
assert (Hhi : (0 <= m / 2 ^ 64 < 2 ^ 64)%Z).
{ split; [apply Z.div_pos; lia |].
  apply Z.div_lt_upper_bound; [lia |]. rewrite <- Z.pow_add_r by lia. exact (proj2 Hm). }
set (x := (m mod 2 ^ 64)%Z :: (m / 2 ^ 64)%Z :: nil).
assert (Hx : limbs_ok x) by (unfold limbs_ok, x; repeat constructor; lia).
assert (Hv : Limbs.val x = m).
{ unfold x. cbn [Limbs.val]. pose proof (Z.div_mod m (2 ^ 64) ltac:(lia)). lia. }
(* The exponent [e + bits(m) - 128] of the result is far from the ends of [i64]. *)
assert (He' : (Limbs.val x = 0 \/
               - 2 ^ 63 <= e + nat_bits (Limbs.val x) - dprec 2 < 2 ^ 63 - 1)%Z).
{ rewrite Hv. unfold nat_bits. change (dprec 2) with 128%Z.
  destruct (Z.eqb_spec m 0) as [H0 | H0]; [left; exact H0 | right].
  assert (Hl : (Z.log2 m < 128)%Z) by (apply Z.log2_lt_pow2; lia).
  pose proof (Z.log2_nonneg m). lia. }
destruct (round_correct 2 false _ e false up 0 L2 Hx eq_refl He') as (d & Ed & Hd & Rd).
exists d. split; [exact Ed |]. split; [exact Hd |].
rewrite Rd, Hv, Rplus_0_r. reflexivity.
Qed.

(** Where [acc_bounds] gives two [Dyadic<2>]s, they bound x^y: the bound
    below is [lo 2^e] rounded down, and the one above is [hi 2^e]
    rounded up. *)
Lemma acc_bounds_correct :
  forall x y l h,
  is_finite x = true -> 0 < B2R x -> is_finite y = true -> B2R y <> 0 ->
  DyadicPow.acc_bounds x y = Some (Some (l, h)) ->
  dy_ok 2 l /\ dy_ok 2 h /\
  Dyadic.dy_R l <= Rpower (B2R x) (B2R y) <= Dyadic.dy_R h.
Proof.
intros x y l h Fx Px Fy Y0 B.
assert (L2 : level_ok 2) by (unfold level_ok; lia).
unfold DyadicPow.acc_bounds in B.
destruct (DyadicPow.acc_pow x y) as [[[lo hi] e]|] eqn:P; cbv beta iota in B;
  [| discriminate B].
destruct (acc_pow_correct x y lo hi e Fx Px Fy Y0 P) as (Hlo & Hhi & He & Hb).
destruct (acc_round_correct lo e false ltac:(lia) He) as (dl & El & Hl & Rl).
destruct (acc_round_correct hi e true Hhi He) as (dh & Eh & Hh & Rh).
rewrite El, Eh in B. cbv beta iota in B. injection B as <- <-.
split; [exact Hl |]. split; [exact Hh |].
pose proof (dround_bounds 2 (IZR lo * bpow radix2 e) L2) as Bl.
pose proof (dround_bounds 2 (IZR hi * bpow radix2 e) L2) as Bh.
rewrite Rl, Rh. lra.
Qed.

Theorem acc_pow_dir_correct :
  forall x y (up : bool) v,
  is_finite x = true -> 0 < B2R x -> is_finite y = true -> B2R y <> 0 ->
  DyadicPow.acc_pow_dir x y up = Some (Some v) ->
  rounds up (Rpower (B2R x) (B2R y)) v.
Proof.
intros x y up v Fx Px Fy Y0 A.
assert (L2 : level_ok 2) by (unfold level_ok; lia).
unfold DyadicPow.acc_pow_dir in A.
destruct (DyadicPow.acc_bounds x y) as [[[l h]|]|] eqn:B; cbv beta iota in A;
  [| discriminate A | discriminate A].
destruct (acc_bounds_correct x y l h Fx Px Fy Y0 B) as (Hl & Hh & Hb).
destruct (to_f64_correct 2 l up L2 Hl) as (a & Ea & Ra).
destruct (to_f64_correct 2 h up L2 Hh) as (b & Eb & Rb).
rewrite Ea, Eb in A. cbv beta iota in A.
(* Both bounds round to [a], so x^y between them does too. *)
destruct (Model.eq a b) eqn:Q; cbv beta iota in A; [| discriminate A].
injection A as <-.
exact (round_between _ _ _ _ _ _ Hb Ra Rb Q).
Qed.

Theorem acc_pow_near_correct :
  forall x y v,
  is_finite x = true -> 0 < B2R x -> is_finite y = true -> B2R y <> 0 ->
  DyadicPow.acc_pow_near x y = Some (Some v) ->
  near_round (Rpower (B2R x) (B2R y)) v.
Proof.
intros x y v Fx Px Fy Y0 A.
assert (L2 : level_ok 2) by (unfold level_ok; lia).
unfold DyadicPow.acc_pow_near in A.
destruct (DyadicPow.acc_bounds x y) as [[[l h]|]|] eqn:B; cbv beta iota in A;
  [| discriminate A | discriminate A].
destruct (acc_bounds_correct x y l h Fx Px Fy Y0 B) as (Hl & Hh & Hb).
destruct (to_f64_near_correct 2 l L2 Hl) as (a & Ea & Ra & _).
destruct (to_f64_near_correct 2 h L2 Hh) as (b & Eb & Rb & _).
rewrite Ea, Eb in A. cbv beta iota in A.
(* Both bounds round to the same bits, so to the same [f64], and x^y
   between them rounds to it ([DyDriverNear.ziv_near_levels_correct]). *)
destruct (Z.eqb_spec (to_bits a) (to_bits b)) as [Q |]; cbv beta iota in A;
  [| discriminate A].
injection A as <-.
assert (a = b) as <-.
{ rewrite <- (Encoding.from_to_bits a), <- (Encoding.from_to_bits b), Q. reflexivity. }
exact (near_between _ _ _ _ Hb Ra Rb).
Qed.
