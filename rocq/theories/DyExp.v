(** * e^x, 2^x and 10^x in the dyadic kernel

    [exp_dir], [exp2_dir] and [exp10_dir] of [DyadicExp] in [Model.v]
    apply the rules of [DyExpRules.v], and [exp2_int_rule] for [exp2] at
    the integers from -1022 to 1023, where one applies, and otherwise
    the driver [ziv] to the enclosures of [ev_exp_correct] and the others.
    [exp_dir_post] and the others prove, for any driver [z] in place of
    [ziv] ([exp_dir_with z] and the others) and any property [post] that
    holds of every correct rounding ([rounds_post]) and that [z] gives
    ([driver_post] of [DyDriver.v]), that the result has [post] for [exp],
    [Rexp2] and [Rexp10] of a finite [x] and the direction [up]. So with
    [ziv_strict] the kernel rounds correctly where it returns
    ([exp_dir_correct] and the others, by [ziv_strict_correct]), the Rust
    returns the same value there ([exp_dir_strict] and the others), and
    wherever the Rust returns, its result is on the side of [up]
    ([exp_dir_side] and the others, by [ziv_side]). The reductions write
    [e^x = 2^k e^-y] for [y = k ln 2 - x], with the enclosures of ln 2 and
    ln 10 of [DyConst.v] and of [e^-y] of [DyExpCore.v]. That a rounding
    test passes by the cap is not proved. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Fushimi Require Import Model Mpfr Limbs Elementary DyRound DyConv DyOps DyDriver DyGrow
  DyConst DyExpCore DyExpRules FastExp.

Open Scope Z_scope.

(** Where [ziv_strict] returns, [Dyadic.ziv] returns the same: the goal
    [<body with ziv_strict> = Some v -> <body with Dyadic.ziv> = Some v]
    of a function of this file, split at its guards, which name neither
    driver. A branch that calls no driver is the same on both sides, and
    one that calls it is closed by [ziv_strict_ziv], in either branch of
    an [if], as in [exp_dir_with], where the call is in a [then]. *)
Local Ltac dir_strict :=
  repeat match goal with
  | |- (if ?c then _ else _) = Some _ -> _ => destruct c
  | |- match ?c with Some _ => _ | None => _ end = Some _ -> _ => destruct c
  end;
  first [exact (fun h => h) | apply ziv_strict_ziv].

(** ** Helpers *)

(** The [f64] literals [1.0], [2.0] and [-2.0]. *)
Lemma one_B2R : is_finite DyadicExp.one = true /\ B2R DyadicExp.one = 1%R.
Proof.
split; [vm_compute; reflexivity|].
rewrite <- SF2R_B2SF.
replace (B2SF DyadicExp.one) with (SpecFloat.S754_finite false 4503599627370496 (-52))
  by (vm_compute; reflexivity).
unfold SF2R, F2R. cbn [Fnum Fexp SpecFloat.cond_Zopp].
change (bpow radix2 (-52)) with (/ 4503599627370496)%R.
lra.
Qed.

Lemma two_B2R : is_finite DyadicExp.two = true /\ B2R DyadicExp.two = 2%R.
Proof.
split; [vm_compute; reflexivity|].
rewrite <- SF2R_B2SF.
replace (B2SF DyadicExp.two) with (SpecFloat.S754_finite false 4503599627370496 (-51))
  by (vm_compute; reflexivity).
unfold SF2R, F2R. cbn [Fnum Fexp SpecFloat.cond_Zopp].
change (bpow radix2 (-51)) with (/ 2251799813685248)%R.
lra.
Qed.

Lemma m_two_B2R : is_finite DyadicExp.m_two = true /\ B2R DyadicExp.m_two = (-2)%R.
Proof.
split; [vm_compute; reflexivity|].
rewrite <- SF2R_B2SF.
replace (B2SF DyadicExp.m_two) with (SpecFloat.S754_finite true 4503599627370496 (-51))
  by (vm_compute; reflexivity).
unfold SF2R, F2R. cbn [Fnum Fexp SpecFloat.cond_Zopp].
change (bpow radix2 (-51)) with (/ 2251799813685248)%R.
rewrite opp_IZR. lra.
Qed.

(** A finite [x] is not NaN and is neither infinity. *)
Lemma fin_not_nan : forall x : f64, is_finite x = true -> is_nan x = false.
Proof.
now intros [s|s| |s m e H].
Qed.

Lemma fin_neq_inf : forall x : f64, is_finite x = true -> eq x infinity = false.
Proof.
intros x F.
replace infinity with (B754_infinity false : f64) by (now apply B2SF_inj).
destruct x as [s|s| |s m e H]; try discriminate F; destruct s; reflexivity.
Qed.

Lemma fin_neq_ninf : forall x : f64, is_finite x = true -> eq x DyadicExp.neg_infinity = false.
Proof.
intros x F.
replace DyadicExp.neg_infinity with (B754_infinity true : f64) by (now apply B2SF_inj).
destruct x as [s|s| |s m e H]; try discriminate F; destruct s; reflexivity.
Qed.

(** [x < 0.0] for any [x]: the infinities and NaN have the value 0. *)
Lemma lt_zero_spec :
  forall x : f64,
  (lt x zero = true -> B2R x <= 0)%R /\ (lt x zero = false -> 0 <= B2R x)%R.
Proof.
intros x. destruct (is_finite x) eqn:F.
- unfold lt. rewrite Bltb_correct; [|exact F|reflexivity].
  change (B2R zero) with 0%R.
  destruct (Rlt_bool_spec (B2R x) 0); split; intros Hb; (discriminate Hb || lra).
- destruct x as [s|s| |s m e H]; try discriminate F; cbn [B2R]; split; intros; lra.
Qed.

(** If [x < hi && x > lo] and [x >= hi] are false for a finite [x], then
    [x <= lo]: the last branch of [exp_dir_with] and [exp10_dir_with], and
    of their [_near_with]. *)
Lemma range_low :
  forall x hi lo, is_finite x = true -> is_finite hi = true -> is_finite lo = true ->
  (lt x hi && gt x lo) = false -> ge x hi = false -> le x lo = true.
Proof.
intros x hi lo Fx Fh Fl G G1.
unfold ge in G1. rewrite Bleb_correct in G1 by assumption.
unfold lt, gt in G. rewrite !Bltb_correct in G by assumption.
unfold le. rewrite Bleb_correct by assumption. apply Rle_bool_true.
destruct (Rle_bool_spec (B2R hi) (B2R x)) as [_|A]; [discriminate G1|].
destruct (Rlt_bool_spec (B2R x) (B2R hi)) as [_|C]; [cbn [andb] in G|lra].
destruct (Rlt_bool_spec (B2R lo) (B2R x)) as [_|B]; [discriminate G | exact B].
Qed.

(** If [lo <= x && x < hi] and [x >= hi] are false for a finite [x], then
    [x < lo]: the last branch of [exp2_dir_with] and [exp2_near_with]. *)
Lemma range_low_ge :
  forall x hi lo, is_finite x = true -> is_finite hi = true -> is_finite lo = true ->
  (le lo x && lt x hi) = false -> ge x hi = false -> lt x lo = true.
Proof.
intros x hi lo Fx Fh Fl G G1.
unfold ge in G1. rewrite Bleb_correct in G1 by assumption.
unfold le, lt in G. rewrite Bleb_correct, Bltb_correct in G by assumption.
unfold lt. rewrite Bltb_correct by assumption. apply Rlt_bool_true.
destruct (Rle_bool_spec (B2R hi) (B2R x)) as [_|A]; [discriminate G1|].
destruct (Rlt_bool_spec (B2R x) (B2R hi)) as [_|C]; [|lra].
destruct (Rle_bool_spec (B2R lo) (B2R x)) as [_|B]; [discriminate G | exact B].
Qed.

(** [x.ceil()] is the integer above [x]. *)
Lemma fceil_IZR : forall a, B2R (fceil a) = IZR (Zceil (B2R a)).
Proof.
intros a. unfold fceil. rewrite (proj1 (Bnearbyint_correct 53 1024 _ mode_UP a)).
unfold round, F2R, scaled_mantissa, cexp, FIX_exp.
cbn [Fnum Fexp bpow Z.opp round_mode]. now rewrite !Rmult_1_r.
Qed.

(** [to_k] returns a [k] with [|k| <= 2048], and an integer [c] itself. *)
Lemma to_k_bound :
  forall c k, DyadicExp.to_k c = Some k -> - 2048 <= k <= 2048 /\ k = DyadicExp.to_i64 c.
Proof.
intros c k H. unfold DyadicExp.to_k in H.
destruct (Z.abs (DyadicExp.to_i64 c) <=? 2048) eqn:B; [|discriminate H].
injection H as <-. apply Z.leb_le in B. split; [lia | reflexivity].
Qed.

Lemma to_k_int :
  forall c k z,
  is_finite c = true -> B2R c = IZR z -> DyadicExp.to_k c = Some k -> B2R c = IZR k.
Proof.
intros c k z Fc Hz H.
destruct (to_k_bound c k H) as (Hk & ->).
assert (T : Btrunc c = z).
{ apply eq_IZR. rewrite Btrunc_correct, Hz by reflexivity.
  unfold round, F2R, scaled_mantissa, cexp, FIX_exp.
  cbn [Fnum Fexp bpow Z.opp]. rewrite !Rmult_1_r. now rewrite Ztrunc_IZR. }
assert (M : DyadicExp.to_i64 c = Z.max (- 2 ^ 63) (Z.min (2 ^ 63 - 1) (Btrunc c)))
  by (destruct c; try discriminate Fc; reflexivity).
rewrite M in Hk |- *. rewrite T in Hk |- *. rewrite Hz. f_equal. lia.
Qed.

(** The enclosure [[h, h]] of a dyadic number. *)
Lemma hh_correct :
  forall n h E,
  dy_ok n h -> - E <= Dyadic.dy_exp h <= E ->
  encl_ok n {| Dyadic.en_lo := h; Dyadic.en_hi := h |} /\
  encl_le E {| Dyadic.en_lo := h; Dyadic.en_hi := h |} /\
  encl_has {| Dyadic.en_lo := h; Dyadic.en_hi := h |} (Dyadic.dy_R h).
Proof.
intros n h E Hh HE. unfold encl_ok, encl_le, encl_has; cbn [Dyadic.en_lo Dyadic.en_hi].
split; [split; [exact Hh | split; [exact Hh | apply Rle_refl]] |].
split; [split; exact HE | split; apply Rle_refl].
Qed.

(** [mul_int a k] holds [x k] for every [x] of [a]. *)
Lemma mul_int_step :
  forall n a k c E,
  level_ok n -> encl_ok n a -> encl_le E a -> 0 <= E <= 2 ^ 60 -> - 2048 <= k <= 2048 ->
  DyadicExp.mul_int n a k = Some c ->
  encl_ok n c /\ encl_le (E + 2 ^ 13) c /\
  forall x, encl_has a x -> encl_has c (x * IZR k).
Proof.
intros n a k c E Hn Ha HE HE0 Hk H. unfold DyadicExp.mul_int in H.
destruct (Dyadic.encl_mul_u64 n a (Z.abs k)) as [p|] eqn:Hp; [|discriminate H].
injection H as <-.
assert (Hk' : 0 <= Z.abs k < 2 ^ 64) by lia.
destruct (mul_u64_step n a (Z.abs k) p E Hn Ha HE HE0 Hk' Hp) as (Op & Lp & Hp').
destruct (k <? 0) eqn:Hk0.
- apply Z.ltb_lt in Hk0.
  destruct (neg_step n p (E + 2 ^ 13) Hn Op Lp) as (On & Ln & Hn').
  split; [exact On|]. split; [exact Ln|].
  intros x Hx. replace (x * IZR k)%R with (- (x * IZR (Z.abs k)))%R.
  + exact (Hn' _ (Hp' x Hx)).
  + rewrite Z.abs_neq by lia. rewrite opp_IZR. ring.
- apply Z.ltb_ge in Hk0.
  split; [exact Op|]. split; [exact Lp|].
  intros x Hx. rewrite <- (Z.abs_eq k) by lia. exact (Hp' x Hx).
Qed.

(** [mul_f64 a x] holds [x v] for every [v] of [a]. *)
Lemma mul_f64_step :
  forall n a x c E,
  level_ok n -> encl_ok n a -> encl_le E a -> 0 <= E <= 2 ^ 59 ->
  DyadicExp.mul_f64 n a x = Some c ->
  encl_ok n c /\ encl_le (E + 2 ^ 14) c /\
  forall v, encl_has a v -> encl_has c (B2R x * v).
Proof.
intros n a x c E Hn Ha HE HE0 H. unfold DyadicExp.mul_f64 in H.
destruct (Dyadic.encl_point n (fabs x)) as [px|] eqn:Hpx; [|discriminate H].
destruct (Dyadic.encl_mul n px a) as [p|] eqn:Hp; [|discriminate H].
injection H as <-.
destruct (point_has n (fabs x) px Hn Hpx) as (Opx & Lpx & Hpx').
destruct (mul_step n px a p (2 ^ 13) E Hn Opx Ha Lpx HE ltac:(lia) ltac:(lia) Hp)
  as (Op & Lp & Hp').
rewrite B2R_Babs in Hpx'.
assert (Lp' : encl_le (E + 2 ^ 14) p) by (apply (encl_le_mono (2 ^ 13 + E + 2 ^ 13)); [lia | exact Lp]).
destruct (lt_zero_spec x) as (Hneg & Hpos).
destruct (lt x zero) eqn:L.
- destruct (neg_step n p (E + 2 ^ 14) Hn Op Lp') as (On & Ln & Hn').
  split; [exact On|]. split; [exact Ln|].
  intros v Hv. specialize (Hneg eq_refl).
  replace (B2R x * v)%R with (- (Rabs (B2R x) * v))%R.
  + exact (Hn' _ (Hp' _ _ Hpx' Hv)).
  + rewrite Rabs_left1 by exact Hneg. ring.
- split; [exact Op|]. split; [exact Lp'|].
  intros v Hv. specialize (Hpos eq_refl).
  rewrite <- (Rabs_pos_eq (B2R x)) by exact Hpos. exact (Hp' _ _ Hpx' Hv).
Qed.

(** ** [scaled] *)

(** The end of [scaled], from the check of [y] on. *)
Lemma scaled_tail :
  forall n y k c E yv,
  level_ok n -> encl_ok n y -> encl_le E y -> 0 <= E <= 2 ^ 29 + 2 ^ 20 -> encl_has y yv ->
  - 2 ^ 20 <= k <= 2 ^ 20 ->
  (let* two_d := Dyadic.from_f64 n DyadicExp.two in
   if DyadicExp.dy_lt n (Dyadic.en_lo y) (Dyadic.dy_zero n)
      || DyadicExp.dy_gt n (Dyadic.en_hi y) two_d then None else
   let* e := DyadicExp.exp_neg n y in
   Dyadic.encl_shl n e k) = Some c ->
  encl_ok n c /\ encl_le (2 ^ 25 * (E + 2 ^ 16) + 2 ^ 20) c /\
  encl_has c (bpow radix2 k * exp (- yv)).
Proof.
intros n y k c E yv Hn Hy HE HE0 Hyv Hk H.
destruct (Dyadic.from_f64 n DyadicExp.two) as [two_d|] eqn:Et; [|discriminate H].
cbv beta iota in H.
destruct (DyadicExp.dy_lt n (Dyadic.en_lo y) (Dyadic.dy_zero n)) eqn:L1;
  cbn [orb] in H; [discriminate H|].
destruct (DyadicExp.dy_gt n (Dyadic.en_hi y) two_d) eqn:L2; cbn [orb] in H; [discriminate H|].
destruct (DyadicExp.exp_neg n y) as [e|] eqn:Ee; [|discriminate H].
destruct (from_f64_step n DyadicExp.two two_d Hn Et) as (Ot & _ & Vt & _).
rewrite (proj2 two_B2R) in Vt.
destruct Hy as (Olo & Ohi & Hle).
destruct (dy_zero_ok n) as (Oz & Vz & _).
(* The check: [0 <= lo] and [hi <= 2], so that [0 <= yv <= 2]. *)
assert (Hlo : (0 <= Dyadic.dy_R (Dyadic.en_lo y))%R).
{ unfold DyadicExp.dy_lt in L1. rewrite (cmp_correct n _ _ Hn Olo Oz), Vz in L1.
  destruct (Rcompare_spec (Dyadic.dy_R (Dyadic.en_lo y)) 0); [discriminate L1 | lra | lra]. }
assert (Hhi : (Dyadic.dy_R (Dyadic.en_hi y) <= 2)%R).
{ unfold DyadicExp.dy_gt in L2. rewrite (cmp_correct n _ _ Hn Ohi Ot), Vt in L2.
  destruct (Rcompare_spec (Dyadic.dy_R (Dyadic.en_hi y)) 2); [lra | lra | discriminate L2]. }
unfold encl_has in Hyv.
destruct (exp_neg_correct n y e E yv Hn (conj Olo (conj Ohi Hle)) HE HE0 Hyv ltac:(lra) Ee)
  as (Oe & Le & He).
destruct (shl_step n e k c _ Hn Oe Le ltac:(lia) Hk H) as (Oc & Lc & Hc).
split; [exact Oc|].
split; [apply (encl_le_mono (2 ^ 25 * (E + 2 ^ 16) + Z.abs k)); [lia | exact Lc]|].
rewrite Rmult_comm. exact (Hc _ He).
Qed.

(** The bound of the exponents of the result is linear in the bound [E]
    of those of [y] ([scaled_gen]): [y + ln 2] adds at most [2^15] to it,
    then [exp_neg_correct] and the shift by [k] give
    [2^25 (E + 2^15 + 2^16) + 2^20]. [scaled_correct] is its bound for
    [E <= 2^20]. *)
Lemma scaled_gen :
  forall n y k h l c E yv,
  level_ok n -> encl_ok n y -> encl_le E y -> 0 <= E <= 2 ^ 29 + 2 ^ 19 ->
  dy_ok n h -> - 2 ^ 14 <= Dyadic.dy_exp h <= 2 ^ 14 ->
  encl_ok n l -> encl_le (2 ^ 14) l -> encl_has l (ln 2 - Dyadic.dy_R h) ->
  - 2 ^ 14 <= k <= 2 ^ 14 -> encl_has y yv ->
  DyadicExp.scaled n y k h l = Some c ->
  encl_ok n c /\ encl_le (2 ^ 25 * (E + 2 ^ 17) + 2 ^ 20) c /\
  encl_has c (bpow radix2 k * exp (- yv)).
Proof.
intros n y k h l c E yv Hn Hy HEy HE Hh Heh Hl HEl Hhl Hk Hyv H.
unfold DyadicExp.scaled in H.
destruct (DyadicExp.dy_lt n (Dyadic.en_lo y) (Dyadic.dy_zero n)) eqn:Lt0.
- (* [y < 0]: [y + ln 2] and [k + 1], with [2^(k+1) e^-(y + ln 2) = 2^k e^-y]. *)
  destruct (Dyadic.encl_add n y {| Dyadic.en_lo := h; Dyadic.en_hi := h |}) as [y1|] eqn:E1;
    [|discriminate H].
  destruct (Dyadic.encl_add n y1 l) as [y2|] eqn:E2; [|discriminate H].
  cbv beta iota in H.
  destruct (hh_correct n h (2 ^ 14) Hh Heh) as (Ohh & Lhh & Hhh).
  destruct (add_step n y _ y1 E _ Hn Hy Ohh HEy Lhh ltac:(lia) ltac:(lia) E1)
    as (O1 & L1 & H1).
  destruct (add_step n y1 l y2 _ _ Hn O1 Hl L1 HEl ltac:(lia) ltac:(lia) E2)
    as (O2 & L2 & H2).
  specialize (H2 _ _ (H1 _ _ Hyv Hhh) Hhl).
  replace (yv + Dyadic.dy_R h + (ln 2 - Dyadic.dy_R h))%R with (yv + ln 2)%R in H2 by ring.
  destruct (scaled_tail n y2 (k + 1) c _ _ Hn O2 L2 ltac:(lia) H2 ltac:(lia) H)
    as (Oc & Lc & Hc).
  split; [exact Oc|].
  split; [eapply encl_le_mono; [| exact Lc]; lia|].
  replace (bpow radix2 k * exp (- yv))%R
    with (bpow radix2 (k + 1) * exp (- (yv + ln 2)))%R; [exact Hc|].
  rewrite bpow_plus, Ropp_plus_distr, exp_plus, (exp_Ropp (ln 2)), exp_ln by lra.
  change (bpow radix2 1) with 2%R. field.
- destruct (scaled_tail n y k c E yv Hn Hy HEy ltac:(lia) Hyv ltac:(lia) H) as (Oc & Lc & Hc).
  split; [exact Oc|].
  split; [apply (encl_le_mono (2 ^ 25 * (E + 2 ^ 16) + 2 ^ 20)); [lia | exact Lc]|].
  exact Hc.
Qed.

Lemma scaled_correct :
  forall n y k h l c E yv,
  level_ok n -> encl_ok n y -> encl_le E y -> 0 <= E <= 2 ^ 20 ->
  dy_ok n h -> - 2 ^ 14 <= Dyadic.dy_exp h <= 2 ^ 14 ->
  encl_ok n l -> encl_le (2 ^ 14) l -> encl_has l (ln 2 - Dyadic.dy_R h) ->
  - 2 ^ 14 <= k <= 2 ^ 14 -> encl_has y yv ->
  DyadicExp.scaled n y k h l = Some c ->
  encl_ok n c /\ encl_le (2 ^ 48) c /\ encl_has c (bpow radix2 k * exp (- yv)).
Proof.
intros n y k h l c E yv Hn Hy HEy HE Hh Heh Hl HEl Hhl Hk Hyv H.
destruct (scaled_gen n y k h l c E yv Hn Hy HEy ltac:(lia) Hh Heh Hl HEl Hhl Hk Hyv H)
  as (Oc & Lc & Hc).
split; [exact Oc|]. split; [| exact Hc].
apply (encl_le_mono (2 ^ 25 * (E + 2 ^ 17) + 2 ^ 20)); [lia | exact Lc].
Qed.

(** ** [exp_encl] and the [Eval]s *)

Lemma exp_encl_correct :
  forall n x c,
  level_ok n -> DyadicExp.exp_encl n x = Some c ->
  encl_ok n c /\ encl_le (2 ^ 48) c /\ encl_has c (exp (B2R x)).
Proof.
intros n x c Hn H. unfold DyadicExp.exp_encl in H.
destruct (DyadicExp.to_k (fceil (mul x DyadicExp.log2_e))) as [k|] eqn:Ek; [|discriminate H].
destruct (DyadicConsts.ln2 n) as [[h l]|] eqn:El; [|discriminate H].
destruct (DyadicExp.mul_int n {| Dyadic.en_lo := h; Dyadic.en_hi := h |} k) as [a|] eqn:Ea;
  [|discriminate H].
destruct (Dyadic.encl_point n x) as [px|] eqn:Ep; [|discriminate H].
destruct (Dyadic.encl_sub n a px) as [b|] eqn:Eb; [|discriminate H].
destruct (DyadicExp.mul_int n l k) as [c'|] eqn:Ec; [|discriminate H].
destruct (Dyadic.encl_add n b c') as [y|] eqn:Ey; [|discriminate H].
cbv beta iota in H.
destruct (to_k_bound _ _ Ek) as (Hk & _).
destruct (ln2_correct n h l Hn El) as (Hh & Heh & Hl & HEl & Hhl).
destruct (hh_correct n h (2 ^ 13) Hh Heh) as (Ohh & Lhh & Hhh).
destruct (mul_int_step n _ k a _ Hn Ohh Lhh ltac:(lia) Hk Ea) as (Oa & La & Ha).
destruct (point_has n x px Hn Ep) as (Op & Lp & Hp).
destruct (sub_step n a px b _ _ Hn Oa Op La Lp ltac:(lia) ltac:(lia) Eb) as (Ob & Lb & Hb).
destruct (mul_int_step n l k c' _ Hn Hl HEl ltac:(lia) Hk Ec) as (Oc & Lc & Hc).
destruct (add_step n b c' y _ _ Hn Ob Oc Lb Lc ltac:(lia) ltac:(lia) Ey) as (Oy & Ly & Hy).
(* [y] holds [k ln 2 - x]. *)
specialize (Hy _ _ (Hb _ _ (Ha _ Hhh) Hp) (Hc _ Hhl)).
replace (Dyadic.dy_R h * IZR k - B2R x + (ln 2 - Dyadic.dy_R h) * IZR k)%R
  with (IZR k * ln 2 - B2R x)%R in Hy by ring.
destruct (scaled_correct n y k h l c _ _ Hn Oy Ly ltac:(lia) Hh ltac:(lia) Hl HEl Hhl ltac:(lia)
  Hy H) as (Oc' & Lc' & Hc').
split; [exact Oc'|]. split; [exact Lc'|].
rewrite bpow_exp2, <- exp_plus in Hc'.
replace (IZR k * ln 2 + - (IZR k * ln 2 - B2R x))%R with (B2R x) in Hc' by ring.
exact Hc'.
Qed.

Lemma ev_exp_correct :
  forall x n a,
  level_ok n -> DyadicExp.ev_exp x n = Some a -> encl_ok n a /\ encl_has a (exp (B2R x)).
Proof.
intros x n a Hn H. unfold DyadicExp.ev_exp in H.
destruct (exp_encl_correct n x a Hn H) as (O & _ & Ha). split; assumption.
Qed.

Lemma ev_exp2_correct :
  forall x n a,
  level_ok n -> DyadicExp.ev_exp2 x n = Some a -> encl_ok n a /\ encl_has a (Rexp2 (B2R x)).
Proof.
intros x n a Hn H. unfold DyadicExp.ev_exp2 in H. cbv zeta in H.
destruct (DyadicExp.to_k (fceil x)) as [m|] eqn:Em; [|discriminate H].
destruct (DyadicConsts.ln2 n) as [[h l]|] eqn:El; [|discriminate H].
destruct (Dyadic.encl_add n {| Dyadic.en_lo := h; Dyadic.en_hi := h |} l) as [ln2e|] eqn:E2;
  [|discriminate H].
destruct (Dyadic.encl_point n (fceil x)) as [pc|] eqn:Epc; [|discriminate H].
destruct (Dyadic.encl_point n x) as [px|] eqn:Epx; [|discriminate H].
destruct (Dyadic.encl_sub n pc px) as [g|] eqn:Eg; [|discriminate H].
destruct (Dyadic.encl_mul n g ln2e) as [y|] eqn:Ey; [|discriminate H].
cbv beta iota in H.
destruct (to_k_bound _ _ Em) as (Hk & _).
destruct (ln2_correct n h l Hn El) as (Hh & Heh & Hl & HEl & Hhl).
destruct (hh_correct n h (2 ^ 13) Hh Heh) as (Ohh & Lhh & Hhh).
destruct (add_step n _ l ln2e _ _ Hn Ohh Hl Lhh HEl ltac:(lia) ltac:(lia) E2)
  as (O2 & L2 & H2).
destruct (point_has n (fceil x) pc Hn Epc) as (Opc & Lpc & Hpc).
destruct (point_step n (fceil x) pc Hn Epc) as (_ & _ & _ & _ & Fc).
destruct (point_has n x px Hn Epx) as (Opx & Lpx & Hpx).
destruct (sub_step n pc px g _ _ Hn Opc Opx Lpc Lpx ltac:(lia) ltac:(lia) Eg) as (Og & Lg & Hg).
destruct (mul_step n g ln2e y _ _ Hn Og O2 Lg L2 ltac:(lia) ltac:(lia) Ey) as (Oy & Ly & Hy).
(* [ceil x] is the integer [m]. *)
rewrite (to_k_int _ m _ Fc (fceil_IZR x) Em) in Hpc.
specialize (H2 _ _ Hhh Hhl).
replace (Dyadic.dy_R h + (ln 2 - Dyadic.dy_R h))%R with (ln 2) in H2 by ring.
specialize (Hy _ _ (Hg _ _ Hpc Hpx) H2).
replace ((IZR m - B2R x) * ln 2)%R with (IZR m * ln 2 - B2R x * ln 2)%R in Hy by ring.
destruct (scaled_correct n y m h l a _ _ Hn Oy Ly ltac:(lia) Hh ltac:(lia) Hl HEl Hhl ltac:(lia)
  Hy H) as (Oa & _ & Ha).
split; [exact Oa|].
unfold Rexp2, Rpower.
rewrite bpow_exp2, <- exp_plus in Ha.
replace (IZR m * ln 2 + - (IZR m * ln 2 - B2R x * ln 2))%R with (B2R x * ln 2)%R in Ha by ring.
exact Ha.
Qed.

Lemma ev_exp10_correct :
  forall x n a,
  level_ok n -> DyadicExp.ev_exp10 x n = Some a -> encl_ok n a /\ encl_has a (Rexp10 (B2R x)).
Proof.
intros x n a Hn H. unfold DyadicExp.ev_exp10 in H.
destruct (DyadicExp.to_k (fceil (mul x DyadicExp.log2_10))) as [k|] eqn:Ek; [|discriminate H].
destruct (DyadicConsts.ln2 n) as [[h2 l2]|] eqn:El2; [|discriminate H].
destruct (DyadicConsts.ln10 n) as [[h10 l10]|] eqn:El10; [|discriminate H].
destruct (DyadicExp.mul_int n {| Dyadic.en_lo := h2; Dyadic.en_hi := h2 |} k) as [a'|] eqn:Ea;
  [|discriminate H].
destruct (DyadicExp.mul_f64 n {| Dyadic.en_lo := h10; Dyadic.en_hi := h10 |} x) as [b|] eqn:Eb;
  [|discriminate H].
destruct (Dyadic.encl_sub n a' b) as [ab|] eqn:Eab; [|discriminate H].
destruct (DyadicExp.mul_int n l2 k) as [c|] eqn:Ec; [|discriminate H].
destruct (DyadicExp.mul_f64 n l10 x) as [d|] eqn:Ed; [|discriminate H].
destruct (Dyadic.encl_sub n c d) as [cd|] eqn:Ecd; [|discriminate H].
destruct (Dyadic.encl_add n ab cd) as [y|] eqn:Ey; [|discriminate H].
cbv beta iota in H.
destruct (to_k_bound _ _ Ek) as (Hk & _).
destruct (ln2_correct n h2 l2 Hn El2) as (Hh2 & Heh2 & Hl2 & HEl2 & Hhl2).
destruct (ln10_correct n h10 l10 Hn El10) as (Hh10 & Heh10 & Hl10 & HEl10 & Hhl10).
destruct (hh_correct n h2 (2 ^ 13) Hh2 Heh2) as (Ohh2 & Lhh2 & Hhh2).
destruct (hh_correct n h10 (2 ^ 13) Hh10 Heh10) as (Ohh10 & Lhh10 & Hhh10).
destruct (mul_int_step n _ k a' _ Hn Ohh2 Lhh2 ltac:(lia) Hk Ea) as (Oa & La & Ha).
destruct (mul_f64_step n _ x b _ Hn Ohh10 Lhh10 ltac:(lia) Eb) as (Ob & Lb & Hb).
destruct (sub_step n a' b ab _ _ Hn Oa Ob La Lb ltac:(lia) ltac:(lia) Eab)
  as (Oab & Lab & Hab).
destruct (mul_int_step n l2 k c _ Hn Hl2 HEl2 ltac:(lia) Hk Ec) as (Oc & Lc & Hc).
destruct (mul_f64_step n l10 x d _ Hn Hl10 HEl10 ltac:(lia) Ed) as (Od & Ld & Hd).
destruct (sub_step n c d cd _ _ Hn Oc Od Lc Ld ltac:(lia) ltac:(lia) Ecd) as (Ocd & Lcd & Hcd).
destruct (add_step n ab cd y _ _ Hn Oab Ocd Lab Lcd ltac:(lia) ltac:(lia) Ey) as (Oy & Ly & Hy).
(* [y] holds [k ln 2 - x ln 10]. *)
specialize (Hy _ _ (Hab _ _ (Ha _ Hhh2) (Hb _ Hhh10)) (Hcd _ _ (Hc _ Hhl2) (Hd _ Hhl10))).
replace (Dyadic.dy_R h2 * IZR k - B2R x * Dyadic.dy_R h10 +
         ((ln 2 - Dyadic.dy_R h2) * IZR k - B2R x * (ln 10 - Dyadic.dy_R h10)))%R
  with (IZR k * ln 2 - B2R x * ln 10)%R in Hy by ring.
destruct (scaled_correct n y k h2 l2 a _ _ Hn Oy Ly ltac:(lia) Hh2 ltac:(lia) Hl2 HEl2 Hhl2
  ltac:(lia) Hy H) as (Oa' & _ & Ha').
split; [exact Oa'|].
unfold Rexp10, Rpower.
rewrite bpow_exp2, <- exp_plus in Ha'.
replace (IZR k * ln 2 + - (IZR k * ln 2 - B2R x * ln 10))%R with (B2R x * ln 10)%R in Ha'
  by ring.
exact Ha'.
Qed.

(** [B2R l] for a literal [l], as in [DyHypRules.v]: [B2SF l] computes to
    its sign, significand and exponent. *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** [k as f64] is [k] for [|k| < 2^53], as [DyPowCore.of_i64_exact]
    shows for the same function of [DyadicPow]; [DyPowCore.v] requires
    this file. *)
Local Lemma exp_of_i64 :
  forall k, Z.abs k < 2 ^ 53 ->
  is_finite (DyadicExp.of_i64 k) = true /\ B2R (DyadicExp.of_i64 k) = IZR k.
Proof.
intros k Hk.
assert (Fk : generic_format radix2 (SpecFloat.fexp 53 1024) (IZR k)).
{ change (SpecFloat.fexp 53 1024) with (FLT_exp (-1074) 53).
  apply generic_format_FLT, (FLT_spec _ _ _ _ (Float radix2 k 0)).
  - unfold F2R; cbn [Fnum Fexp bpow]. ring.
  - cbn [Fnum radix_val radix2]. exact Hk.
  - cbn [Fexp]. lia. }
unfold DyadicExp.of_i64.
pose proof (binary_normalize_correct 53 1024 prec_gt_0_53 prec_lt_emax_53_1024
  mode_NE k 0 false) as H.
cbv zeta in H.
replace (F2R (Float radix2 k 0)) with (IZR k) in H by (unfold F2R; cbn [Fnum Fexp bpow]; ring).
rewrite (round_generic _ _ _ (IZR k) Fk) in H.
rewrite Rlt_bool_true in H.
2: { rewrite <- abs_IZR.
  apply Rlt_trans with (IZR (2 ^ 53)); [apply IZR_lt; exact Hk|].
  rewrite (IZR_Zpower radix2) by lia. apply bpow_lt. lia. }
destruct H as (HR & HF & _). split; [exact HF | exact HR].
Qed.

(** The rule of [exp2_dir_slow] for the integers from -1022 to 1023: at
    an [x] in the range [-1075 <= x < 1024] of the test of
    [exp2_dir_with], which calls [exp2_dir_slow], with
    [x >= -1022] and [(x as i64) as f64 == x], [two_pow (to_i64 x)] is
    [2^x], rounded in either direction. It is here rather than in
    [DyExpRules.v] as it takes [pow2_bits] from [FastRound.v], which
    requires [DyExpRules.v]. *)
Lemma exp2_int_rule :
  forall x (up : bool), is_finite x = true ->
  le (from_bits 0xc090cc0000000000) x && lt x (from_bits 0x4090000000000000) = true ->
  ge x (from_bits 0xc08ff00000000000) && eq (DyadicExp.of_i64 (DyadicExp.to_i64 x)) x = true ->
  mpfr_round f64_format (if up then RNDU else RNDD) (Rexp2 (B2R x))
    (with_val (DyadicExp.two_pow (DyadicExp.to_i64 x))).
Proof.
intros x up Fx H0 H4.
apply andb_prop in H0 as [_ Hhi]. apply andb_prop in H4 as [Hge He].
apply lt_R in Hhi; [| exact Fx | vm_compute; reflexivity].
apply ge_R in Hge; [| exact Fx | vm_compute; reflexivity].
assert (L1 : B2R (from_bits 0xc08ff00000000000) = (-1022)%R)
  by (lit_B2R; cbn [bpow radix_val radix2]; lra).
assert (L2 : B2R (from_bits 0x4090000000000000) = 1024%R)
  by (lit_B2R; cbn [bpow radix_val radix2]; lra).
rewrite L1 in Hge. rewrite L2 in Hhi.
(* [to_i64 x] is [trunc x], which lies in [-1022, 1024] as [x] does. *)
assert (M : DyadicExp.to_i64 x = Z.max (- 2 ^ 63) (Z.min (2 ^ 63 - 1) (Btrunc x)))
  by (destruct x; try discriminate Fx; reflexivity).
assert (T : Btrunc x = Ztrunc (B2R x))
  by (apply eq_IZR; rewrite Btrunc_correct, round_FIX_IZR; reflexivity).
assert (T1 : -1022 <= Ztrunc (B2R x))
  by (rewrite <- (Ztrunc_IZR (-1022)); apply Ztrunc_le; lra).
assert (T2 : Ztrunc (B2R x) <= 1024)
  by (rewrite <- (Ztrunc_IZR 1024); apply Ztrunc_le; lra).
set (k := DyadicExp.to_i64 x) in *.
assert (Hk : -1022 <= k <= 1024) by (rewrite M, T; lia).
(* [k as f64 == x] is true, so [x] is the integer [k], and [k <= 1023]. *)
destruct (exp_of_i64 k) as [Fk Vk]; [lia|].
unfold eq in He. rewrite Beqb_correct in He by first [exact Fk | exact Fx].
destruct (Req_bool_spec (B2R (DyadicExp.of_i64 k)) (B2R x)) as [Ek|]; [|discriminate].
rewrite Vk in Ek.
assert (Hk' : k < 1024) by (apply lt_IZR; lra).
(* [two_pow k] is the [f64] [2^k], as [k] is in the normal range. *)
destruct (FastRound.pow2_bits k ltac:(lia)) as [Fp Ep].
unfold DyadicExp.two_pow. apply rnd_exact; [exact Fp|].
rewrite Ep, bpow_exp2, Ek. reflexivity.
Qed.

(** ** The directed functions *)

Lemma exp_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x up v,
  is_finite x = true -> DyadicExp.exp_dir_with z x up = Some v ->
  post up (exp (B2R x)) v.
Proof.
intros z post Hp Hz x up v Fx H. unfold DyadicExp.exp_dir_with in H.
destruct (lt (fabs x) DyadicExp.tiny_exp) eqn:G3; cbv iota in H.
{ injection H as <-. apply Hp. exact (exp_tiny_rule x up Fx G3). }
destruct (lt x (from_bits 0x4086300000000000) && gt x (from_bits 0xc087500000000000)) eqn:G0;
  cbv iota in H.
{ destruct (DyadicExp.fast_exp_dir false x up) eqn:F; cbv iota in H.
  { injection H as <-. apply Hp. exact (fast_exp_dir_correct false x up _ Fx F). }
  apply (Hz (DyadicExp.ev_exp x) up (DyadicExp.exp_start x)); [|exact H].
  intros n a Hn Ha. exact (ev_exp_correct x n a Hn Ha). }
rewrite (fin_not_nan x Fx), (fin_neq_inf x Fx), (fin_neq_ninf x Fx) in H. cbn [orb] in H.
destruct (ge x (from_bits 0x4086300000000000)) eqn:G1; cbv iota in H.
{ injection H as <-. apply Hp. exact (exp_overflow_rule x up Fx G1). }
(* [x < 710 && x > -746] and [x >= 710] are false, so [x <= -746]. *)
assert (G2 : le x (from_bits 0xc087500000000000) = true)
  by (apply (range_low x (from_bits 0x4086300000000000));
      [exact Fx | reflexivity | reflexivity | exact G0 | exact G1]).
injection H as <-. apply Hp. exact (exp_underflow_rule x up Fx G2).
Qed.

Theorem exp_dir_correct :
  forall x up v,
  is_finite x = true -> DyadicExp.exp_dir_with ziv_strict x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (exp (B2R x)) (with_val v).
Proof. exact (exp_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem exp_dir_side :
  forall x up v,
  is_finite x = true -> DyadicExp.exp_dir x up = Some v ->
  f64_side up (exp (B2R x)) v.
Proof. exact (exp_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem exp_dir_strict :
  forall x up v,
  DyadicExp.exp_dir_with ziv_strict x up = Some v -> DyadicExp.exp_dir x up = Some v.
Proof.
intros x up v. unfold DyadicExp.exp_dir, DyadicExp.exp_dir_with. dir_strict.
Qed.

Lemma exp2_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x up v,
  is_finite x = true -> DyadicExp.exp2_dir_with z x up = Some v ->
  post up (Rexp2 (B2R x)) v.
Proof.
intros z post Hp Hz x up v Fx H. unfold DyadicExp.exp2_dir_with, DyadicExp.exp2_dir_slow in H.
destruct (lt (fabs x) DyadicExp.tiny_exp) eqn:G3; cbv iota in H.
{ injection H as <-. apply Hp. exact (exp2_tiny_rule x up Fx G3). }
destruct (le (from_bits 0xc090cc0000000000) x && lt x (from_bits 0x4090000000000000)) eqn:G0;
  cbv iota in H.
{ destruct (DyadicExp.fast_exp2_dir false x up) eqn:F; cbv iota in H.
  { injection H as <-. apply Hp.
    exact (fast_exp2_dir_correct false x up _ Fx (tiny_exp_false x Fx G3) F). }
  destruct (ge x (from_bits 0xc08ff00000000000)
            && eq (DyadicExp.of_i64 (DyadicExp.to_i64 x)) x) eqn:G4; cbv iota in H.
  { injection H as <-. apply Hp. exact (exp2_int_rule x up Fx G0 G4). }
  apply (Hz (DyadicExp.ev_exp2 x) up (DyadicExp.exp2_start x)); [|exact H].
  intros n a Hn Ha. exact (ev_exp2_correct x n a Hn Ha). }
rewrite (fin_not_nan x Fx), (fin_neq_inf x Fx), (fin_neq_ninf x Fx) in H. cbn [orb] in H.
destruct (ge x (from_bits 0x4090000000000000)) eqn:G1; cbv iota in H.
{ injection H as <-. apply Hp. exact (exp2_overflow_rule x up Fx G1). }
(* [-1075 <= x && x < 1024] and [x >= 1024] are false, so [x < -1075]. *)
assert (G2 : lt x (from_bits 0xc090cc0000000000) = true)
  by (apply (range_low_ge x (from_bits 0x4090000000000000));
      [exact Fx | reflexivity | reflexivity | exact G0 | exact G1]).
injection H as <-. apply Hp. exact (exp2_underflow_rule x up Fx G2).
Qed.

Theorem exp2_dir_correct :
  forall x up v,
  is_finite x = true -> DyadicExp.exp2_dir_with ziv_strict x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (Rexp2 (B2R x)) (with_val v).
Proof. exact (exp2_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem exp2_dir_side :
  forall x up v,
  is_finite x = true -> DyadicExp.exp2_dir x up = Some v ->
  f64_side up (Rexp2 (B2R x)) v.
Proof. exact (exp2_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem exp2_dir_strict :
  forall x up v,
  DyadicExp.exp2_dir_with ziv_strict x up = Some v -> DyadicExp.exp2_dir x up = Some v.
Proof.
intros x up v. unfold DyadicExp.exp2_dir, DyadicExp.exp2_dir_with, DyadicExp.exp2_dir_slow.
dir_strict.
Qed.

Lemma exp10_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x up v,
  is_finite x = true -> DyadicExp.exp10_dir_with z x up = Some v ->
  post up (Rexp10 (B2R x)) v.
Proof.
intros z post Hp Hz x up v Fx H. unfold DyadicExp.exp10_dir_with in H.
destruct (lt (fabs x) DyadicExp.tiny_exp10) eqn:G3; cbv iota in H.
{ injection H as <-. apply Hp. exact (exp10_tiny_rule x up Fx G3). }
destruct (lt x (from_bits 0x4073500000000000) && gt x (from_bits 0xc074400000000000)) eqn:G0;
  cbv iota in H.
{ destruct (DyadicExp.fast_exp10_dir false x up) eqn:F; cbv iota in H.
  { injection H as <-. apply Hp.
    exact (fast_exp10_dir_correct false x up _ Fx (tiny_exp10_false x Fx G3) F). }
  destruct (le DyadicExp.one x && le x (from_bits 0x4036000000000000) && eq x (ffloor x))
    eqn:G4; cbv iota in H.
  { injection H as <-. apply Hp. exact (exp10_int_rule x up Fx G4). }
  apply (Hz (DyadicExp.ev_exp10 x) up (DyadicExp.exp10_start x)); [|exact H].
  intros n a Hn Ha. exact (ev_exp10_correct x n a Hn Ha). }
rewrite (fin_not_nan x Fx), (fin_neq_inf x Fx), (fin_neq_ninf x Fx) in H. cbn [orb] in H.
destruct (ge x (from_bits 0x4073500000000000)) eqn:G1; cbv iota in H.
{ injection H as <-. apply Hp. exact (exp10_overflow_rule x up Fx G1). }
(* [x < 309 && x > -324] and [x >= 309] are false, so [x <= -324]. *)
assert (G2 : le x (from_bits 0xc074400000000000) = true)
  by (apply (range_low x (from_bits 0x4073500000000000));
      [exact Fx | reflexivity | reflexivity | exact G0 | exact G1]).
injection H as <-. apply Hp. exact (exp10_underflow_rule x up Fx G2).
Qed.

Theorem exp10_dir_correct :
  forall x up v,
  is_finite x = true -> DyadicExp.exp10_dir_with ziv_strict x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (Rexp10 (B2R x)) (with_val v).
Proof. exact (exp10_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem exp10_dir_side :
  forall x up v,
  is_finite x = true -> DyadicExp.exp10_dir x up = Some v ->
  f64_side up (Rexp10 (B2R x)) v.
Proof. exact (exp10_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem exp10_dir_strict :
  forall x up v,
  DyadicExp.exp10_dir_with ziv_strict x up = Some v -> DyadicExp.exp10_dir x up = Some v.
Proof.
intros x up v. unfold DyadicExp.exp10_dir, DyadicExp.exp10_dir_with. dir_strict.
Qed.
