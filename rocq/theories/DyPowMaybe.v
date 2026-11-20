(** * The test [maybe_exact] of the dyadic [pow]

    [maybe_exact x y] of [DyadicPow] in [Model.v] says whether [pow] tries
    [exact] before the fast path. At a normal [x > 0] other than 1 and a
    finite [y] other than 0, it is true wherever [exact] returns an [f64]
    ([maybe_exact_complete]), which is why [pow] calls [exact] after the
    fast path only at a subnormal [x]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Elementary DyRound DyConv DyPowArith DyPowRules
  DyPowExact Encoding Decompose.

Open Scope Z_scope.

Local Notation G := (generic_format radix2 (SpecFloat.fexp 53 1024)).

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (as in [FastExp.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** [f64::MIN_POSITIVE] is 2^-1022. *)
Lemma lit_min_normal :
  is_finite DyadicPow.min_normal = true /\ B2R DyadicPow.min_normal = bpow radix2 (-1022).
Proof.
split; [vm_compute; reflexivity |].
lit_B2R. change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
reflexivity.
Qed.

(** [2^e] in [Z] is [bpow radix2 e]. *)
Local Lemma IZR_pow2 : forall e, 0 <= e -> IZR (2 ^ e) = bpow radix2 e.
Proof. intros e He. rewrite <- IZR_Zpower by exact He. reflexivity. Qed.

(** [o 2^t] with an odd [o > 0] has [t] trailing zeros. *)
Local Lemma tz_odd_mul :
  forall o t, Z.odd o = true -> 0 < o -> 0 <= t -> trailing_zeros 64 (o * 2 ^ t) = t.
Proof.
intros o t Ho Ho0 Ht.
assert (Hm : 0 < o * 2 ^ t) by (apply Z.mul_pos_pos; [exact Ho0 | apply Z.pow_pos_nonneg; lia]).
destruct (trailing_zeros_odd _ Hm) as (Hz & Hodd & Hs).
revert Hz Hodd Hs. generalize (trailing_zeros 64 (o * 2 ^ t)) as z. intros z Hz Hodd Hs.
assert (ER : (IZR o * bpow radix2 t = IZR (Z.shiftr (o * 2 ^ t) z) * bpow radix2 z)%R).
{ rewrite <- !IZR_pow2 by lia. rewrite <- !mult_IZR. f_equal. exact Hs. }
destruct (odd_pow2_inj _ _ _ _ Ho Hodd ER) as [_ E]. lia.
Qed.

(** At a normal [x], the [b] of [maybe_exact] is [Z.log2 mx] of the odd
    part [mx] of [x]: the low 53 bits of [bits | 2^52] are [2^52 + f =
    mx 2^z], and the bits above them are a multiple of [2^53], so that
    [bits | 2^52 = (A 2^(53 - z) + mx) 2^z] with an odd first factor and
    [tz = z], while [log2 (2^52 + f) = 52]. *)
Local Lemma b_log2 :
  forall x mx ex,
  is_finite x = true -> (bpow radix2 (-1022) <= Rabs (B2R x))%R ->
  DyadicPow.odd_parts x = (mx, ex) ->
  52 - trailing_zeros 64 (Z.lor (to_bits x) (Z.shiftl 1 52)) = Z.log2 mx.
Proof.
intros x mx ex Fx Hn Ox.
assert (Hx0 : B2R x <> 0%R).
{ intros E. rewrite E, Rabs_R0 in Hn. pose proof (bpow_gt_0 radix2 (-1022)). lra. }
destruct (odd_parts_spec x mx ex Fx Hx0 Ox) as (Hmx & Hmx0 & _ & Ax).
destruct (to_bits_finite x Fx) as (c & Hc & Hbits).
unfold DyadicPow.odd_parts in Ox. rewrite Hbits, biased_finite, frac_finite in Ox by exact Hc.
rewrite Hbits.
destruct (Z.eqb_spec (c / 2^52) 0) as [HE0 | HE0]; cbv beta iota zeta in Ox.
- exfalso. apply pair_equal_spec in Ox as [Emx Eex].
  destruct (Z.eq_dec (c mod 2^52) 0) as [E0 | E0].
  { rewrite E0, Z.shiftr_0_l in Emx. lia. }
  destruct (trailing_zeros_odd (c mod 2^52) ltac:(zlia)) as (Hz & _ & Hsplit).
  set (z := trailing_zeros 64 (c mod 2^52)) in *.
  rewrite Emx in Hsplit.
  assert (E : (IZR mx * bpow radix2 ex = IZR (c mod 2^52) * bpow radix2 (-1074))%R).
  { rewrite <- Eex, Hsplit, mult_IZR, IZR_pow2, bpow_plus by lia. ring. }
  assert (Hlt : (IZR (c mod 2^52) * bpow radix2 (-1074) < bpow radix2 (-1022))%R).
  { replace (bpow radix2 (-1022)) with (bpow radix2 52 * bpow radix2 (-1074))%R
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_lt_compat_r; [apply bpow_gt_0 |].
    rewrite <- IZR_pow2 by lia. apply IZR_lt. zlia. }
  lra.
- rewrite lor_implicit in Ox by zlia.
  set (m0 := c mod 2^52 + 2^52) in Ox.
  assert (Hm0 : 2^52 <= m0 < 2^53) by (unfold m0; zlia).
  destruct (trailing_zeros_odd m0 ltac:(lia)) as (Hz & _ & Hsplit).
  set (z := trailing_zeros 64 m0) in *.
  apply pair_equal_spec in Ox as [Emx _]. rewrite Emx in Hsplit.
  assert (Hz52 : z <= 52).
  { destruct (Z_le_gt_dec z 52) as [|Hz53]; [assumption | exfalso].
    assert (2 ^ 53 <= 2 ^ z) by (apply Z.pow_le_mono_r; lia). nia. }
  assert (HL : Z.log2 mx = 52 - z).
  { assert (Hl : Z.log2 m0 = 52)
      by (apply Z.log2_unique; [lia | split; [lia | change (2 ^ Z.succ 52) with (2 ^ 53); lia]]).
    rewrite Hsplit, Z.log2_mul_pow2 in Hl by lia. lia. }
  set (N := Z.lor (sign_bit (Bsign x) + c) (Z.shiftl 1 52)).
  (* The low 53 bits of [N] are [m0 = 2^52 + f]. *)
  assert (HN : N mod 2^53 = m0).
  { rewrite <- (Z.mod_small m0 (2^53)) by lia. unfold N, m0.
    rewrite <- (lor_implicit (c mod 2^52)) by zlia.
    apply Z.bits_inj'. intros i Hi.
    destruct (Z.lt_ge_cases i 53) as [H53 | H53].
    2: { rewrite !Z.mod_pow2_bits_high by lia. reflexivity. }
    rewrite !Z.mod_pow2_bits_low by exact H53. rewrite !Z.lor_spec.
    destruct (Z.lt_ge_cases i 52) as [H52 | H52].
    - f_equal. rewrite <- (Z.mod_pow2_bits_low (sign_bit (Bsign x) + c) 52 i H52).
      f_equal. destruct (Bsign x); cbn [sign_bit]; zlia.
    - assert (B : Z.testbit (Z.shiftl 1 52) i = true) by (replace i with 52 by lia; reflexivity).
      rewrite B, !Bool.orb_true_r. reflexivity. }
  assert (HN0 : 0 <= N).
  { apply Z.lor_nonneg.
    split; [destruct (Bsign x); cbn [sign_bit]; lia | apply Z.shiftl_nonneg; lia]. }
  set (A := N / 2^53).
  assert (HA : 0 <= A) by (apply Z.div_pos; lia).
  assert (EN : N = (A * 2 ^ (53 - z) + mx) * 2 ^ z).
  { assert (E53 : 2 ^ 53 = 2 ^ (53 - z) * 2 ^ z) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    pose proof (Z.div_mod N (2^53) ltac:(lia)) as D. fold A in D.
    rewrite HN, Hsplit, E53 in D. rewrite D. ring. }
  assert (Ho : Z.odd (A * 2 ^ (53 - z) + mx) = true).
  { rewrite Z.odd_add, Z.odd_mul, Z.odd_pow, Hmx by lia. destruct (Z.odd A); reflexivity. }
  assert (Hpos : 0 < A * 2 ^ (53 - z) + mx).
  { assert (0 <= A * 2 ^ (53 - z))
      by (apply Z.mul_nonneg_nonneg; [exact HA | apply Z.pow_nonneg; lia]).
    lia. }
  rewrite EN, (tz_odd_mul _ z Ho Hpos Hz). lia.
Qed.

(** A [y = my 2^ey] with [my < 2^11] and [ey > -1023] is normal, and its
    stored significand [2^52 + f = my 2^z] has [z >= 42] trailing zeros, so
    that the low 32 bits of [y] are 0. *)
Local Lemma low_bits :
  forall y my ey,
  is_finite y = true -> B2R y <> 0%R -> DyadicPow.odd_parts y = (my, ey) ->
  my < 2 ^ 11 -> -1023 < ey -> to_bits y mod 2 ^ 32 = 0.
Proof.
intros y my ey Fy Hy0 Oy Hmy Hey.
destruct (odd_parts_spec y my ey Fy Hy0 Oy) as (_ & Hmy0 & _ & _).
destruct (to_bits_finite y Fy) as (c & Hc & Hbits).
unfold DyadicPow.odd_parts in Oy. rewrite Hbits, biased_finite, frac_finite in Oy by exact Hc.
rewrite Hbits.
destruct (Z.eqb_spec (c / 2^52) 0) as [HE0 | HE0]; cbv beta iota zeta in Oy.
- exfalso. set (z := trailing_zeros 64 (c mod 2^52)) in *.
  apply pair_equal_spec in Oy as [Emy Eey].
  destruct (Z.eq_dec (c mod 2^52) 0) as [E0 | E0].
  { rewrite E0, Z.shiftr_0_l in Emy. lia. }
  destruct (trailing_zeros_odd (c mod 2^52) ltac:(zlia)) as (Hz & _ & Hsplit).
  fold z in Hsplit. rewrite Emy in Hsplit.
  assert (2 ^ 52 <= 2 ^ z) by (apply Z.pow_le_mono_r; lia).
  assert (c mod 2^52 < 2^52) by zlia.
  nia.
- rewrite lor_implicit in Oy by zlia.
  set (m0 := c mod 2^52 + 2^52) in Oy.
  assert (Hm0 : m0 = c mod 2^52 + 2^52) by reflexivity.
  assert (Hm0b : 2^52 <= m0 < 2^53) by zlia. clearbody m0.
  destruct (trailing_zeros_odd m0 ltac:(lia)) as (Hz & _ & Hsplit).
  set (z := trailing_zeros 64 m0) in *. clearbody z.
  apply pair_equal_spec in Oy as [Emy _]. rewrite Emy in Hsplit.
  assert (Hz42 : 42 <= z).
  { destruct (Z_lt_le_dec z 42) as [Hlt | ]; [exfalso | assumption].
    assert (2 ^ z <= 2 ^ 41) by (apply Z.pow_le_mono_r; lia).
    assert (0 < 2 ^ z) by (apply Z.pow_pos_nonneg; lia). nia. }
  assert (E1 : 2 ^ z = 2 ^ (z - 32) * 2 ^ 32) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite E1, Z.mul_assoc in Hsplit.
  set (W := my * 2 ^ (z - 32)) in Hsplit. clearbody W.
  destruct (Bsign y); cbn [sign_bit]; zlia.
Qed.

(** If [L y] is an [f64] with [0 <= L y < 53], the [t] of [maybe_exact] is [L y]
    exactly, and passes the range check; where [t] is [-0], at [L = 0] and
    [y < 0], [le zero t] holds, as [Bleb] compares the reals. *)
Local Lemma t_range :
  forall L y, 0 <= L <= 52 -> is_finite y = true ->
  (0 <= IZR L * B2R y < 53)%R -> G (IZR L * B2R y) ->
  (Model.le zero (mul (DyadicPow.of_i64 L) y) &&
   Model.lt (mul (DyadicPow.of_i64 L) y) (DyadicPow.of_i64 53))%bool = true.
Proof.
intros L y HL Fy Hr Gt.
destruct (of_u64_exact L ltac:(lia)) as (FL & _ & EL).
destruct (of_u64_exact 53 ltac:(lia)) as (F53 & _ & E53).
change (DyadicPow.of_i64 L) with (of_u64 L). change (DyadicPow.of_i64 53) with (of_u64 53).
assert (Er : round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE) (IZR L * B2R y)
             = (IZR L * B2R y)%R)
  by (apply round_generic; first [exact Gt | typeclasses eauto]).
assert (B1024 : (2048 <= bpow radix2 1024)%R)
  by (change 2048%R with (bpow radix2 11); apply bpow_le; lia).
pose proof (Bmult_correct 53 1024 _ _ mode_NE (of_u64 L) y) as Hm.
rewrite EL, Er, Rlt_bool_true in Hm by (rewrite Rabs_pos_eq by lra; lra).
destruct Hm as (Em & Fm & _). rewrite FL, Fy in Fm. cbn [andb] in Fm.
unfold Model.le, Model.lt, mul.
rewrite Bleb_correct, Bltb_correct by first [exact Fm | exact F53 | reflexivity].
rewrite Em, E53. change (B2R zero) with 0%R.
rewrite Rle_bool_true, Rlt_bool_true by lra. reflexivity.
Qed.

(** At a normal [x > 0] other than 1 and a finite [y] other than 0,
    [maybe_exact] is true wherever [exact] returns an [f64]. *)
Lemma maybe_exact_complete :
  forall x y (v : f64),
  is_finite x = true -> (bpow radix2 (-1022) <= B2R x)%R -> B2R x <> 1%R ->
  is_finite y = true -> B2R y <> 0%R ->
  DyadicPow.exact x y = Some (Some v) -> DyadicPow.maybe_exact x y = true.
Proof.
(* [exact] needs [ey <= 11]. If its root [mr] is 1, then [er <> 0] (as
   [x <> 1]), and the range check of [er p] gives [k <= 10] and [L = 0].
   Otherwise [y > 0] and [mr^p < 2^53], so [p < 53], [k <= 5], and
   [2^(L p) <= mx^p = (mr^p)^(2^k) < 2^(53 2^k)] gives [L y < 53]. Both
   give [my < 2^11], so [low_bits] applies, and [L y = (L my) 2^ey] is an
   [f64]. *)
intros x y v Fx Hn Hx1 Fy Hy0 H.
assert (Hx : (0 < B2R x)%R) by (pose proof (bpow_gt_0 radix2 (-1022)); lra).
destruct (DyadicPow.odd_parts x) as [mx ex] eqn:Ox.
destruct (exact_v_parts x mx ex Fx Hx Ox) as (Hmx & Hmx0 & Hex & Hex2 & Ax).
assert (Hn' : (bpow radix2 (-1022) <= Rabs (B2R x))%R) by (rewrite Rabs_pos_eq by lra; exact Hn).
pose proof (b_log2 x mx ex Fx Hn' Ox) as Hb.
destruct (DyadicPow.odd_parts y) as [my ey] eqn:Oy.
destruct (odd_parts_spec y my ey Fy Hy0 Oy) as (Hmy & Hmy0 & Hey & Ay).
unfold DyadicPow.exact in H. rewrite Ox, Oy in H.
destruct (11 <? ey) eqn:E11; [discriminate H |].
destruct (if 0 <=? ey then (Z.shiftl my ey, 0) else (my, - ey)) as [p k] eqn:PK.
assert (PKs : (0 <= ey /\ p = my * 2 ^ ey /\ k = 0) \/ (ey < 0 /\ p = my /\ k = - ey)).
{ revert PK. destruct (0 <=? ey) eqn:B; intros PK; injection PK as <- <-.
  - left. apply Z.leb_le in B. rewrite Z.shiftl_mul_pow2 by exact B. lia.
  - right. apply Z.leb_gt in B. lia. }
destruct (pk_spec my ey p k ltac:(lia) PK) as (Hp & Hk & _ & _ & Ey).
assert (Hmyp : my <= p).
{ destruct PKs as [(Hey0 & -> & _) | (_ & -> & _)]; [|lia].
  assert (0 < 2 ^ ey) by (apply Z.pow_pos_nonneg; lia). nia. }
destruct (DyadicPow.roots_loop (Z.to_nat k) mx ex) as [[mr er]|] eqn:RL; [|discriminate H].
destruct (roots_loop_sound _ mx ex mr er ltac:(lia) RL) as (Hmr & Emx & Eex).
rewrite Z2Nat.id in Emx, Eex by exact Hk.
assert (Ly : lt y zero = Rlt_bool (B2R y) 0) by (apply Bltb_correct; [exact Fy | reflexivity]).
rewrite Ly in H.
assert (H2k : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
assert (HL52 : 0 <= Z.log2 mx <= 52).
{ split; [apply Z.log2_nonneg |]. assert (Z.log2 mx < 53) by (apply Z.log2_lt_pow2; lia). lia. }
assert (Main : my < 2 ^ 11 /\ k <= 10 /\
  (0 <= IZR (Z.log2 mx) * B2R y < 53)%R /\ G (IZR (Z.log2 mx) * B2R y)).
{ destruct (Z.eq_dec mr 1) as [R1 | R1].
  - subst mr. rewrite Z.pow_1_l in Emx by lia.
    rewrite Z.eqb_refl in H. cbv beta iota zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Rg; [discriminate H |] end.
    apply range_check in Rg; [| lia]. destruct Rg as [He1 He2]. rewrite Z.log2_1 in He2.
    assert (Hep : -1074 <= er * p <= 1074) by (destruct (Rlt_bool (B2R y) 0); lia).
    assert (Eer : er <> 0).
    { intros E0. apply Hx1. rewrite Ax, Emx, Eex, E0, Z.mul_0_l.
      change (bpow radix2 0) with 1%R. lra. }
    rewrite Emx, Z.log2_1 in Hex2.
    assert (Hk10 : k <= 10).
    { destruct (Z_le_gt_dec k 10) as [|Hk11]; [assumption | exfalso].
      assert (2048 <= 2 ^ k) by (change 2048 with (2 ^ 11); apply Z.pow_le_mono_r; lia).
      assert (er <= -1 \/ 1 <= er) as [Hn1 | Hp1] by lia; nia. }
    assert (Hp1074 : p <= 1074) by (assert (er <= -1 \/ 1 <= er) as [Hn1 | Hp1] by lia; nia).
    rewrite Emx, Z.log2_1. replace (IZR 0 * B2R y)%R with 0%R by ring.
    split; [lia |]. split; [exact Hk10 |]. split; [lra | apply generic_format_0].
  - rewrite (proj2 (Z.eqb_neq mr 1) R1) in H.
    destruct (Rlt_bool_cases (B2R y) 0) as [[SB Yn] | [SB Yp]]; rewrite SB in H;
      [discriminate H |].
    assert (Yp' : (0 < B2R y)%R) by lra.
    destruct (DyadicPow.small_power mr p) as [q|] eqn:Q; [|discriminate H].
    apply small_power_spec in Q; [| lia | lia]. destruct Q as [_ Hq53].
    rewrite Rabs_pos_eq in Ay by lra.
    assert (Hp53 : p < 53).
    { destruct (Z_lt_le_dec p 53) as [|Hp53]; [assumption | exfalso].
      assert (2 ^ 53 <= 2 ^ p) by (apply Z.pow_le_mono_r; lia).
      assert (2 ^ p <= mr ^ p) by (apply Z.pow_le_mono_l; lia). lia. }
    assert (Hk5 : k <= 5).
    { destruct (Z_le_gt_dec k 5) as [|Hk6]; [assumption | exfalso].
      assert (2 ^ 6 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia).
      assert (2 ^ 53 <= 2 ^ (2 ^ k)) by (apply Z.pow_le_mono_r; lia).
      assert (2 ^ (2 ^ k) <= mr ^ (2 ^ k)) by (apply Z.pow_le_mono_l; lia). lia. }
    pose proof (Z.log2_spec mx ltac:(lia)) as [HL _].
    set (L := Z.log2 mx) in *.
    assert (HLp : L * p < 53 * 2 ^ k).
    { destruct (Z_lt_le_dec (L * p) (53 * 2 ^ k)) as [|Hge]; [assumption | exfalso].
      assert (A1 : 2 ^ (53 * 2 ^ k) <= 2 ^ (L * p)) by (apply Z.pow_le_mono_r; lia).
      assert (A2 : 2 ^ (L * p) <= mx ^ p).
      { rewrite Z.pow_mul_r by lia. apply Z.pow_le_mono_l.
        split; [apply Z.pow_nonneg; lia | exact HL]. }
      assert (A3 : mx ^ p = (mr ^ p) ^ (2 ^ k)).
      { rewrite Emx, <- !Z.pow_mul_r by lia. f_equal. apply Z.mul_comm. }
      assert (A4 : (mr ^ p) ^ (2 ^ k) < (2 ^ 53) ^ (2 ^ k)).
      { apply Z.pow_lt_mono_l; [lia |]. split; [apply Z.pow_nonneg; lia | exact Hq53]. }
      rewrite <- (Z.pow_mul_r 2 53 (2 ^ k)) in A4 by lia. lia. }
    assert (Ry : B2R y = (IZR p / IZR (2 ^ k))%R) by (rewrite Ay; exact Ey).
    assert (Hk2 : (0 < IZR (2 ^ k))%R) by (apply IZR_lt; lia).
    assert (Hlt53 : (IZR L * B2R y < 53)%R).
    { rewrite Ry.
      replace (IZR L * (IZR p / IZR (2 ^ k)))%R with (IZR (L * p) * / IZR (2 ^ k))%R
        by (rewrite mult_IZR; field; lra).
      replace 53%R with (IZR (53 * 2 ^ k) * / IZR (2 ^ k))%R by (rewrite mult_IZR; field; lra).
      apply Rmult_lt_compat_r; [apply Rinv_0_lt_compat; exact Hk2 | apply IZR_lt; exact HLp]. }
    assert (HL0 : (0 <= IZR L)%R) by (apply IZR_le; lia).
    assert (Hmy53 : 0 <= L * my < 2 ^ 53) by nia.
    assert (E : (IZR L * B2R y = IZR (L * my) * bpow radix2 ey)%R) by (rewrite Ay, mult_IZR; ring).
    split; [lia |]. split; [lia |]. split.
    + split; [apply Rmult_le_pos; lra | exact Hlt53].
    + assert (B1024 : (2048 <= bpow radix2 1024)%R)
        by (change 2048%R with (bpow radix2 11); apply bpow_le; lia).
      assert (Hb1 : (IZR (L * my) * bpow radix2 ey < bpow radix2 1024)%R) by lra.
      rewrite E. destruct (normalize_exact (L * my) ey Hmy53 Hey Hb1) as (_ & En).
      rewrite <- En. apply generic_format_B2R. }
destruct Main as (Hmy11 & Hk10 & Hr & Gt).
assert (Hey' : -1023 < ey) by (destruct PKs as [(? & _ & _) | (? & _ & ?)]; lia).
pose proof (low_bits y my ey Fy Hy0 Oy Hmy11 Hey') as Hlow.
unfold DyadicPow.maybe_exact. rewrite Hlow, Z.eqb_refl. cbn [negb].
rewrite Hb. apply t_range; assumption.
Qed.
