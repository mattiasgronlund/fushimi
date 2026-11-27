(** * The fast path of [cbrt]

    [DyadicRoot.fast_cbrt fma x], for a finite nonzero [x], writes
    [|x| = zz 2^(3 e)] with [zz] in [1, 8) from the bits of [x] and
    returns [None] or a double-double [(h, l)] with [h = RN (h + l)]
    within 2^-65 of [Rcbrt |x| 2^-e], for [e] in [-358, 341]
    ([fast_cbrt_correct], from [cbrt_split_bits] and [cbrt_zz_rr] of
    [FastCbrtReduce.v] and [cbrt_step_correct] of [FastCbrtStep.v]).
    [DyadicRoot.fast_cbrt_dir] and [DyadicRoot.fast_cbrt_near] then
    round it with [Fast.round_dir_err] and [Fast.round_near_err], and put
    the sign back ([fast_cbrt_dir_correct], [fast_cbrt_near_correct]).
    Where the directed test fails, [DyadicRoot.cbrt_exact] returns
    [h 2^e] only where its cube is [|x|] ([cbrt_exact_correct]). With
    an FMA they return the same ([fast_cbrt_dir_fma],
    [fast_cbrt_near_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Fushimi Require Import Model Elementary TwoSum DyDriver NearF64 FastCbrtStep.
From Fushimi Require Import FastCbrtReduce.
From Fushimi Require FastRoundErr FastSign RoundOpp NearCells RootReal Encoding.
From Fushimi Require FastRound DyExpRules DyPowRules.

Open Scope R_scope.

(** [err_cbrt], [0x3be0000000000000], is 2^-65. *)
Local Lemma err_cbrt_R : B2R DyadicRoot.err_cbrt = bpow radix2 (-65).
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicRoot.err_cbrt) with (SpecFloat.S754_finite false 4503599627370496 (-117))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Local Lemma scale_back : forall y e, y = y * bpow radix2 (- e) * bpow radix2 e.
Proof.
intros y e. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l.
change (bpow radix2 0) with 1. ring.
Qed.

Theorem fast_cbrt_correct :
  forall fma x h l e,
  is_finite x = true -> B2R x <> 0 ->
  DyadicRoot.fast_cbrt fma x = Some (h, l, e) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-358 <= e <= 341)%Z /\
  Rabs (Rcbrt (Rabs (B2R x)) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (-65).
Proof.
intros fma x h l e Fx Hx0 H.
unfold DyadicRoot.fast_cbrt in H. cbv beta zeta in H.
lazymatch type of H with
| (match ?P with pair _ _ => _ end) = _ => destruct P as [m e0] eqn:EP
end.
cbv beta iota in H.
destruct (cbrt_split_bits x m e0 Fx Hx0 EP) as (Hm & He0 & Hax).
assert (HD : (e0 + 3072 = 3 * ((e0 + 3072) / 3) + (e0 + 3072) mod 3)%Z)
  by (apply Z.div_mod; lia).
assert (HM : (0 <= (e0 + 3072) mod 3 < 3)%Z) by (apply Z.mod_pos_bound; lia).
set (et := ((e0 + 3072) / 3)%Z) in *.
set (i := ((e0 + 3072) mod 3)%Z) in *.
assert (Hi : (0 <= i <= 2)%Z) by lia.
pose proof (cbrt_zz_rr m i Hm Hi) as HZ. cbv zeta in HZ.
destruct HZ as (Fzz & Ezz & Hzz & Frr & Hrr).
lazymatch type of H with
| (match DyadicRoot.cbrt_step ?f ?y ?z ?r with Some _ => _ | None => _ end) = _ =>
  destruct (DyadicRoot.cbrt_step f y z r) as [[h' l']|] eqn:ES; [|discriminate H]
end.
injection H as Eh El Ee. subst h' l' e.
destruct (cbrt_step_correct fma _ _ _ h l Fzz Frr Hzz Hrr ES) as (Fh & Fl & Ehl & Hb).
set (zz := from_bits (Z.lor m 0x3ff0000000000000 + Z.shiftl i 52)%Z) in *.
split; [exact Fh | split; [exact Fl | split; [exact Ehl | split; [lia |]]]].
(* [|x| = (2^52 + m) 2^(e0 - 1075)] and [zz = (2^52 + m) 2^(i - 52)] with
   [e0 + 3072 = 3 et + i], so [|x| = zz 2^(3 (et - 1365))]. *)
assert (HX : Rabs (B2R x) = B2R zz * bpow radix2 (3 * (et - 1365))).
{ rewrite Hax, Ezz, Rmult_assoc, <- bpow_plus.
  replace (i - 52 + 3 * (et - 1365))%Z with (e0 - 1075)%Z by lia. reflexivity. }
(* So the cube root of [|x|] is that of [zz] times [2^(et - 1365)]. *)
assert (HC : Rcbrt (Rabs (B2R x)) = Rcbrt (B2R zz) * bpow radix2 (et - 1365)).
{ apply RootReal.Rcbrt_unique. rewrite HX.
  pose proof (RootReal.Rcbrt_cube (B2R zz)) as Hc.
  set (k := (et - 1365)%Z).
  replace (3 * k)%Z with (k + k + k)%Z by ring.
  rewrite !bpow_plus.
  set (c := Rcbrt (B2R zz)) in *. set (b := bpow radix2 k).
  rewrite <- Hc. ring. }
rewrite HC, Rmult_assoc, <- bpow_plus, Z.add_opp_diag_r.
change (bpow radix2 0) with 1. rewrite Rmult_1_r. exact Hb.
Qed.

(** [Rcbrt |x| 2^-e = Rcbrt zz] is in [1, 2), as [zz] is in [1, 8). *)
Local Lemma fast_cbrt_range :
  forall fma x h l e,
  is_finite x = true -> B2R x <> 0 ->
  DyadicRoot.fast_cbrt fma x = Some (h, l, e) ->
  1 <= Rcbrt (Rabs (B2R x)) * bpow radix2 (- e) < 2.
Proof.
intros fma x h l e Fx Hx0 H.
(* The opening of [fast_cbrt_correct], up to [HC]. *)
unfold DyadicRoot.fast_cbrt in H. cbv beta zeta in H.
lazymatch type of H with
| (match ?P with pair _ _ => _ end) = _ => destruct P as [m e0] eqn:EP
end.
cbv beta iota in H.
destruct (cbrt_split_bits x m e0 Fx Hx0 EP) as (Hm & He0 & Hax).
assert (HD : (e0 + 3072 = 3 * ((e0 + 3072) / 3) + (e0 + 3072) mod 3)%Z)
  by (apply Z.div_mod; lia).
assert (HM : (0 <= (e0 + 3072) mod 3 < 3)%Z) by (apply Z.mod_pos_bound; lia).
set (et := ((e0 + 3072) / 3)%Z) in *.
set (i := ((e0 + 3072) mod 3)%Z) in *.
assert (Hi : (0 <= i <= 2)%Z) by lia.
pose proof (cbrt_zz_rr m i Hm Hi) as HZ. cbv zeta in HZ.
destruct HZ as (_ & Ezz & Hzz & _).
lazymatch type of H with
| (match DyadicRoot.cbrt_step ?f ?y ?z ?r with Some _ => _ | None => _ end) = _ =>
  destruct (DyadicRoot.cbrt_step f y z r) as [[h' l']|] eqn:ES; [|discriminate H]
end.
injection H as Eh El Ee. subst h' l' e.
set (zz := from_bits (Z.lor m 0x3ff0000000000000 + Z.shiftl i 52)%Z) in *.
assert (HX : Rabs (B2R x) = B2R zz * bpow radix2 (3 * (et - 1365))).
{ rewrite Hax, Ezz, Rmult_assoc, <- bpow_plus.
  replace (i - 52 + 3 * (et - 1365))%Z with (e0 - 1075)%Z by lia. reflexivity. }
assert (HC : Rcbrt (Rabs (B2R x)) = Rcbrt (B2R zz) * bpow radix2 (et - 1365)).
{ apply RootReal.Rcbrt_unique. rewrite HX.
  pose proof (RootReal.Rcbrt_cube (B2R zz)) as Hc.
  set (k := (et - 1365)%Z).
  replace (3 * k)%Z with (k + k + k)%Z by ring.
  rewrite !bpow_plus.
  set (c := Rcbrt (B2R zz)) in *. set (b := bpow radix2 k).
  rewrite <- Hc. ring. }
rewrite HC, Rmult_assoc, <- bpow_plus, Z.add_opp_diag_r.
change (bpow radix2 0) with 1. rewrite Rmult_1_r.
(* [Rcbrt] is increasing, with [Rcbrt 1 = 1] and [Rcbrt 8 = 2]. *)
assert (C1 : Rcbrt 1 = 1) by (apply RootReal.Rcbrt_unique; ring).
assert (C8 : Rcbrt 8 = 2) by (apply RootReal.Rcbrt_unique; ring).
split.
- destruct (Rle_lt_or_eq_dec 1 (B2R zz) (proj1 Hzz)) as [L|E].
  + rewrite <- C1 at 1. left. apply RootReal.Rcbrt_lt. exact L.
  + rewrite <- E, C1. lra.
- rewrite <- C8. apply RootReal.Rcbrt_lt. lra.
Qed.

Theorem cbrt_exact_correct :
  forall fma x h l e c,
  is_finite x = true -> B2R x <> 0 ->
  DyadicRoot.fast_cbrt fma x = Some (h, l, e) ->
  DyadicRoot.cbrt_exact x h e = Some c ->
  is_finite c = true /\ B2R c = Rcbrt (Rabs (B2R x)).
Proof.
intros fma x h l e c Fx Hx0 H C.
destruct (fast_cbrt_correct fma x h l e Fx Hx0 H) as (Fh & _ & Ehl & He & Hb).
pose proof (fast_cbrt_range fma x h l e Fx Hx0 H) as Hr.
unfold DyadicRoot.cbrt_exact in C.
(* The test of the low bits of [h] is only a filter: soundness needs
   only the test of the odd parts. *)
destruct (Z.land (to_bits h) (2 ^ 35 - 1) =? 0)%Z; [|discriminate C].
destruct (DyadicPow.odd_parts h) as [mh eh] eqn:Oh.
destruct (DyadicPow.odd_parts x) as [mx ex] eqn:Ox.
destruct ((mh * mh * mh =? mx) && (3 * (eh + e) =? ex))%Z eqn:T; [|discriminate C].
injection C as <-.
apply andb_prop in T. destruct T as [T1 T2].
apply Z.eqb_eq in T1. apply Z.eqb_eq in T2.
(* [h >= 1/2]: [h + l] is within 2^-65 of [Rcbrt |x| 2^-e >= 1], and
   [h = RN (h + l)] with [RN] monotone. *)
assert (Hh : / 2 <= B2R h).
{ rewrite Ehl. apply round_ge_generic; [typeclasses eauto .. | |].
  - change (/ 2) with (bpow radix2 (-1)). apply generic_format_bpow.
    unfold FLT_exp. lia.
  - assert (HE : bpow radix2 (-65) <= / 4) by (cbn [bpow radix_val radix2]; lra).
    apply Rabs_le_inv in Hb. lra. }
(* [|h| = mh 2^eh] and [|x| = mx 2^ex] with [mh^3 = mx] and
   [3 (eh + e) = ex], so [(h 2^e)^3 = |x|]. *)
destruct (DyPowRules.odd_parts_spec h mh eh Fh ltac:(lra) Oh) as (_ & _ & _ & Rh).
destruct (DyPowRules.odd_parts_spec x mx ex Fx Hx0 Ox) as (_ & _ & _ & Rx).
rewrite Rabs_pos_eq in Rh by lra.
assert (HE : Rcbrt (Rabs (B2R x)) = B2R h * bpow radix2 e).
{ apply RootReal.Rcbrt_unique.
  rewrite Rx, Rh, <- T1, <- T2, !mult_IZR.
  replace (3 * (eh + e))%Z with (eh + e + (eh + e) + (eh + e))%Z by ring.
  rewrite !bpow_plus. ring. }
(* So [h = Rcbrt |x| 2^-e < 2], and [scale] is exact. *)
assert (Hh2 : B2R h < 2).
{ rewrite HE, Rmult_assoc, <- bpow_plus, Z.add_opp_diag_r in Hr.
  change (bpow radix2 0) with 1 in Hr. rewrite Rmult_1_r in Hr. lra. }
destruct (FastRound.scale_correct h e Fh ltac:(lra) ltac:(lia)) as (Fs & Rs).
split; [exact Fs |]. rewrite Rs. symmetry. exact HE.
Qed.

(** [r] rounded in the direction [up != (x < 0)] at [Rcbrt |x|], with the
    sign of [x] put back, is [Rcbrt x] rounded in the direction [up]. *)
Local Lemma cbrt_sign_dir :
  forall x up r,
  is_finite x = true ->
  rounds (xorb up (lt x zero)) (Rcbrt (Rabs (B2R x))) r ->
  rounds up (Rcbrt (B2R x)) (if lt x zero then opp r else r).
Proof.
intros x up r Fx Hr.
pose proof (FastSign.lt_zero_R x Fx) as Hs.
destruct (lt x zero).
- (* [x < 0]: [cbrt x = - cbrt (-x)], rounded the other way. *)
  rewrite Rabs_left in Hr by exact Hs.
  rewrite RootReal.Rcbrt_opp in Hr.
  replace (xorb up true) with (negb up) in Hr by (destruct up; reflexivity).
  apply RoundOpp.pown_rnd_opp. exact Hr.
- rewrite Rabs_pos_eq in Hr by exact Hs.
  replace (xorb up false) with up in Hr by (destruct up; reflexivity).
  exact Hr.
Qed.

Theorem fast_cbrt_dir_correct :
  forall fma x up v,
  is_finite x = true -> B2R x <> 0 ->
  DyadicRoot.fast_cbrt_dir fma x up = Some v ->
  rounds up (Rcbrt (B2R x)) v.
Proof.
intros fma x up v Fx Hx0 H.
unfold DyadicRoot.fast_cbrt_dir in H.
destruct (DyadicRoot.fast_cbrt fma x) as [[[h l] e]|] eqn:E; [|discriminate H].
destruct (fast_cbrt_correct fma x h l e Fx Hx0 E) as (Fh & Fl & Ehl & He & Hb).
destruct (Fast.round_dir_err h l e DyadicRoot.err_cbrt (xorb up (lt x zero))) as [r|] eqn:R;
  cbv beta iota in H.
- (* The rounding test passes. *)
  injection H as <-.
  assert (He' : (-1021 <= e <= 1022)%Z) by lia.
  assert (Hp : (55 <= 65 <= 105)%Z) by lia.
  pose proof (FastRoundErr.round_dir_err_correct h l e DyadicRoot.err_cbrt 65 _ r _
                Fh Fl Ehl He' Hp err_cbrt_R Hb R) as Hr.
  rewrite <- scale_back in Hr.
  exact (cbrt_sign_dir x up r Fx Hr).
- (* It fails, and [cbrt_exact] finds that [cbrt |x|] is an [f64]. *)
  destruct (DyadicRoot.cbrt_exact x h e) as [r|] eqn:C; [|discriminate H].
  injection H as <-.
  destruct (cbrt_exact_correct fma x h l e r Fx Hx0 E C) as (Fr & Rr).
  apply cbrt_sign_dir; [exact Fx |].
  unfold rounds. exact (DyExpRules.rnd_exact r _ _ Fr Rr).
Qed.

Theorem fast_cbrt_near_correct :
  forall fma x v,
  is_finite x = true -> B2R x <> 0 ->
  DyadicRoot.fast_cbrt_near fma x = Some v ->
  near_round (Rcbrt (B2R x)) v.
Proof.
intros fma x v Fx Hx0 H.
unfold DyadicRoot.fast_cbrt_near in H.
destruct (DyadicRoot.fast_cbrt fma x) as [[[h l] e]|] eqn:E; [|discriminate H].
destruct (Fast.round_near_err h l e DyadicRoot.err_cbrt) as [r|] eqn:R; [|discriminate H].
injection H as <-.
destruct (fast_cbrt_correct fma x h l e Fx Hx0 E) as (Fh & Fl & Ehl & He & Hb).
assert (He' : (-1021 <= e <= 1022)%Z) by lia.
assert (Hp : (55 <= 65 <= 105)%Z) by lia.
pose proof (FastRoundErr.round_near_err_correct h l e DyadicRoot.err_cbrt 65 r _
              Fh Fl Ehl He' Hp err_cbrt_R Hb R) as Hr.
rewrite <- scale_back in Hr.
rewrite Encoding.xor_sign_eq, (Encoding.Bsign_lt_zero x Fx Hx0).
pose proof (FastSign.lt_zero_R x Fx) as Hs.
destruct (lt x zero).
- (* [x < 0]: [cbrt x = - cbrt (-x)], and rounding to nearest is odd. *)
  rewrite Rabs_left in Hr by exact Hs.
  rewrite RootReal.Rcbrt_opp in Hr.
  rewrite <- (Ropp_involutive (Rcbrt (B2R x))).
  apply NearCells.near_opp. exact Hr.
- rewrite Rabs_pos_eq in Hr by exact Hs. exact Hr.
Qed.

(** The FMA reaches [fast_cbrt] only through [cbrt_step], whose [zz] is
    in [1, 8) ([cbrt_zz_rr]), where [cbrt_step_fma] applies. *)
Local Lemma fast_cbrt_fma :
  forall x,
  is_finite x = true -> B2R x <> 0 ->
  DyadicRoot.fast_cbrt true x = DyadicRoot.fast_cbrt false x.
Proof.
intros x Fx Hx0.
unfold DyadicRoot.fast_cbrt. cbv beta zeta.
lazymatch goal with
| |- (match ?P with pair _ _ => _ end) = _ => destruct P as [m e0] eqn:EP
end.
cbv beta iota.
destruct (cbrt_split_bits x m e0 Fx Hx0 EP) as (Hm & _ & _).
assert (Hi : (0 <= (e0 + 3072) mod 3 <= 2)%Z)
  by (pose proof (Z.mod_pos_bound (e0 + 3072) 3 ltac:(lia)); lia).
pose proof (cbrt_zz_rr m _ Hm Hi) as HZ. cbv zeta in HZ.
destruct HZ as (Fzz & _ & Hzz & _).
rewrite (cbrt_step_fma _ _ _ Fzz Hzz). reflexivity.
Qed.

Theorem fast_cbrt_dir_fma :
  forall x up,
  is_finite x = true -> B2R x <> 0 ->
  DyadicRoot.fast_cbrt_dir true x up = DyadicRoot.fast_cbrt_dir false x up.
Proof.
intros x up Fx Hx0. unfold DyadicRoot.fast_cbrt_dir.
rewrite (fast_cbrt_fma x Fx Hx0). reflexivity.
Qed.

Theorem fast_cbrt_near_fma :
  forall x,
  is_finite x = true -> B2R x <> 0 ->
  DyadicRoot.fast_cbrt_near true x = DyadicRoot.fast_cbrt_near false x.
Proof.
intros x Fx Hx0. unfold DyadicRoot.fast_cbrt_near.
rewrite (fast_cbrt_fma x Fx Hx0). reflexivity.
Qed.
