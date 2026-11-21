(** * The fast path of [hypot]

    [DyadicRoot.fast_hypot] and [DyadicRoot.fast_hypot_near] take
    [big = max(|x|, |y|)] and [small = min(|x|, |y|)], return the rule of
    [FastHypotFar.v] where their biased exponents differ by 27 or more,
    and otherwise round the double-double of [hypot_dd] ([FastHypotDd.v])
    with [Fast.round_dir_err] and [Fast.round_near_err]
    ([fast_hypot_dir_correct], [fast_hypot_near_correct]). Where the
    directed test fails, [DyadicRoot.hypot_exact] returns [h 2^e] only
    where its square is [big^2 + small^2] ([hypot_exact_correct]). With
    an FMA they return the same ([fast_hypot_dir_fma],
    [fast_hypot_near_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model DyDriver NearF64 FastHypotFar FastHypotDd.
From Inari Require FastRoundErr DyExpRules DyPowRules.

Open Scope R_scope.

(** ** Lemmas *)

(** [B2R] of an [f64] literal, by computation (as in [FastExpEdge.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** [ERR_HYPOT] is 2^-98: the significand 2^52 times 2^-150. *)
Local Lemma lit_err_hypot : B2R DyadicRoot.err_hypot = bpow radix2 (-98).
Proof.
lit_B2R. change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
reflexivity.
Qed.

(** As in [FastPow.v]. *)
Local Lemma scale_back : forall y e, y = y * bpow radix2 (- e) * bpow radix2 e.
Proof.
intros y e. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l.
change (bpow radix2 0) with 1. ring.
Qed.

(** [big] and [small] as both functions order them, by [ge] of the
    absolute values as [hypot_odd] does ([DyHypotOdd.v]): finite, with
    [0 < small <= big], and with the sum of the squares of [x] and [y]. *)
Local Lemma order :
  forall x y,
  is_finite x = true -> is_finite y = true -> B2R x <> 0 -> B2R y <> 0 ->
  exists big small,
  (if ge (fabs x) (fabs y) then (fabs x, fabs y) else (fabs y, fabs x)) = (big, small) /\
  is_finite big = true /\ is_finite small = true /\ 0 < B2R small <= B2R big /\
  B2R x * B2R x + B2R y * B2R y = B2R big * B2R big + B2R small * B2R small.
Proof.
intros x y Fx Fy Hx Hy.
assert (Fax : is_finite (fabs x) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fx).
assert (Fay : is_finite (fabs y) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fy).
assert (Rx : B2R (fabs x) = Rabs (B2R x)) by (unfold fabs; apply B2R_Babs).
assert (Ry : B2R (fabs y) = Rabs (B2R y)) by (unfold fabs; apply B2R_Babs).
pose proof (Rabs_pos_lt _ Hx) as Px.
pose proof (Rabs_pos_lt _ Hy) as Py.
(* [r^2 = |r|^2]. *)
assert (Sq : forall r, r * r = Rabs r * Rabs r)
  by (intros r; unfold Rabs; destruct (Rcase_abs r); ring).
(* [ge a b] is [b <= a] for finite [a] and [b]. *)
assert (G : ge (fabs x) (fabs y) = Rle_bool (B2R (fabs y)) (B2R (fabs x)))
  by (unfold ge; apply Bleb_correct; assumption).
rewrite G.
destruct (Rle_bool_spec (B2R (fabs y)) (B2R (fabs x))) as [L | L].
- exists (fabs x), (fabs y).
  split; [reflexivity |]. split; [exact Fax |]. split; [exact Fay |].
  rewrite Rx, Ry in *. split; [lra |].
  rewrite (Sq (B2R x)), (Sq (B2R y)). reflexivity.
- exists (fabs y), (fabs x).
  split; [reflexivity |]. split; [exact Fay |]. split; [exact Fax |].
  rewrite Rx, Ry in *. split; [lra |].
  rewrite (Sq (B2R x)), (Sq (B2R y)). ring.
Qed.

(** ** The theorems *)

Theorem hypot_exact_correct :
  forall big small h e c,
  is_finite big = true -> is_finite small = true -> 0 < B2R small <= B2R big ->
  DyadicRoot.hypot_exact big small h e = Some c ->
  is_finite c = true /\ B2R c = sqrt (B2R big * B2R big + B2R small * B2R small).
Proof.
intros big small h e c Fb Fs Hbs H.
unfold DyadicRoot.hypot_exact in H. cbv zeta in H.
(* Nothing is known of [h 2^e]: the test alone decides. *)
set (c0 := Fast.scale h e) in H. clearbody c0.
assert (Hb0 : B2R big <> 0) by lra.
assert (Hs0 : B2R small <> 0) by lra.
destruct (DyadicPow.odd_parts small) as [ms es] eqn:Os.
destruct (DyadicPow.odd_parts big) as [mb eb] eqn:Ob.
destruct (DyPowRules.odd_parts_spec small ms es Fs Hs0 Os) as (_ & _ & _ & Rs).
destruct (DyPowRules.odd_parts_spec big mb eb Fb Hb0 Ob) as (_ & Hmb & _ & Rb).
destruct (is_finite c0) eqn:Fc.
- (* [ge c0 big] is [big <= c0], so [c0] is positive. *)
  unfold ge in H. rewrite Bleb_correct in H by assumption.
  destruct (Rle_bool_spec (B2R big) (B2R c0)) as [Hc | Hc]; [| discriminate H].
  assert (Hc0 : B2R c0 <> 0) by lra.
  destruct (DyadicPow.odd_parts c0) as [mc ec] eqn:Oc.
  destruct (DyPowRules.odd_parts_spec c0 mc ec Fc Hc0 Oc) as (_ & _ & _ & Rc).
  cbv beta iota in H.
  destruct (ec <=? es)%Z eqn:Tes; [| discriminate H].
  destruct (ec <=? eb)%Z eqn:Teb; [| discriminate H].
  apply Z.leb_le in Tes, Teb.
  rewrite !Z.shiftl_mul_pow2 in H by lia.
  destruct (mb * 2 ^ (eb - ec) * (mb * 2 ^ (eb - ec)) +
    ms * 2 ^ (es - ec) * (ms * 2 ^ (es - ec)) =? mc * mc)%Z eqn:Q; [| discriminate H].
  injection H as <-. split; [exact Fc |].
  (* The integer identity, read in the reals. *)
  apply Z.eqb_eq, (f_equal IZR) in Q.
  assert (P2 : forall n, (0 <= n)%Z -> IZR (2 ^ n) = bpow radix2 n)
    by (intros n Hn; exact (IZR_Zpower radix2 n Hn)).
  rewrite plus_IZR, !mult_IZR, !P2 in Q by lia.
  (* Each of [big], [small] and [c0] is its odd part times [2^ec]. *)
  set (P := bpow radix2 ec) in *.
  assert (Sp : forall m k, (ec <= k)%Z ->
    IZR m * bpow radix2 k = IZR m * bpow radix2 (k - ec) * P).
  { intros m k Hk. unfold P. rewrite Rmult_assoc, <- bpow_plus.
    replace (k - ec + ec)%Z with k by ring. reflexivity. }
  rewrite Rabs_pos_eq in Rs, Rb, Rc by lra.
  rewrite (Sp ms es Tes) in Rs. rewrite (Sp mb eb Teb) in Rb.
  assert (Sum : B2R big * B2R big + B2R small * B2R small = B2R c0 * B2R c0).
  { rewrite Rb, Rs, Rc.
    replace (IZR mc * P * (IZR mc * P)) with (IZR mc * IZR mc * (P * P)) by ring.
    rewrite <- Q. ring. }
  rewrite Sum. symmetry. apply sqrt_square. lra.
- (* [c0] is an infinity or NaN. *)
  destruct c0 as [s | s | | s m ex Hx]; try discriminate Fc.
  + destruct s.
    * (* -inf: [ge] is false, as [big] is finite. *)
      assert (G : ge (B754_infinity true) big = false)
        by (destruct big; try discriminate Fb; reflexivity).
      rewrite G in H. discriminate H.
    * (* +inf: its odd parts are [(1, 1024)], and [eb < 1024] as [big] is
         finite. *)
      destruct (ge _ big); [| discriminate H].
      replace (DyadicPow.odd_parts (B754_infinity false)) with (1, 1024)%Z in H
        by (vm_compute; reflexivity).
      cbv beta iota in H.
      destruct (1024 <=? es)%Z; [| discriminate H].
      destruct (1024 <=? eb)%Z eqn:Teb; [| discriminate H].
      apply Z.leb_le in Teb.
      exfalso.
      pose proof (abs_B2R_lt_emax _ _ big) as Lb. rewrite Rb in Lb.
      assert (M1 : 1 <= IZR mb) by (apply IZR_le; lia).
      assert (E : bpow radix2 1024 <= bpow radix2 eb) by (apply bpow_le; exact Teb).
      assert (M2 : 0 <= (IZR mb - 1) * bpow radix2 eb)
        by (apply Rmult_le_pos; [lra | apply bpow_ge_0]).
      lra.
  + (* NaN: [ge] is false. *)
    assert (G : ge B754_nan big = false) by (destruct big; reflexivity).
    rewrite G in H. discriminate H.
Qed.

Theorem fast_hypot_dir_correct :
  forall fma x y up v,
  is_finite x = true -> is_finite y = true -> B2R x <> 0 -> B2R y <> 0 ->
  DyadicRoot.fast_hypot fma x y up = Some v ->
  rounds up (sqrt (B2R x * B2R x + B2R y * B2R y)) v.
Proof.
intros fma x y up v Fx Fy Hx Hy H.
destruct (order x y Fx Fy Hx Hy) as (big & small & E & Fb & Fs & Hbs & Hsum).
rewrite Hsum.
unfold DyadicRoot.fast_hypot in H. rewrite E in H. cbv beta iota in H.
destruct (27 <=? Z.shiftr (to_bits big) 52 - Z.shiftr (to_bits small) 52)%Z eqn:G.
- (* A gap of 27 or more: the rule of [FastHypotFar.v]. *)
  injection H as <-. apply hypot_far_dir; try assumption. apply Z.leb_le. exact G.
- (* Otherwise [hypot_dd] gives [hypot(big, small) 2^-e] within 2^-98. *)
  destruct (DyadicRoot.hypot_dd fma big small) as [[[h l] e] |] eqn:D; [| discriminate H].
  apply Z.leb_gt in G.
  destruct (hypot_dd_correct fma big small h l e Fb Fs Hbs G D) as (Fh & Fl & Rh & He & Hb).
  destruct (Fast.round_dir_err h l e DyadicRoot.err_hypot up) as [r |] eqn:R;
    cbv beta iota in H.
  + (* The rounding test passes. *)
    injection H as <-.
    rewrite (scale_back (sqrt (B2R big * B2R big + B2R small * B2R small)) e).
    exact (FastRoundErr.round_dir_err_correct h l e DyadicRoot.err_hypot 98 up r _
      Fh Fl Rh He ltac:(lia) lit_err_hypot Hb R).
  + (* It fails, and [hypot_exact] finds that [hypot(big, small)] is an [f64]. *)
    destruct (hypot_exact_correct big small h e v Fb Fs Hbs H) as (Fv & Rv).
    unfold rounds. exact (DyExpRules.rnd_exact v _ _ Fv Rv).
Qed.

Theorem fast_hypot_near_correct :
  forall fma x y v,
  is_finite x = true -> is_finite y = true -> B2R x <> 0 -> B2R y <> 0 ->
  DyadicRoot.fast_hypot_near fma x y = Some v ->
  near_round (sqrt (B2R x * B2R x + B2R y * B2R y)) v.
Proof.
intros fma x y v Fx Fy Hx Hy H.
destruct (order x y Fx Fy Hx Hy) as (big & small & E & Fb & Fs & Hbs & Hsum).
rewrite Hsum.
unfold DyadicRoot.fast_hypot_near in H. rewrite E in H. cbv beta iota in H.
destruct (27 <=? Z.shiftr (to_bits big) 52 - Z.shiftr (to_bits small) 52)%Z eqn:G.
- (* A gap of 27 or more: the rule of [FastHypotFar.v]. *)
  injection H as <-. apply hypot_far_near; try assumption. apply Z.leb_le. exact G.
- (* Otherwise [hypot_dd] gives [hypot(big, small) 2^-e] within 2^-98. *)
  destruct (DyadicRoot.hypot_dd fma big small) as [[[h l] e] |] eqn:D; [| discriminate H].
  apply Z.leb_gt in G.
  destruct (hypot_dd_correct fma big small h l e Fb Fs Hbs G D) as (Fh & Fl & Rh & He & Hb).
  rewrite (scale_back (sqrt (B2R big * B2R big + B2R small * B2R small)) e).
  exact (FastRoundErr.round_near_err_correct h l e DyadicRoot.err_hypot 98 v _
    Fh Fl Rh He ltac:(lia) lit_err_hypot Hb H).
Qed.

Theorem fast_hypot_dir_fma :
  forall x y up,
  is_finite x = true -> is_finite y = true -> B2R x <> 0 -> B2R y <> 0 ->
  DyadicRoot.fast_hypot true x y up = DyadicRoot.fast_hypot false x y up.
Proof.
intros x y up Fx Fy Hx Hy.
destruct (order x y Fx Fy Hx Hy) as (big & small & E & Fb & Fs & Hbs & _).
unfold DyadicRoot.fast_hypot. rewrite E. cbv beta iota.
(* Only [hypot_dd] depends on the FMA, and the gap of 27 or more skips it. *)
destruct (27 <=? Z.shiftr (to_bits big) 52 - Z.shiftr (to_bits small) 52)%Z eqn:G;
  [reflexivity |].
apply Z.leb_gt in G. rewrite (hypot_dd_fma big small Fb Fs Hbs G). reflexivity.
Qed.

Theorem fast_hypot_near_fma :
  forall x y,
  is_finite x = true -> is_finite y = true -> B2R x <> 0 -> B2R y <> 0 ->
  DyadicRoot.fast_hypot_near true x y = DyadicRoot.fast_hypot_near false x y.
Proof.
intros x y Fx Fy Hx Hy.
destruct (order x y Fx Fy Hx Hy) as (big & small & E & Fb & Fs & Hbs & _).
unfold DyadicRoot.fast_hypot_near. rewrite E. cbv beta iota.
(* Only [hypot_dd] depends on the FMA, and the gap of 27 or more skips it. *)
destruct (27 <=? Z.shiftr (to_bits big) 52 - Z.shiftr (to_bits small) 52)%Z eqn:G;
  [reflexivity |].
apply Z.leb_gt in G. rewrite (hypot_dd_fma big small Fb Fs Hbs G). reflexivity.
Qed.
