(** * The fast paths of [sinh], [cosh] and [tanh]

    Where [DyadicExp.fast_sinh_dir] and the others of [Model.v] return,
    they return [sinh x], [cosh t] and [tanh x] rounded toward +inf if
    [up] and toward -inf otherwise ([fast_sinh_dir_correct] and the
    others), and rounded to nearest ([fast_sinh_near_correct] and the
    others), from the bounds of [FastHypPos.v], [FastCoshPos.v] and
    [FastTanhPos.v] and the tests of [FastRoundErr.v]. [sinh] and [tanh]
    are odd: for [x < 0] they round [f(|x|)] in the other direction and
    negate it. They return the same with and without an FMA
    ([fast_sinh_dir_fma] and the others). The theorems of [sinh] and
    [tanh] assume [|x| >= 2^-27], which their rules for a tiny [|x|]
    leave ([hyp_arg_dir] and [hyp_arg_near]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Fushimi Require Import Model Mpfr Elementary ExpReal TwoSum DyDriver NearF64 NearCells
  FastRound FastRoundErr FastDiv FastHypPos FastCoshPos FastTanhPos.
From Fushimi Require DyExp DyPown FastRoundWide Encoding.

Open Scope R_scope.

(** ** The common part *)

(** What [FastCoshPos.v] proves of [fast_cosh_pos] for [f] = [cosh]. *)
Local Definition pos_bound (f : R -> R) (pos : f64 -> option (f64 * f64 * Z * f64)) : Prop :=
  forall t h l e err,
  is_finite t = true -> 0 <= B2R t -> pos t = Some (h, l, e, err) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e <= 1023)%Z /\
  exists p, (55 <= p <= 105)%Z /\ B2R err = bpow radix2 (- p) /\
    Rabs (f (B2R t) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (- p).

(** What [FastHypPos.v] and [FastTanhPos.v] prove of [fast_sinh_pos]
    and [fast_tanh_pos] for [f] = [sinh] and [tanh]: [pos_bound] for
    [t >= 2^-27]. *)
Local Definition odd_bound (f : R -> R) (pos : f64 -> option (f64 * f64 * Z * f64)) : Prop :=
  forall t h l e err,
  is_finite t = true -> 0 <= B2R t -> bpow radix2 (-27) <= B2R t ->
  pos t = Some (h, l, e, err) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e <= 1023)%Z /\
  exists p, (55 <= p <= 105)%Z /\ B2R err = bpow radix2 (- p) /\
    Rabs (f (B2R t) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (- p).

(** [fast_tanh_pos_correct] bounds [e] by [1022], within [odd_bound]. *)
Local Lemma tanh_bound : forall fma, odd_bound tanh (DyadicExp.fast_tanh_pos fma).
Proof.
intros fma t h l e err Ft Ht H27 E.
destruct (fast_tanh_pos_correct fma t h l e err Ft Ht H27 E) as (Fh & Fl & Eh & He & R).
refine (conj Fh (conj Fl (conj Eh (conj _ R)))). lia.
Qed.

Local Lemma fabs_facts :
  forall x, is_finite x = true ->
  is_finite (fabs x) = true /\ B2R (fabs x) = Rabs (B2R x) /\ 0 <= B2R (fabs x).
Proof.
intros x Fx. unfold fabs. rewrite is_finite_Babs, B2R_Babs.
split; [exact Fx | split; [reflexivity | apply Rabs_pos]].
Qed.

Local Lemma scale_back : forall y e, y = y * bpow radix2 (- e) * bpow radix2 e.
Proof.
intros y e. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l.
change (bpow radix2 0) with 1. ring.
Qed.

(** For [t >= 0], the tests of [FastRoundErr.v] on the bound of [f(t)]. *)
Local Lemma pos_dir :
  forall f pos t up v,
  pos_bound f pos -> is_finite t = true -> 0 <= B2R t ->
  match pos t with
  | Some (h, l, e, err) => Fast.round_dir_err h l e err up
  | None => None
  end = Some v ->
  rounds up (f (B2R t)) v.
Proof.
intros f pos t up v P Ft Ht H.
destruct (pos t) as [[[[h l] e] err]|] eqn:E; [|discriminate H].
destruct (P t h l e err Ft Ht E) as (Fh & Fl & Eh & He & p & Hp & Herr & Hb).
rewrite (scale_back (f (B2R t)) e).
exact (FastRoundWide.round_dir_err_wide_correct h l e err p up v _ Fh Fl Eh He Hp Herr Hb H).
Qed.

Local Lemma pos_near :
  forall f pos t v,
  pos_bound f pos -> is_finite t = true -> 0 <= B2R t ->
  match pos t with
  | Some (h, l, e, err) => Fast.round_near_err h l e err
  | None => None
  end = Some v ->
  near_round (f (B2R t)) v.
Proof.
intros f pos t v P Ft Ht H.
destruct (pos t) as [[[[h l] e] err]|] eqn:E; [|discriminate H].
destruct (P t h l e err Ft Ht E) as (Fh & Fl & Eh & He & p & Hp & Herr & Hb).
rewrite (scale_back (f (B2R t)) e).
exact (FastRoundWide.round_near_err_wide_correct h l e err p v _ Fh Fl Eh He Hp Herr Hb H).
Qed.

(** An odd [f] at [x < 0] is [-f(|x|)]: rounding [f(|x|)] in the other
    direction and negating it rounds [f(x)] ([DyPown.rounds_odd]). The
    direction and the negation take the sign bit of [x], which is the test
    [x < 0] as [x <> 0] here ([Encoding.Bsign_lt_zero]), and
    [Fast.xor_sign r x] negates [r] where it is set
    ([Encoding.xor_sign_eq]). [f(|x|)] is rounded as in [pos_dir] and
    [pos_near], from [odd_bound] at [|x| >= 2^-27]. *)
Local Lemma odd_dir :
  forall f pos x up v,
  odd_bound f pos -> (forall r, f (- r) = - f r) -> is_finite x = true ->
  bpow radix2 (-27) <= Rabs (B2R x) ->
  match pos (fabs x) with
  | Some (h, l, e, err) =>
    match Fast.round_dir_err h l e err (xorb up (Bsign x)) with
    | Some r => Some (Fast.xor_sign r x)
    | None => None
    end
  | None => None
  end = Some v ->
  rounds up (f (B2R x)) v.
Proof.
intros f pos x up v P O Fx Hx H.
assert (Hs : Bsign x = lt x zero).
{ apply Encoding.Bsign_lt_zero; [exact Fx |]. intros Hz.
  rewrite Hz, Rabs_R0 in Hx. pose proof (bpow_gt_0 radix2 (-27)). lra. }
destruct (fabs_facts x Fx) as (Ft & Et & Ht). rewrite <- Et in Hx.
destruct (pos (fabs x)) as [[[[h l] e] err]|] eqn:E; [|discriminate H].
rewrite Hs in H.
destruct (Fast.round_dir_err h l e err (xorb up (lt x zero))) as [r|] eqn:R; [|discriminate H].
rewrite Encoding.xor_sign_eq, Hs in H.
injection H as <-.
assert (Hr : rounds (xorb up (lt x zero)) (f (B2R (fabs x))) r).
{ destruct (P (fabs x) h l e err Ft Ht Hx E) as (Fh & Fl & Eh & He & p & Hp & Herr & Hb).
  rewrite (scale_back (f (B2R (fabs x))) e).
  exact (FastRoundWide.round_dir_err_wide_correct h l e err p _ r _ Fh Fl Eh He Hp Herr Hb R). }
rewrite Et in Hr.
destruct (DyExp.lt_zero_spec x) as (N1 & N2).
destruct (lt x zero) eqn:L.
- rewrite Rabs_left1 in Hr by (apply N1; reflexivity).
  rewrite O, Bool.xorb_true_r in Hr.
  exact (DyPown.rounds_odd up (f (B2R x)) r Hr).
- rewrite Rabs_pos_eq in Hr by (apply N2; reflexivity).
  rewrite Bool.xorb_false_r in Hr. exact Hr.
Qed.

Local Lemma odd_near :
  forall f pos x v,
  odd_bound f pos -> (forall r, f (- r) = - f r) -> is_finite x = true ->
  bpow radix2 (-27) <= Rabs (B2R x) ->
  match pos (fabs x) with
  | Some (h, l, e, err) =>
    match Fast.round_near_err h l e err with
    | Some r => Some (Fast.xor_sign r x)
    | None => None
    end
  | None => None
  end = Some v ->
  near_round (f (B2R x)) v.
Proof.
intros f pos x v P O Fx Hx H.
assert (Hs : Bsign x = lt x zero).
{ apply Encoding.Bsign_lt_zero; [exact Fx |]. intros Hz.
  rewrite Hz, Rabs_R0 in Hx. pose proof (bpow_gt_0 radix2 (-27)). lra. }
destruct (fabs_facts x Fx) as (Ft & Et & Ht). rewrite <- Et in Hx.
destruct (pos (fabs x)) as [[[[h l] e] err]|] eqn:E; [|discriminate H].
destruct (Fast.round_near_err h l e err) as [r|] eqn:R; [|discriminate H].
rewrite Encoding.xor_sign_eq, Hs in H.
injection H as <-.
assert (Hr : near_round (f (B2R (fabs x))) r).
{ destruct (P (fabs x) h l e err Ft Ht Hx E) as (Fh & Fl & Eh & He & p & Hp & Herr & Hb).
  rewrite (scale_back (f (B2R (fabs x))) e).
  exact (FastRoundWide.round_near_err_wide_correct h l e err p r _ Fh Fl Eh He Hp Herr Hb R). }
rewrite Et in Hr.
destruct (DyExp.lt_zero_spec x) as (N1 & N2).
destruct (lt x zero) eqn:L.
- rewrite Rabs_left1, O in Hr by (apply N1; reflexivity).
  rewrite <- (Ropp_involutive (f (B2R x))).
  exact (near_opp _ r Hr).
- rewrite Rabs_pos_eq in Hr by (apply N2; reflexivity). exact Hr.
Qed.

(** [sinh] is odd ([tanh_odd] of [ExpReal.v] is [tanh]'s). *)
Local Lemma sinh_odd : forall r, sinh (- r) = - sinh r.
Proof. intros r. unfold sinh. rewrite Ropp_involutive. field. Qed.

(** ** The arguments that reach the fast paths of [sinh] and [tanh] *)

(** The rules for a tiny [|x|] of [sinh] and [tanh] leave [|x| >= 2^-26]
    before the fast paths rounded toward +inf or -inf, and [|x| >= 2^-27]
    before those rounded to nearest: the bound [2^-27 <= |x|] that the
    theorems below assume. *)
Lemma hyp_arg_dir :
  forall x, is_finite x = true -> lt (fabs x) DyadicExp.tiny_hyp = false ->
  bpow radix2 (-27) <= Rabs (B2R x).
Proof.
intros x Fx G. destruct (fabs_facts x Fx) as (Ft & Et & _).
assert (L : is_finite DyadicExp.tiny_hyp = true /\ B2R DyadicExp.tiny_hyp = bpow radix2 (-26))
  by exact (pow2_bits (-26) ltac:(lia)).
destruct L as (Fh & Eh).
pose proof (FastHypPos.lt_false _ _ Ft Fh G) as T. rewrite Eh, Et in T.
assert (bpow radix2 (-27) <= bpow radix2 (-26)) by (apply bpow_le; lia).
lra.
Qed.

Lemma hyp_arg_near :
  forall x, is_finite x = true -> lt (fabs x) DyadicExp.tiny_near = false ->
  bpow radix2 (-27) <= Rabs (B2R x).
Proof.
intros x Fx G. destruct (fabs_facts x Fx) as (Ft & Et & _).
assert (Fn : is_finite DyadicExp.tiny_near = true) by (vm_compute; reflexivity).
pose proof (FastHypPos.lt_false _ _ Ft Fn G) as T. rewrite lit_tiny, Et in T.
exact T.
Qed.

(** ** Rounded toward -inf and +inf *)

Theorem fast_sinh_dir_correct :
  forall fma x up v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicExp.fast_sinh_dir fma x up = Some v ->
  rounds up (sinh (B2R x)) v.
Proof.
intros fma x up v Fx Hx H.
exact (odd_dir sinh _ x up v (fast_sinh_pos_correct fma) sinh_odd Fx Hx H).
Qed.

Theorem fast_cosh_dir_correct :
  forall fma t up v,
  is_finite t = true -> 0 <= B2R t -> DyadicExp.fast_cosh_dir fma t up = Some v ->
  rounds up (cosh (B2R t)) v.
Proof.
intros fma t up v Ft Ht H.
exact (pos_dir cosh _ t up v (fast_cosh_pos_correct fma) Ft Ht H).
Qed.

Theorem fast_tanh_dir_correct :
  forall fma x up v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicExp.fast_tanh_dir fma x up = Some v ->
  rounds up (tanh (B2R x)) v.
Proof.
intros fma x up v Fx Hx H.
exact (odd_dir tanh _ x up v (tanh_bound fma) tanh_odd Fx Hx H).
Qed.

(** ** Rounded to nearest *)

Theorem fast_sinh_near_correct :
  forall fma x v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicExp.fast_sinh_near fma x = Some v ->
  near_round (sinh (B2R x)) v.
Proof.
intros fma x v Fx Hx H.
exact (odd_near sinh _ x v (fast_sinh_pos_correct fma) sinh_odd Fx Hx H).
Qed.

Theorem fast_cosh_near_correct :
  forall fma t v,
  is_finite t = true -> 0 <= B2R t -> DyadicExp.fast_cosh_near fma t = Some v ->
  near_round (cosh (B2R t)) v.
Proof.
intros fma t v Ft Ht H.
exact (pos_near cosh _ t v (fast_cosh_pos_correct fma) Ft Ht H).
Qed.

Theorem fast_tanh_near_correct :
  forall fma x v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicExp.fast_tanh_near fma x = Some v ->
  near_round (tanh (B2R x)) v.
Proof.
intros fma x v Fx Hx H.
exact (odd_near tanh _ x v (tanh_bound fma) tanh_odd Fx Hx H).
Qed.

(** ** With and without an FMA *)

Theorem fast_sinh_dir_fma :
  forall x up,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicExp.fast_sinh_dir true x up = DyadicExp.fast_sinh_dir false x up.
Proof.
intros x up Fx Hx. destruct (fabs_facts x Fx) as (Ft & Et & Ht). rewrite <- Et in Hx.
unfold DyadicExp.fast_sinh_dir. rewrite (fast_sinh_pos_fma _ Ft Ht Hx). reflexivity.
Qed.

Theorem fast_cosh_dir_fma :
  forall t up,
  is_finite t = true -> 0 <= B2R t ->
  DyadicExp.fast_cosh_dir true t up = DyadicExp.fast_cosh_dir false t up.
Proof.
intros t up Ft Ht.
unfold DyadicExp.fast_cosh_dir. rewrite (fast_cosh_pos_fma _ Ft Ht). reflexivity.
Qed.

Theorem fast_tanh_dir_fma :
  forall x up,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicExp.fast_tanh_dir true x up = DyadicExp.fast_tanh_dir false x up.
Proof.
intros x up Fx Hx. destruct (fabs_facts x Fx) as (Ft & Et & Ht). rewrite <- Et in Hx.
unfold DyadicExp.fast_tanh_dir. rewrite (fast_tanh_pos_fma _ Ft Ht Hx). reflexivity.
Qed.

Theorem fast_sinh_near_fma :
  forall x,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicExp.fast_sinh_near true x = DyadicExp.fast_sinh_near false x.
Proof.
intros x Fx Hx. destruct (fabs_facts x Fx) as (Ft & Et & Ht). rewrite <- Et in Hx.
unfold DyadicExp.fast_sinh_near. rewrite (fast_sinh_pos_fma _ Ft Ht Hx). reflexivity.
Qed.

Theorem fast_cosh_near_fma :
  forall t,
  is_finite t = true -> 0 <= B2R t ->
  DyadicExp.fast_cosh_near true t = DyadicExp.fast_cosh_near false t.
Proof.
intros t Ft Ht.
unfold DyadicExp.fast_cosh_near. rewrite (fast_cosh_pos_fma _ Ft Ht). reflexivity.
Qed.

Theorem fast_tanh_near_fma :
  forall x,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicExp.fast_tanh_near true x = DyadicExp.fast_tanh_near false x.
Proof.
intros x Fx Hx. destruct (fabs_facts x Fx) as (Ft & Et & Ht). rewrite <- Et in Hx.
unfold DyadicExp.fast_tanh_near. rewrite (fast_tanh_pos_fma _ Ft Ht Hx). reflexivity.
Qed.
