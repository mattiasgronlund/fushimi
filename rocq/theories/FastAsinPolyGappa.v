(** * Round-off bound of the polynomial of [fast_asin_poly], by Gappa

    [DyadicAtan.fast_asin_poly] of [Model.v] evaluates [fl = c0l + tau q],
    [q = c1 + tau (c2 + tau (c3 + tau (c4 + tau (c5 + tau c6))))], by
    Horner's rule in [f64] rounded to nearest, with the coefficients of a
    row of [DyadicAtan.ASIN_TABLE]. [asin_horner_gappa] bounds its
    round-off for [|tau| <= 513 2^-18], with the coefficients as variables
    in the ranges that [FastAsinTable.asin_coef_facts] gives for every row,
    and [asin_fl_gappa] restates it for the [f64] operations of [Model.v],
    as [FastAsinPoly.v] uses it. As in [FastTrigGappa.v], the [gappa]
    tactic of coq-gappa turns Gappa's answer into a proof term that Rocq's
    kernel checks at [Qed]. *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Gappa Require Import Gappa_tactic.
From Fushimi Require Import Model TwoSum FastExpErr FastExpTables.

(* coq-gappa 1.11.0 names [Coq.Init.Logic.and] and other paths that Rocq 9
   renamed, and Rocq warns about each at every [gappa] call. The build turns
   warnings into errors ([-w +default] in [rocq/Makefile]), so this file,
   and only this file, turns the warning off, as [FastTrigGappa.v] does: a
   [Set] in a file does not reach the files that require it. *)
Set Warnings "-deprecated-dirpath-Coq".

Open Scope R_scope.

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp] in *.

Local Lemma asin_horner_gappa :
  forall tau c0l c1 c2 c3 c4 c5 c6 : R,
  Rabs tau <= 513 * bpow radix2 (-18) -> Rabs c0l <= bpow radix2 (-53) ->
  Rabs c1 <= 441 * bpow radix2 (-11) ->
  Rabs c2 <= bpow radix2 (-3) -> Rabs c3 <= bpow radix2 (-3) -> Rabs c4 <= bpow radix2 (-3) ->
  Rabs c5 <= bpow radix2 (-3) -> Rabs c6 <= bpow radix2 (-3) ->
  Rabs (RN (c0l + RN (tau * RN (c1 + RN (tau * RN (c2 + RN (tau * RN (c3 + RN (tau * RN (c4 +
          RN (tau * RN (c5 + RN (tau * c6)))))))))))) -
        (c0l + tau * (c1 + tau * (c2 + tau * (c3 + tau * (c4 + tau * (c5 + tau * c6))))))) <=
    7 * bpow radix2 (-66).
Proof. intros. gappa. Qed.

Lemma asin_fl_gappa :
  forall tau c0l c1 c2 c3 c4 c5 c6 : f64,
  is_finite tau = true -> is_finite c0l = true -> is_finite c1 = true -> is_finite c2 = true ->
  is_finite c3 = true -> is_finite c4 = true -> is_finite c5 = true -> is_finite c6 = true ->
  Rabs (B2R tau) <= / 512 + bpow radix2 (-55) -> Rabs (B2R c0l) <= bpow radix2 (-53) ->
  Rabs (B2R c1) <= 441 / 2048 -> Rabs (B2R c2) <= / 8 -> Rabs (B2R c3) <= / 8 ->
  Rabs (B2R c4) <= / 8 -> Rabs (B2R c5) <= / 8 -> Rabs (B2R c6) <= / 8 ->
  let q :=
    add c1 (mul tau (add c2 (mul tau (add c3 (mul tau (add c4 (mul tau (add c5 (mul tau c6))))))))) in
  let fl := add c0l (mul tau q) in
  is_finite fl = true /\ Rabs (B2R fl) <= 7 / 8 * bpow radix2 (-11) /\
  Rabs (B2R fl - (B2R c0l + B2R tau * (B2R c1 + B2R tau * (B2R c2 + B2R tau * (B2R c3 +
          B2R tau * (B2R c4 + B2R tau * (B2R c5 + B2R tau * B2R c6))))))) <= 7 * bpow radix2 (-66).
Proof.
intros tau c0l c1 c2 c3 c4 c5 c6 Ft F0 F1 F2 F3 F4 F5 F6 Ht H0 H1 H2 H3 H4 H5 H6. cbv zeta.
(* The bounds of [asin_horner_gappa], as dyadic numbers for Gappa (as in
   [FastTrigGappa.v]): /512 + 2^-55 <= 513 2^-18. *)
assert (Ht' : Rabs (B2R tau) <= 513 * bpow radix2 (-18)) by (num; lra).
assert (H1' : Rabs (B2R c1) <= 441 * bpow radix2 (-11)) by (num; lra).
assert (H2' : Rabs (B2R c2) <= bpow radix2 (-3)) by (num; lra).
assert (H3' : Rabs (B2R c3) <= bpow radix2 (-3)) by (num; lra).
assert (H4' : Rabs (B2R c4) <= bpow radix2 (-3)) by (num; lra).
assert (H5' : Rabs (B2R c5) <= bpow radix2 (-3)) by (num; lra).
assert (H6' : Rabs (B2R c6) <= bpow radix2 (-3)) by (num; lra).
clear Ht H1 H2 H3 H4 H5 H6.
(* Each step is [RN] of its exact result, which Gappa bounds by 16. *)
destruct (mul_e tau c6 Ft F6 ltac:(gappa)) as (Fp6 & Ep6 & _).
destruct (add_e c5 _ F5 Fp6 ltac:(rewrite Ep6; gappa)) as (Fs5 & Es5 & _).
destruct (mul_e tau _ Ft Fs5 ltac:(rewrite Es5, Ep6; gappa)) as (Fp5 & Ep5 & _).
destruct (add_e c4 _ F4 Fp5 ltac:(rewrite Ep5, Es5, Ep6; gappa)) as (Fs4 & Es4 & _).
destruct (mul_e tau _ Ft Fs4 ltac:(rewrite Es4, Ep5, Es5, Ep6; gappa)) as (Fp4 & Ep4 & _).
destruct (add_e c3 _ F3 Fp4 ltac:(rewrite Ep4, Es4, Ep5, Es5, Ep6; gappa)) as (Fs3 & Es3 & _).
destruct (mul_e tau _ Ft Fs3 ltac:(rewrite Es3, Ep4, Es4, Ep5, Es5, Ep6; gappa))
  as (Fp3 & Ep3 & _).
destruct (add_e c2 _ F2 Fp3 ltac:(rewrite Ep3, Es3, Ep4, Es4, Ep5, Es5, Ep6; gappa))
  as (Fs2 & Es2 & _).
destruct (mul_e tau _ Ft Fs2 ltac:(rewrite Es2, Ep3, Es3, Ep4, Es4, Ep5, Es5, Ep6; gappa))
  as (Fp2 & Ep2 & _).
destruct (add_e c1 _ F1 Fp2 ltac:(rewrite Ep2, Es2, Ep3, Es3, Ep4, Es4, Ep5, Es5, Ep6; gappa))
  as (Fq & Eq & _).
destruct (mul_e tau _ Ft Fq
  ltac:(rewrite Eq, Ep2, Es2, Ep3, Es3, Ep4, Es4, Ep5, Es5, Ep6; gappa)) as (Fp1 & Ep1 & _).
destruct (add_e c0l _ F0 Fp1
  ltac:(rewrite Ep1, Eq, Ep2, Es2, Ep3, Es3, Ep4, Es4, Ep5, Es5, Ep6; gappa))
  as (Ffl & Efl & _).
split; [exact Ffl|].
rewrite Efl, Ep1, Eq, Ep2, Es2, Ep3, Es3, Ep4, Es4, Ep5, Es5, Ep6.
split; [gappa|].
apply asin_horner_gappa; assumption.
Qed.
