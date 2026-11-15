(** * The table of stage 0 of [asin] and [acos]

    Row [j] of [DyadicAtan.ASIN_TABLE] of [Model.v], for [j = 0, ..., 64],
    holds [c0h + c0l] and [c1, ..., c6], so that [asin_table_poly j tau]
    is a polynomial of degree 6 in [tau]. [asin_table_close] bounds its
    distance to [AsinSeries.asin_poly 34] at [j / 256 + tau] for [|tau| <=
    2^-9 + 2^-55], and [asin_coef_facts] gives the ranges of its
    coefficients, which [FastAsinPolyGappa.v] and [FastAsinPoly.v] take. *)

From Stdlib Require Import ZArith Reals Lra Lia List Bool.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model TwoSum AsinSeries FastExpTables.

Import ListNotations.

Open Scope R_scope.

(** ** Polynomials with integer coefficients

    The checks below evaluate polynomials whose coefficients are
    integers, so that [vm_compute] decides them exactly without [Q],
    whose gcds ([Qred]) would be too slow at these sizes. *)

(** [zeval [a0; a1; ...] x = a0 + x (a1 + x (...))] *)
Local Fixpoint zeval (l : list Z) (x : R) : R :=
  match l with
  | [] => 0
  | a :: l => IZR a + x * zeval l x
  end.

Local Lemma zeval_app :
  forall l1 l2 x, zeval (l1 ++ l2) x = zeval l1 x + x ^ length l1 * zeval l2 x.
Proof.
intros l1 l2 x. induction l1 as [|a l1 IH]; cbn [app zeval length pow]; [ring|].
rewrite IH. ring.
Qed.

Local Lemma zeval_scale :
  forall c l x, zeval (map (Z.mul c) l) x = IZR c * zeval l x.
Proof.
intros c l x. induction l as [|a l IH]; cbn [map zeval]; [ring|].
rewrite mult_IZR, IH. ring.
Qed.

Local Lemma zeval_opp : forall l x, zeval (map Z.opp l) x = - zeval l x.
Proof.
intros l x. induction l as [|a l IH]; cbn [map zeval]; [ring|].
rewrite opp_IZR, IH. ring.
Qed.

(** [zsub l1 l2] is [l1 - l2]. *)
Local Fixpoint zsub (l1 l2 : list Z) : list Z :=
  match l1, l2 with
  | [], _ => map Z.opp l2
  | _, [] => l1
  | a :: l1, b :: l2 => (a - b)%Z :: zsub l1 l2
  end.

Local Lemma zeval_sub :
  forall l1 l2 x, zeval (zsub l1 l2) x = zeval l1 x - zeval l2 x.
Proof.
intros l1. induction l1 as [|a l1 IH]; intros [|b l2] x; cbn [zsub zeval].
- cbn [map zeval]. ring.
- rewrite zeval_opp. cbn [zeval]. ring.
- ring.
- rewrite minus_IZR, IH. ring.
Qed.

(** [zlin a c q] is [a + (c + u) q(u)] as a polynomial in [u]. *)
Local Fixpoint zlin (a c : Z) (q : list Z) : list Z :=
  match q with
  | [] => [a]
  | q0 :: q => (a + c * q0)%Z :: zlin q0 c q
  end.

Local Lemma zeval_lin :
  forall q a c u, zeval (zlin a c q) u = IZR a + (IZR c + u) * zeval q u.
Proof.
intros q. induction q as [|q0 q IH]; intros a c u; cbn [zlin zeval].
- ring.
- rewrite IH, plus_IZR, mult_IZR. ring.
Qed.

(** [zshift c l] is [l(c + u)] as a polynomial in [u] (Horner's
    scheme, each step a [zlin]). *)
Local Fixpoint zshift (c : Z) (l : list Z) : list Z :=
  match l with
  | [] => []
  | a :: l => zlin a c (zshift c l)
  end.

Local Lemma zeval_shift : forall c l u, zeval (zshift c l) u = zeval l (IZR c + u).
Proof.
intros c l u. induction l as [|a l IH]; cbn [zshift zeval]; [reflexivity|].
rewrite zeval_lin, IH. reflexivity.
Qed.

(** [zmp b l] is [l(b u)] as a polynomial in [u]. *)
Local Fixpoint zmp (b : Z) (l : list Z) : list Z :=
  match l with
  | [] => []
  | a :: l => a :: map (Z.mul b) (zmp b l)
  end.

Local Lemma zeval_mp : forall b l u, zeval (zmp b l) u = zeval l (IZR b * u).
Proof.
intros b l u. induction l as [|a l IH]; cbn [zmp zeval]; [reflexivity|].
rewrite zeval_scale, IH. ring.
Qed.

(** For [|x| <= r], [|l(x)|] is at most [l] with its coefficients'
    absolute values at [r]. *)
Local Lemma zeval_abs :
  forall l x r, Rabs x <= r -> Rabs (zeval l x) <= zeval (map Z.abs l) r.
Proof.
intros l x r Hx.
induction l as [|a l IH]; cbn [map zeval].
- rewrite Rabs_R0. lra.
- eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_mult, abs_IZR.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hx | exact IH].
Qed.

(** [znum l r d = d^n l(r / d)], an integer, for [n] the length of [l] *)
Local Fixpoint znum (l : list Z) (r d : Z) : Z :=
  match l with
  | [] => 0
  | a :: l => (d ^ Z.of_nat (S (length l)) * a + r * znum l r d)%Z
  end.

Local Lemma zeval_num :
  forall l r d, (0 < d)%Z -> zeval l (IZR r / IZR d) * IZR d ^ length l = IZR (znum l r d).
Proof.
intros l r d Hd. assert (HD : IZR d <> 0) by (apply not_0_IZR; lia).
induction l as [|a l IH]; cbn [zeval znum length]; [ring|].
rewrite plus_IZR, !mult_IZR, <- pow_IZR, <- IH. cbn [pow]. field. exact HD.
Qed.

(** ** [asin_poly 34] as an integer polynomial *)

(** [bz n = (p, q)] with [b_n = p / q] *)
Local Fixpoint bz (n : nat) : Z * Z :=
  match n with
  | O => (1, 1)%Z
  | S k => let '(p, q) := bz k in (p * (2 * Z.of_nat k + 1), q * (2 * Z.of_nat k + 2))%Z
  end.

Local Lemma bz_correct :
  forall n, (0 < snd (bz n))%Z /\ IZR (fst (bz n)) / IZR (snd (bz n)) = asin_b n.
Proof.
intros n. induction n as [|k [Hq IH]]; cbn [bz asin_b].
- cbn [fst snd]. split; [lia | field].
- destruct (bz k) as [p q]. cbn [fst snd] in *.
  pose proof (pos_INR k) as Hk.
  assert (Hq' : IZR q <> 0) by (apply not_0_IZR; lia).
  split; [apply Z.mul_pos_pos; lia|].
  rewrite <- IH, !mult_IZR, !plus_IZR, !mult_IZR, <- INR_IZR_INZ.
  field. lra.
Qed.

(** [asin_S = 2^330 lcm(1, 3, ..., 67)] clears the denominators of
    [a_n / 256^n = binom(2n, n) / (2^(10 n) (2n + 1))] for [n < 34]. *)
Local Definition asin_S : Z :=
  (2 ^ 330 * fold_right Z.lcm 1 (map (fun k => 2 * Z.of_nat k + 1) (seq 0 34)))%Z.

(** The denominator of [a_n / 256^n] for [bz n = (p, q)] *)
Local Definition gden (n : nat) : Z :=
  (snd (bz n) * (2 * Z.of_nat n + 1) * 256 ^ Z.of_nat n)%Z.

(** [S a_n / 256^n], if [S] clears its denominator ([gexact]) *)
Local Definition gcoef (S : Z) (n : nat) : Z := (S * fst (bz n) / gden n)%Z.

Local Definition gexact (S : Z) (n : nat) : bool := ((S * fst (bz n)) mod gden n =? 0)%Z.

Local Lemma gcoef_correct :
  forall S n, gexact S n = true -> IZR S * asin_a n = IZR (gcoef S n) * 256 ^ n.
Proof.
intros S n H. unfold gexact, gcoef, gden, asin_a in *.
destruct (bz_correct n) as [Hq Hb]. rewrite <- Hb.
destruct (bz n) as [p q]. cbn [fst snd] in *.
assert (Hd : (q * (2 * Z.of_nat n + 1) * 256 ^ Z.of_nat n <> 0)%Z).
{ assert (0 < 256 ^ Z.of_nat n)%Z by (apply Z.pow_pos_nonneg; lia). nia. }
apply Z.eqb_eq, (Z.div_exact _ _ Hd) in H.
set (g := (S * p / (q * (2 * Z.of_nat n + 1) * 256 ^ Z.of_nat n))%Z) in *.
apply (f_equal IZR) in H.
rewrite !mult_IZR, plus_IZR, mult_IZR, <- pow_IZR, <- INR_IZR_INZ in H.
pose proof (pos_INR n) as Hn.
assert (Hq' : IZR q <> 0) by (apply not_0_IZR; lia).
assert (H256 : 256 ^ n <> 0) by (apply pow_nonzero; lra).
replace (IZR S * (IZR p / IZR q / (2 * INR n + 1)))
  with (IZR S * IZR p / (IZR q * (2 * INR n + 1))) by (field; lra).
rewrite H. field. lra.
Qed.

(** The coefficients of [S asin_poly 34 (s / 256)] *)
Local Definition asin_G : list Z := map (gcoef asin_S) (seq 0 34).

Local Lemma asin_S_exact : forallb (gexact asin_S) (seq 0 34) = true.
Proof. vm_compute. reflexivity. Qed.

Local Lemma gpoly_correct :
  forall S N, (forall n, (n < N)%nat -> gexact S n = true) ->
  forall s, IZR S * asin_poly N s = zeval (map (gcoef S) (seq 0 N)) (256 * s).
Proof.
intros S N. induction N as [|N IH]; intros Hex s.
- cbn [asin_poly seq map zeval]. ring.
- rewrite seq_S, map_app, zeval_app, length_map, length_seq.
  cbn [asin_poly map zeval Nat.add].
  rewrite Rmult_plus_distr_l, IH by (intros n Hn; apply Hex; lia).
  replace (IZR S * (asin_a N * s ^ N)) with (IZR S * asin_a N * s ^ N) by ring.
  rewrite (gcoef_correct S N (Hex N ltac:(lia))), Rpow_mult_distr. ring.
Qed.

Local Lemma asin_G_correct : forall s, IZR asin_S * asin_poly 34 s = zeval asin_G (256 * s).
Proof.
apply gpoly_correct. intros n Hn.
pose proof asin_S_exact as H. rewrite forallb_forall in H.
apply H, in_seq. lia.
Qed.

(** ** The check of each row *)

Local Lemma IZR_pow2 : forall e, (0 <= e)%Z -> IZR (2 ^ e) = bpow radix2 e.
Proof. intros e He. rewrite <- IZR_Zpower by exact He. reflexivity. Qed.

Local Lemma fx_le :
  forall a b, (a <= b)%Z -> IZR a * bpow radix2 (-128) <= IZR b * bpow radix2 (-128).
Proof. intros a b H. apply Rmult_le_compat_r; [apply bpow_ge_0 | apply IZR_le, H]. Qed.

Local Lemma fx_abs :
  forall t, Rabs (IZR t * bpow radix2 (-128)) = IZR (Z.abs t) * bpow radix2 (-128).
Proof.
intros t. rewrite Rabs_mult, abs_IZR, (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0.
reflexivity.
Qed.

(** The entries of a row as integers at 128 fractional bits, if each is
    a multiple of [2^-128] ([fix_of]) *)
Local Fixpoint fixes (l : list Z) : option (list Z) :=
  match l with
  | [] => Some []
  | b :: l =>
      match fix_of 128 (from_bits b), fixes l with
      | Some n, Some m => Some (n :: m)
      | _, _ => None
      end
  end.

Local Lemma fixes_nth :
  forall l ts, fixes l = Some ts ->
  length ts = length l /\
  forall k, (k < length l)%nat -> fix_of 128 (from_bits (nth k l 0%Z)) = Some (nth k ts 0%Z).
Proof.
intros l. induction l as [|b l IH]; intros ts H; cbn [fixes] in H.
- injection H as <-. split; [reflexivity | intros k Hk; cbn [length] in Hk; lia].
- destruct (fix_of 128 (from_bits b)) as [n|] eqn:Eb; [|discriminate H].
  destruct (fixes l) as [m|] eqn:El; [|discriminate H].
  injection H as <-. destruct (IH m eq_refl) as [Hl Hn].
  split; [cbn [length]; lia|].
  intros [|k] Hk; cbn [nth]; [exact Eb|].
  apply Hn. cbn [length] in Hk. lia.
Qed.

(** The coefficients of [2^128 asin_table_poly j tau] in [tau], for [ts]
    the entries of row [j] at 128 fractional bits *)
Local Definition row_coefs (ts : list Z) : list Z :=
  [nth 0 ts 0 + nth 1 ts 0; nth 2 ts 0; nth 3 ts 0; nth 4 ts 0; nth 5 ts 0; nth 6 ts 0;
   nth 7 ts 0]%Z.

(** [2^128 S (asin_poly 34 (j / 256 + tau) - asin_table_poly j tau)] in
    [tau], for [G] the coefficients of [S asin_poly 34 (s / 256)]: since
    [256 (j / 256 + tau) = j + 256 tau], the first part is [G] shifted
    by [j], then scaled by [256]. *)
Local Definition row_diff (S : Z) (G : list Z) (j : Z) (ts : list Z) : list Z :=
  zsub (map (Z.mul (2 ^ 128)) (zmp 256 (zshift j G))) (map (Z.mul S) (row_coefs ts)).

(** The check of row [j], each test an integer inequality. The last one
    bounds [row_diff] at [|tau| <= (2^46 + 1) / 2^55 = 2^-9 + 2^-55] by
    its coefficients' absolute values ([zeval_abs], [znum]). Each product
    puts its small or power-of-2 factor first, as [Pos.mul] recurses on
    its first argument. *)
Local Definition row_okb (S : Z) (G : list Z) (j : Z) (row : list Z) : bool :=
  match fixes row with
  | Some ts =>
      let F := row_diff S G j ts in
      (length ts =? 8)%nat &&
      (2 ^ 128 <=? nth 0 ts 0)%Z && (16 * nth 0 ts 0 <=? 17 * 2 ^ 128)%Z &&
      (Z.abs (nth 1 ts 0) <=? 2 ^ 75)%Z &&
      (2048 * Z.abs (nth 2 ts 0) <=? 441 * 2 ^ 128)%Z &&
      forallb (fun k => 8 * Z.abs (nth k ts 0) <=? 2 ^ 128)%Z [3; 4; 5; 6; 7]%nat &&
      (2 ^ 68 * znum (map Z.abs F) (2 ^ 46 + 1) (2 ^ 55) <=?
       11 * (2 ^ 55) ^ Z.of_nat (length F) * (2 ^ 128 * S))%Z
  | None => false
  end.

Local Lemma row_correct :
  forall S G j row,
  (0 < S)%Z -> (forall s, IZR S * asin_poly 34 s = zeval G (256 * s)) ->
  row_okb S G j row = true ->
  (forall k, (k <= 7)%nat -> is_finite (from_bits (nth k row 0%Z)) = true) /\
  1 <= B2R (from_bits (nth 0 row 0%Z)) <= 17 / 16 /\
  Rabs (B2R (from_bits (nth 1 row 0%Z))) <= bpow radix2 (-53) /\
  Rabs (B2R (from_bits (nth 2 row 0%Z))) <= 441 / 2048 /\
  (forall k, (3 <= k <= 7)%nat -> Rabs (B2R (from_bits (nth k row 0%Z))) <= / 8) /\
  forall tau, Rabs tau <= / 512 + bpow radix2 (-55) ->
  let c k := B2R (from_bits (nth k row 0%Z)) in
  Rabs (asin_poly 34 (IZR j / 256 + tau) - (c 0%nat + c 1%nat + tau * (c 2%nat +
    tau * (c 3%nat + tau * (c 4%nat + tau * (c 5%nat + tau * (c 6%nat + tau * c 7%nat)))))))
  <= 11 * bpow radix2 (-68).
Proof.
intros S G j row HS HG Hok.
unfold row_okb in Hok.
destruct (fixes row) as [ts|] eqn:Ef; [|discriminate Hok].
apply fixes_nth in Ef as [Hlen Hnth].
cbv beta zeta in Hok.
repeat rewrite andb_true_iff in Hok.
destruct Hok as [[[[[[H8 H0a] H0b] H1] H2] H37] HF].
apply Nat.eqb_eq in H8.
apply Z.leb_le in H0a. apply Z.leb_le in H0b. apply Z.leb_le in H1.
apply Z.leb_le in H2. apply Z.leb_le in HF.
rewrite forallb_forall in H37.
assert (HB1 : IZR (2 ^ 128) * bpow radix2 (-128) = 1)
  by (rewrite IZR_pow2, <- bpow_plus by lia; reflexivity).
assert (Hc : forall k, (k <= 7)%nat ->
  is_finite (from_bits (nth k row 0%Z)) = true /\
  B2R (from_bits (nth k row 0%Z)) = IZR (nth k ts 0%Z) * bpow radix2 (-128)).
{ intros k Hk.
  destruct (fix_of_correct 128 _ _ (Hnth k ltac:(lia))) as [Hf Hv].
  split; [exact Hf | exact Hv]. }
destruct (Hc 0%nat ltac:(lia)) as [_ R0]. destruct (Hc 1%nat ltac:(lia)) as [_ R1].
destruct (Hc 2%nat ltac:(lia)) as [_ R2]. destruct (Hc 3%nat ltac:(lia)) as [_ R3].
destruct (Hc 4%nat ltac:(lia)) as [_ R4]. destruct (Hc 5%nat ltac:(lia)) as [_ R5].
destruct (Hc 6%nat ltac:(lia)) as [_ R6]. destruct (Hc 7%nat ltac:(lia)) as [_ R7].
split; [intros k Hk; exact (proj1 (Hc k Hk))|].
split.
{ rewrite R0. pose proof (fx_le _ _ H0a) as K1. pose proof (fx_le _ _ H0b) as K2.
  rewrite (mult_IZR 16), (mult_IZR 17) in K2. split; lra. }
split.
{ rewrite R1, fx_abs. pose proof (fx_le _ _ H1) as K.
  assert (E : IZR (2 ^ 75) * bpow radix2 (-128) = bpow radix2 (-53))
    by (rewrite IZR_pow2, <- bpow_plus by lia; reflexivity).
  lra. }
split.
{ rewrite R2, fx_abs. pose proof (fx_le _ _ H2) as K.
  rewrite (mult_IZR 2048), (mult_IZR 441) in K. lra. }
split.
{ intros k Hk. rewrite (proj2 (Hc k ltac:(lia))), fx_abs.
  assert (Hin : In k [3; 4; 5; 6; 7]%nat) by (cbn [In]; lia).
  pose proof (fx_le _ _ (proj1 (Z.leb_le _ _) (H37 k Hin))) as K.
  rewrite (mult_IZR 8) in K. lra. }
intros tau Htau. cbv beta zeta.
rewrite R0, R1, R2, R3, R4, R5, R6, R7.
match goal with |- Rabs (_ - ?T) <= _ =>
  replace T with (bpow radix2 (-128) * zeval (row_coefs ts) tau)
    by (unfold row_coefs; cbn [zeval]; rewrite plus_IZR; ring)
end.
set (P := asin_poly 34 (IZR j / 256 + tau)).
set (Z0 := zeval (row_coefs ts) tau).
(* [2^128 S] times the difference is [row_diff] at [tau]. *)
assert (E1 : zeval (row_diff S G j ts) tau = IZR (2 ^ 128) * (IZR S * P) - IZR S * Z0).
{ unfold row_diff. rewrite zeval_sub, !zeval_scale, zeval_mp, zeval_shift.
  unfold P. rewrite HG.
  replace (256 * (IZR j / 256 + tau)) with (IZR j + 256 * tau) by field.
  reflexivity. }
assert (E : IZR S * IZR (2 ^ 128) * (P - bpow radix2 (-128) * Z0) =
  zeval (row_diff S G j ts) tau).
{ rewrite E1.
  transitivity (IZR (2 ^ 128) * (IZR S * P) -
    IZR S * (IZR (2 ^ 128) * bpow radix2 (-128)) * Z0); [ring|].
  rewrite HB1. ring. }
(* [|tau| <= (2^46 + 1) / 2^55], where [row_okb] bounds [row_diff]. *)
assert (HR : IZR (2 ^ 46 + 1) / IZR (2 ^ 55) = / 512 + bpow radix2 (-55)).
{ change (/ 512) with (bpow radix2 (-9)).
  rewrite plus_IZR, !IZR_pow2 by lia.
  replace (bpow radix2 46) with (bpow radix2 (-9) * bpow radix2 55)
    by (rewrite <- bpow_plus; reflexivity).
  replace (bpow radix2 (-55)) with (/ bpow radix2 55) by (rewrite <- bpow_opp; reflexivity).
  field. apply Rgt_not_eq, bpow_gt_0. }
rewrite <- HR in Htau.
pose proof (zeval_abs (row_diff S G j ts) tau _ Htau) as KA.
pose proof (zeval_num (map Z.abs (row_diff S G j ts)) (2 ^ 46 + 1) (2 ^ 55) ltac:(lia)) as KN.
rewrite length_map in KN.
set (A := zeval (map Z.abs (row_diff S G j ts)) (IZR (2 ^ 46 + 1) / IZR (2 ^ 55))) in *.
set (n := length (row_diff S G j ts)) in *.
apply IZR_le in HF.
rewrite (mult_IZR (2 ^ 68)), (mult_IZR (11 * _)), (mult_IZR 11), <- (pow_IZR (2 ^ 55)),
  (mult_IZR (2 ^ 128)), <- KN in HF.
assert (HD : 0 < IZR (2 ^ 55) ^ n) by (apply pow_lt; rewrite IZR_pow2 by lia; apply bpow_gt_0).
assert (HA : IZR (2 ^ 68) * A <= 11 * (IZR (2 ^ 128) * IZR S)).
{ apply (Rmult_le_reg_r _ _ _ HD).
  replace (IZR (2 ^ 68) * A * IZR (2 ^ 55) ^ n) with (IZR (2 ^ 68) * (A * IZR (2 ^ 55) ^ n))
    by ring.
  replace (11 * (IZR (2 ^ 128) * IZR S) * IZR (2 ^ 55) ^ n)
    with (11 * IZR (2 ^ 55) ^ n * (IZR (2 ^ 128) * IZR S)) by ring.
  exact HF. }
assert (HS2 : 0 < IZR S * IZR (2 ^ 128)).
{ apply Rmult_lt_0_compat; [apply IZR_lt, HS | rewrite IZR_pow2 by lia; apply bpow_gt_0]. }
assert (H68 : 0 < IZR (2 ^ 68)) by (rewrite IZR_pow2 by lia; apply bpow_gt_0).
assert (H68b : IZR (2 ^ 68) * bpow radix2 (-68) = 1)
  by (rewrite IZR_pow2, <- bpow_plus by lia; reflexivity).
rewrite <- E, Rabs_mult, (Rabs_pos_eq (IZR S * IZR (2 ^ 128))) in KA by lra.
pose proof (Rmult_le_compat_l (IZR (2 ^ 68)) _ _ (Rlt_le _ _ H68) KA) as KA'.
apply (Rmult_le_reg_l (IZR (2 ^ 68))); [exact H68|].
replace (IZR (2 ^ 68) * (11 * bpow radix2 (-68))) with 11 by lra.
apply (Rmult_le_reg_l _ _ _ HS2).
lra.
Qed.

(** ** The table *)

Local Fixpoint all_okb (Sc : Z) (G : list Z) (t : list (list Z)) (j : Z) : bool :=
  match t with
  | [] => true
  | row :: t => row_okb Sc G j row && all_okb Sc G t (j + 1)
  end.

Local Lemma all_okb_nth :
  forall Sc G t j0 k, all_okb Sc G t j0 = true -> (k < length t)%nat ->
  row_okb Sc G (j0 + Z.of_nat k) (nth k t []) = true.
Proof.
intros Sc G t; induction t as [|row t IH]; intros j0 k H Hk; [cbn [length] in Hk; lia|].
cbn [all_okb] in H. apply andb_prop in H as [H1 H2].
destruct k as [|k]; cbn [nth].
- replace (j0 + Z.of_nat 0)%Z with j0 by lia. exact H1.
- replace (j0 + Z.of_nat (S k))%Z with ((j0 + 1) + Z.of_nat k)%Z by lia.
  apply IH; [exact H2 | cbn [length] in Hk; lia].
Qed.

(** The check of all 65 rows ([vm_compute]) *)
Local Lemma asin_table_ok : all_okb asin_S asin_G DyadicAtan.ASIN_TABLE 0 = true.
Proof. vm_compute. reflexivity. Qed.

Local Lemma asin_table_length : length DyadicAtan.ASIN_TABLE = 65%nat.
Proof. vm_compute. reflexivity. Qed.

Local Lemma asin_S_pos : (0 < asin_S)%Z.
Proof. vm_compute. reflexivity. Qed.

Local Lemma asin_row_ok :
  forall j, (0 <= j <= 64)%Z ->
  row_okb asin_S asin_G j (nth (Z.to_nat j) DyadicAtan.ASIN_TABLE []) = true.
Proof.
intros j Hj.
pose proof (all_okb_nth asin_S asin_G _ 0 (Z.to_nat j) asin_table_ok) as H.
rewrite asin_table_length, Z.add_0_l, Z2Nat.id in H by lia.
apply H. lia.
Qed.

(** [c0h + c0l + tau (c1 + tau (c2 + ... + tau c6))] of row [j]. *)
Definition asin_table_poly (j : Z) (tau : R) : R :=
  let c k := B2R (DyadicAtan.asin_coef j k) in
  c 0%nat + c 1%nat + tau * (c 2%nat + tau * (c 3%nat + tau * (c 4%nat + tau * (c 5%nat +
    tau * (c 6%nat + tau * c 7%nat))))).

Lemma asin_coef_facts :
  forall j, (0 <= j <= 64)%Z ->
  (forall k, (k <= 7)%nat -> is_finite (DyadicAtan.asin_coef j k) = true) /\
  1 <= B2R (DyadicAtan.asin_coef j 0) <= 17 / 16 /\
  Rabs (B2R (DyadicAtan.asin_coef j 1)) <= bpow radix2 (-53) /\
  Rabs (B2R (DyadicAtan.asin_coef j 2)) <= 441 / 2048 /\
  (forall k, (3 <= k <= 7)%nat -> Rabs (B2R (DyadicAtan.asin_coef j k)) <= / 8).
Proof.
intros j Hj.
destruct (row_correct _ _ _ _ asin_S_pos asin_G_correct (asin_row_ok j Hj))
  as [Hf [H0 [H1 [H2 [H37 _]]]]].
exact (conj Hf (conj H0 (conj H1 (conj H2 H37)))).
Qed.

Theorem asin_table_close :
  forall j tau, (0 <= j <= 64)%Z -> Rabs tau <= / 512 + bpow radix2 (-55) ->
  Rabs (asin_poly 34 (IZR j / 256 + tau) - asin_table_poly j tau) <= 11 * bpow radix2 (-68).
Proof.
intros j tau Hj Htau.
destruct (row_correct _ _ _ _ asin_S_pos asin_G_correct (asin_row_ok j Hj))
  as [_ [_ [_ [_ [_ Hc]]]]].
exact (Hc tau Htau).
Qed.
