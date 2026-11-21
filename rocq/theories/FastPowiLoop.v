(** * The loop of the small powers of the dyadic [pown]

    [DyadicPow.small_loop] of [Model.v] takes [m^a] for [1 <= a <= 8] and
    an [f64] [m] in [[1/2, 1)] by binary powering in double-double, from
    [(m, 0)] over the bits of [a] below its top one: a square of [h + l]
    is [s = RN(h h)] plus the error of that product, which is exact
    ([TwoProduct.v]), and [RN(2 h l)], without [l^2], and a product by
    [m] is [p = RN(h m)] plus its error and [RN(l m)]. Every [h] stays in
    [[2^-8, 1]], so that the products [h h] and [h m] do not underflow,
    and [|l|] stays below
    [2^-49 h]. [small_loop_correct] shows that the result is [m^a] within
    [2^-80 m^a], and [small_loop_fma] that an FMA gives the same result,
    as the errors of the products are exact. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Mult_error.
From Fushimi Require Import Model Mpfr Elementary Encoding TwoSum TwoProduct FastRound FastExpErr.
From Fushimi Require MulRuTiny.

Open Scope R_scope.

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp] in *.

(** ** The products are exact *)

(** The product of two finite [x] and [y] of magnitude at most 1, whose
    exact value is at least [2^-900] in magnitude, is within a factor 2
    of [x y], and TwoProduct is exact for it with and without an FMA: its
    exponent is in [[-901, 1]], and those of [x] and [y] are at most 0
    (as [FastPowCube.v]). *)
Local Lemma prod_exact :
  forall fma x y, is_finite x = true -> is_finite y = true ->
  Rabs (B2R x) <= 1 -> Rabs (B2R y) <= 1 ->
  bpow radix2 (-900) <= Rabs (B2R x * B2R y) ->
  is_finite (mul x y) = true /\
  Rabs (B2R x * B2R y) / 2 <= Rabs (B2R (mul x y)) <= 2 * Rabs (B2R x * B2R y) /\
  Generic.two_prod_is_exact fma x y (mul x y) = true.
Proof.
intros fma x y Fx Fy Hx Hy Hlo.
assert (Hm : Rabs (B2R x * B2R y) <= 1 * 1)
  by (rewrite Rabs_mult;
      apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hx | exact Hy]).
destruct (mul_e x y Fx Fy ltac:(lra)) as (Fp & _ & Bp).
assert (HT : bpow radix2 (-53) * Rabs (B2R x * B2R y) + bpow radix2 (-1075) <=
  Rabs (B2R x * B2R y) / 2) by (num; lra).
pose proof (Rabs_triang_inv (B2R (mul x y)) (B2R x * B2R y)) as T1.
pose proof (Rabs_triang_inv (B2R x * B2R y) (B2R (mul x y))) as T2.
rewrite Rabs_minus_sym in T2.
assert (B : Rabs (B2R x * B2R y) / 2 <= Rabs (B2R (mul x y)) <= 2 * Rabs (B2R x * B2R y))
  by lra.
split; [exact Fp | split; [exact B |]].
assert (Elo : (-901 <= Generic.exponent (mul x y))%Z).
{ apply MulRuTiny.exponent_ge; [exact Fp|].
  assert (bpow radix2 (-901) = bpow radix2 (-900) / 2) by (num; lra). lra. }
assert (Ehi : (Generic.exponent (mul x y) < 2)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fp | lia |]. num. lra. }
assert (Ex : (Generic.exponent x < 1)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fx | lia |]. num. lra. }
assert (Ey : (Generic.exponent y < 1)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fy | lia |]. num. lra. }
unfold Generic.two_prod_is_exact. cbv zeta.
destruct fma; repeat (apply andb_true_intro; split); apply Z.leb_le; lia.
Qed.

(** [add x x] is [2 x] exactly, as [2 x] is an [f64]. *)
Local Lemma add_twice :
  forall x, is_finite x = true -> Rabs (B2R x) <= 1 ->
  is_finite (add x x) = true /\ B2R (add x x) = 2 * B2R x.
Proof.
intros x Fx Hx.
assert (H2 : Rabs (B2R x + B2R x) <= 16)
  by (replace (B2R x + B2R x) with (2 * B2R x) by ring;
      rewrite Rabs_mult, (Rabs_pos_eq 2) by lra; lra).
destruct (add_e x x Fx Fx H2) as (F & R & _).
split; [exact F|]. rewrite R.
assert (G : generic_format radix2 fexp64 (B2R x * bpow radix2 1))
  by (apply mult_bpow_pos_exact_FLT; [apply generic_format_B2R | lia]).
replace (B2R x + B2R x) with (B2R x * bpow radix2 1) by (change (bpow radix2 1) with 2; ring).
rewrite (round_generic _ _ _ _ G). change (bpow radix2 1) with 2. ring.
Qed.

(** A rounded product of magnitude at most 1 stays at most 1, as 1 is an
    [f64]. *)
Local Lemma mul_le_1 :
  forall x y, is_finite x = true -> is_finite y = true -> Rabs (B2R x * B2R y) <= 1 ->
  Rabs (B2R (mul x y)) <= 1.
Proof.
intros x y Fx Fy H.
destruct (mul_e x y Fx Fy ltac:(lra)) as (_ & R & _). rewrite R.
assert (F1 : generic_format radix2 fexp64 1).
{ apply (generic_format_bpow radix2 fexp64 0). unfold FLT_exp. lia. }
apply abs_round_le_generic; [typeclasses eauto .. | exact F1 | exact H].
Qed.

(** ** One step of the loop *)

(** A square of the state [(h, l)]: [s = RN(h h)], and the low part
    [RN(err(h h) + RN(2 h l))], where [add h h] is [2 h] exactly. *)
Local Definition sq_st (fma : bool) (st : f64 * f64) : f64 * f64 :=
  (mul (fst st) (fst st),
   add (Generic.two_prod_err fma (fst st) (fst st) (mul (fst st) (fst st)))
     (mul (add (fst st) (fst st)) (snd st))).

(** A product of the state [(h, l)] by [m]: [p = RN(h m)], and the low
    part [RN(err(h m) + RN(l m))]. *)
Local Definition mu_st (fma : bool) (m : f64) (st : f64 * f64) : f64 * f64 :=
  (mul (fst st) m,
   add (Generic.two_prod_err fma (fst st) m (mul (fst st) m)) (mul (snd st) m)).

(** The loop for each [a], innermost step first: a square for each bit
    of [a] below its top one, followed by a product by [m] if that bit
    is set. *)
Local Lemma chain1 : forall fma m,
  DyadicPow.small_loop fma 1 m (Z.to_nat (DyadicPow.ilog2 1)) m zero = (m, zero).
Proof. reflexivity. Qed.

Local Lemma chain2 : forall fma m,
  DyadicPow.small_loop fma 2 m (Z.to_nat (DyadicPow.ilog2 2)) m zero =
  sq_st fma (m, zero).
Proof. reflexivity. Qed.

Local Lemma chain3 : forall fma m,
  DyadicPow.small_loop fma 3 m (Z.to_nat (DyadicPow.ilog2 3)) m zero =
  mu_st fma m (sq_st fma (m, zero)).
Proof. reflexivity. Qed.

Local Lemma chain4 : forall fma m,
  DyadicPow.small_loop fma 4 m (Z.to_nat (DyadicPow.ilog2 4)) m zero =
  sq_st fma (sq_st fma (m, zero)).
Proof. reflexivity. Qed.

Local Lemma chain5 : forall fma m,
  DyadicPow.small_loop fma 5 m (Z.to_nat (DyadicPow.ilog2 5)) m zero =
  mu_st fma m (sq_st fma (sq_st fma (m, zero))).
Proof. reflexivity. Qed.

Local Lemma chain6 : forall fma m,
  DyadicPow.small_loop fma 6 m (Z.to_nat (DyadicPow.ilog2 6)) m zero =
  sq_st fma (mu_st fma m (sq_st fma (m, zero))).
Proof. reflexivity. Qed.

Local Lemma chain7 : forall fma m,
  DyadicPow.small_loop fma 7 m (Z.to_nat (DyadicPow.ilog2 7)) m zero =
  mu_st fma m (sq_st fma (mu_st fma m (sq_st fma (m, zero)))).
Proof. reflexivity. Qed.

Local Lemma chain8 : forall fma m,
  DyadicPow.small_loop fma 8 m (Z.to_nat (DyadicPow.ilog2 8)) m zero =
  sq_st fma (sq_st fma (sq_st fma (m, zero))).
Proof. reflexivity. Qed.

(** ** The invariant of the loop *)

(** The state [(h, l)] approximates [P]: [h] and [l] are finite, [h] is in
    [[2^-9, 1]], [|l| <= k 2^-53 h], [h + l] is [P] within [d P], and [P]
    is in [[2^-8, 1]]. *)
Local Definition st_inv (P : R) (st : f64 * f64) (k d : R) : Prop :=
  is_finite (fst st) = true /\ is_finite (snd st) = true /\
  bpow radix2 (-9) <= B2R (fst st) <= 1 /\
  Rabs (B2R (snd st)) <= k * bpow radix2 (-53) * B2R (fst st) /\
  Rabs (P - (B2R (fst st) + B2R (snd st))) <= d * P /\
  bpow radix2 (-8) <= P <= 1.

Local Lemma abs_le_inv : forall x a, Rabs x <= a -> - a <= x <= a.
Proof. intros x a H. unfold Rabs in H. destruct (Rcase_abs x); lra. Qed.

Local Lemma abs_sub : forall a b, Rabs (a - b) <= Rabs a + Rabs b.
Proof.
intros a b. unfold Rminus. eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp. lra.
Qed.

(** The real numbers of a square: [S = RN(H H)] with [E = H H - S] exact,
    [U = RN(2 H L)] and [L' = RN(E + U)]. As [(H + L)^2 = H H + 2 H L +
    L^2], the error on [P^2] is [P^2 - (H + L)^2] (about [2 d P^2]), the
    dropped [L^2] (at most [14^2 2^-106 H^2]) and the two roundings (at
    most [(2 k + 1 + 2 k) 2^-106 H^2]): with [H] within a factor [1 +
    2^-40] of [P], all but the first are below [2^-96 P^2]. *)
Local Lemma sq_real :
  forall k d P H L S E U L',
  0 <= k <= 14 -> 0 <= d <= bpow radix2 (-90) ->
  bpow radix2 (-9) <= H <= 1 ->
  Rabs L <= k * bpow radix2 (-53) * H ->
  Rabs (P - (H + L)) <= d * P -> bpow radix2 (-8) <= P <= 1 ->
  bpow radix2 (-8) <= P * P ->
  Rabs (S - H * H) <= bpow radix2 (-53) * Rabs (H * H) + bpow radix2 (-1075) ->
  E = H * H - S ->
  Rabs (U - 2 * H * L) <= bpow radix2 (-53) * Rabs (2 * H * L) + bpow radix2 (-1075) ->
  Rabs (L' - (E + U)) <= bpow radix2 (-53) * Rabs (E + U) + bpow radix2 (-1075) ->
  Rabs L' <= (2 * k + 2) * bpow radix2 (-53) * S /\
  Rabs (P * P - (S + L')) <= (2 * d + bpow radix2 (-96)) * (P * P) /\
  bpow radix2 (-9) <= S.
Proof.
intros k d P H L S E U L' Hk Hd Hh Hl Hp Hp1 Hp2 Hs HE Hu Hl'.
pose proof (bpow_gt_0 radix2 (-9)) as B9.
pose proof (bpow_gt_0 radix2 (-8)) as B8.
assert (H0 : 0 <= H) by lra.
assert (QQ : 0 <= H * H) by nra.
assert (Q0 : bpow radix2 (-18) <= H * H) by (clear - Hh; num; nra).
rewrite (Rabs_pos_eq (H * H)) in Hs by exact QQ.
assert (L14 : Rabs L <= 14 * bpow radix2 (-53) * H) by (clear - Hk H0 Hl; num; nra).
assert (B1 : Rabs (2 * H * L) <= 2 * bpow radix2 (-53) * (k * (H * H))).
{ rewrite !Rabs_mult, (Rabs_pos_eq 2), (Rabs_pos_eq H) by lra.
  pose proof (Rabs_pos L). clear - H0 Hl H1. num. nra. }
assert (K14 : k * (H * H) <= 14 * (H * H)) by (clear - Hk QQ; nra).
assert (K0 : 0 <= k * (H * H)) by (clear - Hk QQ; nra).
assert (LL : Rabs (L * L) <= 196 * bpow radix2 (-106) * (H * H)).
{ rewrite Rabs_mult. pose proof (Rabs_pos L) as A. clear - L14 H0 A. num. nra. }
assert (HE' : Rabs E <= bpow radix2 (-53) * (H * H) + bpow radix2 (-1075))
  by (rewrite HE, Rabs_minus_sym; exact Hs).
pose proof (Rabs_triang_inv U (2 * H * L)) as TU.
pose proof (Rabs_triang E U) as TEU.
pose proof (Rabs_triang_inv L' (E + U)) as TL.
pose proof (abs_le_inv _ _ Hs) as Hs2.
assert (KS : (1 - bpow radix2 (-53)) * (k * (H * H)) - bpow radix2 (-1075) * k <= k * S)
  by (clear - Hk Hs2; nra).
assert (G1 : Rabs L' <= (2 * k + 2) * bpow radix2 (-53) * S).
{ clear - Hk Q0 K14 K0 B1 HE' TU TEU TL Hu Hl' Hs2 KS. num. lra. }
assert (EQ : P * P - (S + L') =
  (2 * P * (P - (H + L)) - (P - (H + L)) * (P - (H + L))) + L * L - (U - 2 * H * L) -
  (L' - (E + U))) by (rewrite HE; ring).
assert (HP1 : H <= (1 + bpow radix2 (-40)) * P).
{ assert (dP : d * P <= bpow radix2 (-90) * P) by (clear - Hd Hp1 B8; nra).
  apply abs_le_inv in Hp. apply abs_le_inv in L14. clear - Hp L14 dP H0 Hp1 B8. num. lra. }
assert (HQ : H * H <= (1 + bpow radix2 (-38)) * (P * P)).
{ clear - HP1 H0 Hp1 B8. num. nra. }
set (D := P - (H + L)) in *.
assert (DB : Rabs D <= bpow radix2 (-90) * P) by (clear - Hp Hd Hp1 B8; nra).
assert (D1 : P * Rabs D <= d * (P * P)) by (clear - Hp Hp1 B8; nra).
assert (D2 : Rabs D * Rabs D <= bpow radix2 (-180) * (P * P)).
{ pose proof (Rabs_pos D). clear - DB H1 Hp1 B8. num. nra. }
assert (F1 : Rabs (2 * P * D - D * D) <= 2 * (d * (P * P)) + bpow radix2 (-180) * (P * P)).
{ pose proof (abs_sub (2 * P * D) (D * D)) as A.
  rewrite !Rabs_mult, (Rabs_pos_eq 2), (Rabs_pos_eq P) in A by lra. lra. }
assert (G2 : Rabs (P * P - (S + L')) <= (2 * d + bpow radix2 (-96)) * (P * P)).
{ rewrite EQ.
  pose proof (abs_sub (2 * P * D - D * D + L * L - (U - 2 * H * L)) (L' - (E + U))) as A1.
  pose proof (abs_sub (2 * P * D - D * D + L * L) (U - 2 * H * L)) as A2.
  pose proof (Rabs_triang (2 * P * D - D * D) (L * L)) as A3.
  clear - A1 A2 A3 F1 LL HQ Hu B1 K14 Hl' TEU HE' TU Hp2. num. lra. }
assert (S0 : 0 <= S) by (clear - Hs2 Q0; num; lra).
assert (KS2 : k * S <= 14 * S) by (clear - Hk S0; nra).
split; [exact G1 | split; [exact G2 |]].
apply abs_le_inv in G1. apply abs_le_inv in G2.
assert (dPP : d * (P * P) <= bpow radix2 (-90) * (P * P)) by (clear - Hd Hp1 B8; nra).
clear - G1 G2 KS2 dPP Hp2 S0. num. lra.
Qed.

(** A square keeps the invariant, for the square [P^2] of [P], with [k]
    doubled plus 2 and [d] doubled plus [2^-96], and the error of [h h]
    is the same [f64] with an FMA as without. *)
Local Lemma sq_step :
  forall fma P st k d,
  st_inv P st k d -> 0 <= k <= 14 -> 0 <= d <= bpow radix2 (-90) ->
  bpow radix2 (-8) <= P * P ->
  st_inv (P * P) (sq_st fma st) (2 * k + 2) (2 * d + bpow radix2 (-96)) /\
  sq_st true st = sq_st false st.
Proof.
intros fma P [h l] k d (Fh & Fl & Hh & Hl & Hp & HP) Hk Hd HP2.
cbn [fst snd] in Fh, Fl, Hh, Hl, Hp.
unfold sq_st; cbn [fst snd].
pose proof (bpow_gt_0 radix2 (-9)) as B9.
pose proof (bpow_gt_0 radix2 (-8)) as B8.
assert (Ah : Rabs (B2R h) <= 1) by (rewrite Rabs_pos_eq; lra).
assert (A1 : Rabs (B2R h * B2R h) <= 1) by (rewrite Rabs_pos_eq by nra; nra).
assert (A16 : Rabs (B2R h * B2R h) <= 16) by lra.
assert (Ahh : bpow radix2 (-900) <= Rabs (B2R h * B2R h)).
{ rewrite Rabs_pos_eq by nra. clear - Hh. num. nra. }
destruct (prod_exact true h h Fh Fh Ah Ah Ahh) as (Fs & _ & X1).
destruct (prod_exact false h h Fh Fh Ah Ah Ahh) as (_ & _ & X0).
assert (Xf : Generic.two_prod_is_exact fma h h (mul h h) = true) by (destruct fma; assumption).
destruct (two_prod_err_correct fma h h Fh Fh Xf) as (_ & _ & _ & Fe & Re).
destruct (mul_e h h Fh Fh A16) as (_ & _ & Bs).
destruct (add_twice h Fh Ah) as (Ft & Rt).
assert (Al : Rabs (B2R l) <= 1) by (clear - Hl Hk Hh B9; num; nra).
assert (A2' : Rabs (2 * B2R h * B2R l) <= 2).
{ rewrite !Rabs_mult, (Rabs_pos_eq 2) by lra.
  pose proof (Rabs_pos (B2R h)). pose proof (Rabs_pos (B2R l)). nra. }
assert (A2 : Rabs (B2R (add h h) * B2R l) <= 16) by (rewrite Rt; lra).
destruct (mul_e (add h h) l Ft Fl A2) as (Fu & _ & Bu).
rewrite Rt in Bu.
set (e := Generic.two_prod_err fma h h (mul h h)) in *.
set (u := mul (add h h) l) in *.
assert (A3 : Rabs (B2R e + B2R u) <= 16).
{ pose proof (Rabs_triang (B2R e) (B2R u)) as T1.
  pose proof (Rabs_triang_inv (B2R u) (2 * B2R h * B2R l)) as T2.
  assert (Ae : Rabs (B2R e) = Rabs (B2R (mul h h) - B2R h * B2R h))
    by (rewrite Re, Rabs_minus_sym; reflexivity).
  clear - T1 T2 Ae Bs Bu A1 A2'. num. lra. }
destruct (add_e e u Fe Fu A3) as (Fl' & _ & Bl').
destruct (sq_real k d P (B2R h) (B2R l) (B2R (mul h h)) (B2R e) (B2R u) (B2R (add e u))
  Hk Hd Hh Hl Hp HP HP2 Bs Re Bu Bl') as (G1 & G2 & G3).
pose proof (abs_le_inv _ _ (mul_le_1 h h Fh Fh A1)) as S1.
split.
- unfold st_inv; cbn [fst snd].
  split; [exact Fs|]. split; [exact Fl'|]. split; [split; [exact G3 | lra]|].
  split; [exact G1|]. split; [exact G2|]. split; [exact HP2 | nra].
- rewrite (two_prod_err_fma_eq h h Fh Fh X1 X0). reflexivity.
Qed.

(** The real numbers of a product by [M]: [Pp = RN(H M)] with [E = H M -
    Pp] exact, [V = RN(L M)] and [L' = RN(E + V)]. The error on [P M] is
    [(P - (H + L)) M] (at most [d P M]) and the two roundings (at most
    [(2 k + 1) 2^-106 H M]), below [2^-96 P M]. *)
Local Lemma mu_real :
  forall k d P H L M Pp E V L',
  0 <= k <= 14 -> 0 <= d <= bpow radix2 (-90) ->
  bpow radix2 (-9) <= H <= 1 ->
  Rabs L <= k * bpow radix2 (-53) * H ->
  Rabs (P - (H + L)) <= d * P -> bpow radix2 (-8) <= P <= 1 ->
  / 2 <= M < 1 -> bpow radix2 (-8) <= P * M ->
  Rabs (Pp - H * M) <= bpow radix2 (-53) * Rabs (H * M) + bpow radix2 (-1075) ->
  E = H * M - Pp ->
  Rabs (V - L * M) <= bpow radix2 (-53) * Rabs (L * M) + bpow radix2 (-1075) ->
  Rabs (L' - (E + V)) <= bpow radix2 (-53) * Rabs (E + V) + bpow radix2 (-1075) ->
  Rabs L' <= (k + 2) * bpow radix2 (-53) * Pp /\
  Rabs (P * M - (Pp + L')) <= (d + bpow radix2 (-96)) * (P * M) /\
  bpow radix2 (-9) <= Pp.
Proof.
intros k d P H L M Pp E V L' Hk Hd Hh Hl Hp Hp1 Hm Hpm Hs HE Hv Hl'.
pose proof (bpow_gt_0 radix2 (-9)) as B9.
pose proof (bpow_gt_0 radix2 (-8)) as B8.
assert (H0 : 0 <= H) by lra.
assert (QQ : 0 <= H * M) by nra.
assert (Q0 : bpow radix2 (-10) <= H * M) by (clear - Hh Hm; num; nra).
rewrite (Rabs_pos_eq (H * M)) in Hs by exact QQ.
assert (L14 : Rabs L <= 14 * bpow radix2 (-53) * H) by (clear - Hk H0 Hl; num; nra).
assert (B1 : Rabs (L * M) <= bpow radix2 (-53) * (k * (H * M))).
{ rewrite Rabs_mult, (Rabs_pos_eq M) by lra.
  pose proof (Rabs_pos L). clear - Hm Hl H1. num. nra. }
assert (K14 : k * (H * M) <= 14 * (H * M)) by (clear - Hk QQ; nra).
assert (K0 : 0 <= k * (H * M)) by (clear - Hk QQ; nra).
assert (HE' : Rabs E <= bpow radix2 (-53) * (H * M) + bpow radix2 (-1075))
  by (rewrite HE, Rabs_minus_sym; exact Hs).
pose proof (Rabs_triang_inv V (L * M)) as TV.
pose proof (Rabs_triang E V) as TEV.
pose proof (Rabs_triang_inv L' (E + V)) as TL.
pose proof (abs_le_inv _ _ Hs) as Hs2.
assert (KS : (1 - bpow radix2 (-53)) * (k * (H * M)) - bpow radix2 (-1075) * k <= k * Pp)
  by (clear - Hk Hs2; nra).
assert (G1 : Rabs L' <= (k + 2) * bpow radix2 (-53) * Pp).
{ clear - Hk Q0 K14 K0 B1 HE' TV TEV TL Hv Hl' Hs2 KS. num. lra. }
assert (EQ : P * M - (Pp + L') = (P - (H + L)) * M - (V - L * M) - (L' - (E + V)))
  by (rewrite HE; ring).
assert (HP1 : H <= (1 + bpow radix2 (-40)) * P).
{ assert (dP : d * P <= bpow radix2 (-90) * P) by (clear - Hd Hp1 B8; nra).
  apply abs_le_inv in Hp. apply abs_le_inv in L14. clear - Hp L14 dP H0 Hp1 B8. num. lra. }
assert (HQ : H * M <= (1 + bpow radix2 (-40)) * (P * M)) by (clear - HP1 Hm; nra).
set (D := P - (H + L)) in *.
assert (D1 : Rabs D * M <= d * (P * M)) by (clear - Hp Hm; nra).
assert (G2 : Rabs (P * M - (Pp + L')) <= (d + bpow radix2 (-96)) * (P * M)).
{ rewrite EQ.
  pose proof (abs_sub (D * M - (V - L * M)) (L' - (E + V))) as A1.
  pose proof (abs_sub (D * M) (V - L * M)) as A2.
  rewrite Rabs_mult, (Rabs_pos_eq M) in A2 by lra.
  clear - A1 A2 D1 HQ Hv B1 K14 Hl' TEV HE' TV Hpm. num. lra. }
assert (S0 : 0 <= Pp) by (clear - Hs2 Q0; num; lra).
assert (KS2 : k * Pp <= 14 * Pp) by (clear - Hk S0; nra).
split; [exact G1 | split; [exact G2 |]].
apply abs_le_inv in G1. apply abs_le_inv in G2.
assert (dPP : d * (P * M) <= bpow radix2 (-90) * (P * M)) by (clear - Hd Hpm B8; nra).
clear - G1 G2 KS2 dPP Hpm S0. num. lra.
Qed.

(** A product by [m] keeps the invariant, for [P m], with [k] and [d]
    plus 2 and [2^-96], and the error of [h m] is the same [f64] with an
    FMA as without. *)
Local Lemma mu_step :
  forall fma m P st k d,
  is_finite m = true -> / 2 <= B2R m < 1 ->
  st_inv P st k d -> 0 <= k <= 14 -> 0 <= d <= bpow radix2 (-90) ->
  bpow radix2 (-8) <= P * B2R m ->
  st_inv (P * B2R m) (mu_st fma m st) (k + 2) (d + bpow radix2 (-96)) /\
  mu_st true m st = mu_st false m st.
Proof.
intros fma m P [h l] k d Fm Hm (Fh & Fl & Hh & Hl & Hp & HP) Hk Hd HP2.
cbn [fst snd] in Fh, Fl, Hh, Hl, Hp.
unfold mu_st; cbn [fst snd].
pose proof (bpow_gt_0 radix2 (-9)) as B9.
pose proof (bpow_gt_0 radix2 (-8)) as B8.
assert (Ah : Rabs (B2R h) <= 1) by (rewrite Rabs_pos_eq; lra).
assert (Am : Rabs (B2R m) <= 1) by (rewrite Rabs_pos_eq; lra).
assert (A1 : Rabs (B2R h * B2R m) <= 1) by (rewrite Rabs_pos_eq by nra; nra).
assert (A16 : Rabs (B2R h * B2R m) <= 16) by lra.
assert (Ahm : bpow radix2 (-900) <= Rabs (B2R h * B2R m)).
{ rewrite Rabs_pos_eq by nra. clear - Hh Hm. num. nra. }
destruct (prod_exact true h m Fh Fm Ah Am Ahm) as (Fs & _ & X1).
destruct (prod_exact false h m Fh Fm Ah Am Ahm) as (_ & _ & X0).
assert (Xf : Generic.two_prod_is_exact fma h m (mul h m) = true) by (destruct fma; assumption).
destruct (two_prod_err_correct fma h m Fh Fm Xf) as (_ & _ & _ & Fe & Re).
destruct (mul_e h m Fh Fm A16) as (_ & _ & Bs).
assert (Al : Rabs (B2R l) <= 1) by (clear - Hl Hk Hh B9; num; nra).
assert (A2' : Rabs (B2R l * B2R m) <= 1).
{ rewrite Rabs_mult. pose proof (Rabs_pos (B2R l)). pose proof (Rabs_pos (B2R m)). nra. }
assert (A2 : Rabs (B2R l * B2R m) <= 16) by lra.
destruct (mul_e l m Fl Fm A2) as (Fv & _ & Bv).
set (e := Generic.two_prod_err fma h m (mul h m)) in *.
set (v := mul l m) in *.
assert (A3 : Rabs (B2R e + B2R v) <= 16).
{ pose proof (Rabs_triang (B2R e) (B2R v)) as T1.
  pose proof (Rabs_triang_inv (B2R v) (B2R l * B2R m)) as T2.
  assert (Ae : Rabs (B2R e) = Rabs (B2R (mul h m) - B2R h * B2R m))
    by (rewrite Re, Rabs_minus_sym; reflexivity).
  clear - T1 T2 Ae Bs Bv A1 A2'. num. lra. }
destruct (add_e e v Fe Fv A3) as (Fl' & _ & Bl').
destruct (mu_real k d P (B2R h) (B2R l) (B2R m) (B2R (mul h m)) (B2R e) (B2R v) (B2R (add e v))
  Hk Hd Hh Hl Hp HP Hm HP2 Bs Re Bv Bl') as (G1 & G2 & G3).
pose proof (abs_le_inv _ _ (mul_le_1 h m Fh Fm A1)) as S1.
split.
- unfold st_inv; cbn [fst snd].
  split; [exact Fs|]. split; [exact Fl'|]. split; [split; [exact G3 | lra]|].
  split; [exact G1|]. split; [exact G2|]. split; [exact HP2 | nra].
- rewrite (two_prod_err_fma_eq h m Fh Fm X1 X0). reflexivity.
Qed.

(** ** The loop for each [a] *)

(** Powers of 2 as numerals in the goal, for [lra]. *)
Local Ltac bnd := cbn [bpow radix_val radix2 Z.opp]; lra.

(** [r^a] is in [[2^-8, 1]] for [r] in [[1/2, 1)] and [1 <= a <= 8] (as
    [FastPowi.v]). *)
Local Lemma pow_range :
  forall r a, / 2 <= r < 1 -> (1 <= a <= 8)%Z -> bpow radix2 (-8) <= powerRZ r a <= 1.
Proof.
intros r a Hr Ha.
destruct a as [|p|p]; [lia| |lia]. cbn [powerRZ].
assert (Hn : (1 <= Pos.to_nat p <= 8)%nat) by (pose proof (positive_nat_Z p); lia).
assert (L : forall n, bpow radix2 (- Z.of_nat n) <= r ^ n <= 1).
{ intros n. induction n as [|n IH].
  - cbn [pow]. change (bpow radix2 (- Z.of_nat 0)) with 1. lra.
  - replace (- Z.of_nat (S n))%Z with (- Z.of_nat n + -1)%Z by lia.
    rewrite bpow_plus. change (bpow radix2 (-1)) with (/ 2). cbn [pow].
    pose proof (bpow_gt_0 radix2 (- Z.of_nat n)). destruct IH as [IH1 IH2]. split; nra. }
destruct (L (Pos.to_nat p)) as [L1 L2]. split; [|exact L2].
apply Rle_trans with (bpow radix2 (- Z.of_nat (Pos.to_nat p))); [apply bpow_le; lia | exact L1].
Qed.

(** [sq_step] for [P = r^j]. *)
Local Lemma sq_pow :
  forall fma r j st k d, / 2 <= r < 1 -> (1 <= 2 * j <= 8)%Z ->
  st_inv (powerRZ r j) st k d -> 0 <= k <= 14 -> 0 <= d <= bpow radix2 (-90) ->
  st_inv (powerRZ r (2 * j)) (sq_st fma st) (2 * k + 2) (2 * d + bpow radix2 (-96)) /\
  sq_st true st = sq_st false st.
Proof.
intros fma r j st k d Hr Hj I Hk Hd.
assert (E : powerRZ r (2 * j) = powerRZ r j * powerRZ r j).
{ replace (2 * j)%Z with (j + j)%Z by lia. apply powerRZ_add. lra. }
pose proof (pow_range r (2 * j) Hr Hj) as R.
rewrite E in R |- *. apply sq_step; [exact I | exact Hk | exact Hd | lra].
Qed.

(** [mu_step] for [P = m^j]. *)
Local Lemma mu_pow :
  forall fma m j st k d, is_finite m = true -> / 2 <= B2R m < 1 -> (1 <= j + 1 <= 8)%Z ->
  st_inv (powerRZ (B2R m) j) st k d -> 0 <= k <= 14 -> 0 <= d <= bpow radix2 (-90) ->
  st_inv (powerRZ (B2R m) (j + 1)) (mu_st fma m st) (k + 2) (d + bpow radix2 (-96)) /\
  mu_st true m st = mu_st false m st.
Proof.
intros fma m j st k d Fm Hm Hj I Hk Hd.
assert (E : powerRZ (B2R m) (j + 1) = powerRZ (B2R m) j * B2R m).
{ rewrite powerRZ_add by lra. rewrite powerRZ_1. reflexivity. }
pose proof (pow_range (B2R m) (j + 1) Hm Hj) as R.
rewrite E in R |- *. apply mu_step; [exact Fm | exact Hm | exact I | exact Hk | exact Hd | lra].
Qed.

(** The loop starts from [(m, 0)], which is [m^1] exactly. *)
Local Lemma inv0 :
  forall m : f64,
  is_finite m = true -> / 2 <= B2R m < 1 -> st_inv (powerRZ (B2R m) 1) (m, zero) 0 0.
Proof.
intros m Fm Hm. rewrite powerRZ_1. unfold st_inv; cbn [fst snd].
replace (B2R zero) with 0 by reflexivity.
replace (B2R m - (B2R m + 0)) with 0 by ring. rewrite Rabs_R0.
split; [exact Fm|]. split; [reflexivity|].
assert (bpow radix2 (-8) <= / 2) by bnd. assert (bpow radix2 (-9) <= / 2) by bnd.
lra.
Qed.

(** The invariant at the end of the loop, with [k <= 16] and [d <= 2^-80],
    is the conclusion of [small_loop_correct]. *)
Local Lemma finish :
  forall P st h l k d, st_inv P st k d -> st = (h, l) -> k <= 16 -> d <= bpow radix2 (-80) ->
  is_finite h = true /\ is_finite l = true /\ 0 < B2R h /\
  Rabs (B2R l) <= bpow radix2 (-49) * B2R h /\
  Rabs (P - (B2R h + B2R l)) <= bpow radix2 (-80) * P.
Proof.
intros P st h l k d I E Hk Hd. subst st.
destruct I as (Fh & Fl & Hh & Hl & Hp & HP). cbn [fst snd] in Fh, Fl, Hh, Hl, Hp.
pose proof (bpow_gt_0 radix2 (-9)) as B9. pose proof (bpow_gt_0 radix2 (-8)) as B8.
pose proof (bpow_gt_0 radix2 (-53)) as B53.
split; [exact Fh|]. split; [exact Fl|]. split; [lra|]. split.
- replace (bpow radix2 (-49)) with (16 * bpow radix2 (-53)) by bnd.
  apply Rle_trans with (1 := Hl).
  apply Rmult_le_compat_r; [lra|]. apply Rmult_le_compat_r; lra.
- apply Rle_trans with (1 := Hp). apply Rmult_le_compat_r; lra.
Qed.

(** [small_loop] from [(m, 0)] gives [m^a] as [h + l] within [2^-80 m^a],
    with [0 < h] and [|l| <= 2^-49 h]. *)
Theorem small_loop_correct :
  forall fma a m h l,
  (1 <= a <= 8)%Z -> is_finite m = true -> / 2 <= B2R m < 1 ->
  DyadicPow.small_loop fma a m (Z.to_nat (DyadicPow.ilog2 a)) m zero = (h, l) ->
  is_finite h = true /\ is_finite l = true /\ 0 < B2R h /\
  Rabs (B2R l) <= bpow radix2 (-49) * B2R h /\
  Rabs (powerRZ (B2R m) a - (B2R h + B2R l)) <= bpow radix2 (-80) * powerRZ (B2R m) a.
Proof.
intros fma a m h l Ha Fm Hm E.
pose proof (inv0 m Fm Hm) as I1.
assert (Ca : a = 1%Z \/ a = 2%Z \/ a = 3%Z \/ a = 4%Z \/ a = 5%Z \/ a = 6%Z \/ a = 7%Z \/
  a = 8%Z) by lia.
destruct Ca as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
- rewrite chain1 in E. apply (finish _ _ _ _ _ _ I1 E); [lra | bnd].
- rewrite chain2 in E.
  destruct (sq_pow fma (B2R m) 1 _ _ _ Hm ltac:(lia) I1 ltac:(lra) ltac:(bnd)) as (I2 & _).
  apply (finish _ _ _ _ _ _ I2 E); [lra | bnd].
- rewrite chain3 in E.
  destruct (sq_pow fma (B2R m) 1 _ _ _ Hm ltac:(lia) I1 ltac:(lra) ltac:(bnd)) as (I2 & _).
  destruct (mu_pow fma m 2 _ _ _ Fm Hm ltac:(lia) I2 ltac:(lra) ltac:(bnd)) as (I3 & _).
  apply (finish _ _ _ _ _ _ I3 E); [lra | bnd].
- rewrite chain4 in E.
  destruct (sq_pow fma (B2R m) 1 _ _ _ Hm ltac:(lia) I1 ltac:(lra) ltac:(bnd)) as (I2 & _).
  destruct (sq_pow fma (B2R m) 2 _ _ _ Hm ltac:(lia) I2 ltac:(lra) ltac:(bnd)) as (I4 & _).
  apply (finish _ _ _ _ _ _ I4 E); [lra | bnd].
- rewrite chain5 in E.
  destruct (sq_pow fma (B2R m) 1 _ _ _ Hm ltac:(lia) I1 ltac:(lra) ltac:(bnd)) as (I2 & _).
  destruct (sq_pow fma (B2R m) 2 _ _ _ Hm ltac:(lia) I2 ltac:(lra) ltac:(bnd)) as (I4 & _).
  destruct (mu_pow fma m 4 _ _ _ Fm Hm ltac:(lia) I4 ltac:(lra) ltac:(bnd)) as (I5 & _).
  apply (finish _ _ _ _ _ _ I5 E); [lra | bnd].
- rewrite chain6 in E.
  destruct (sq_pow fma (B2R m) 1 _ _ _ Hm ltac:(lia) I1 ltac:(lra) ltac:(bnd)) as (I2 & _).
  destruct (mu_pow fma m 2 _ _ _ Fm Hm ltac:(lia) I2 ltac:(lra) ltac:(bnd)) as (I3 & _).
  destruct (sq_pow fma (B2R m) 3 _ _ _ Hm ltac:(lia) I3 ltac:(lra) ltac:(bnd)) as (I6 & _).
  apply (finish _ _ _ _ _ _ I6 E); [lra | bnd].
- rewrite chain7 in E.
  destruct (sq_pow fma (B2R m) 1 _ _ _ Hm ltac:(lia) I1 ltac:(lra) ltac:(bnd)) as (I2 & _).
  destruct (mu_pow fma m 2 _ _ _ Fm Hm ltac:(lia) I2 ltac:(lra) ltac:(bnd)) as (I3 & _).
  destruct (sq_pow fma (B2R m) 3 _ _ _ Hm ltac:(lia) I3 ltac:(lra) ltac:(bnd)) as (I6 & _).
  destruct (mu_pow fma m 6 _ _ _ Fm Hm ltac:(lia) I6 ltac:(lra) ltac:(bnd)) as (I7 & _).
  apply (finish _ _ _ _ _ _ I7 E); [lra | bnd].
- rewrite chain8 in E.
  destruct (sq_pow fma (B2R m) 1 _ _ _ Hm ltac:(lia) I1 ltac:(lra) ltac:(bnd)) as (I2 & _).
  destruct (sq_pow fma (B2R m) 2 _ _ _ Hm ltac:(lia) I2 ltac:(lra) ltac:(bnd)) as (I4 & _).
  destruct (sq_pow fma (B2R m) 4 _ _ _ Hm ltac:(lia) I4 ltac:(lra) ltac:(bnd)) as (I8 & _).
  apply (finish _ _ _ _ _ _ I8 E); [lra | bnd].
Qed.

(** [small_loop] gives the same result with an FMA as without. *)
Theorem small_loop_fma :
  forall a m,
  (1 <= a <= 8)%Z -> is_finite m = true -> / 2 <= B2R m < 1 ->
  DyadicPow.small_loop true a m (Z.to_nat (DyadicPow.ilog2 a)) m zero =
  DyadicPow.small_loop false a m (Z.to_nat (DyadicPow.ilog2 a)) m zero.
Proof.
intros a m Ha Fm Hm.
pose proof (inv0 m Fm Hm) as I1.
assert (Ca : a = 1%Z \/ a = 2%Z \/ a = 3%Z \/ a = 4%Z \/ a = 5%Z \/ a = 6%Z \/ a = 7%Z \/
  a = 8%Z) by lia.
(* Along the loop without an FMA, each step gives the same state with
   an FMA as without, innermost first. *)
destruct Ca as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
- rewrite !chain1. reflexivity.
- rewrite !chain2.
  destruct (sq_pow false (B2R m) 1 _ _ _ Hm ltac:(lia) I1 ltac:(lra) ltac:(bnd)) as (_ & Q1).
  rewrite Q1. reflexivity.
- rewrite !chain3.
  destruct (sq_pow false (B2R m) 1 _ _ _ Hm ltac:(lia) I1 ltac:(lra) ltac:(bnd)) as (I2 & Q1).
  destruct (mu_pow false m 2 _ _ _ Fm Hm ltac:(lia) I2 ltac:(lra) ltac:(bnd)) as (_ & Q2).
  rewrite Q1, Q2. reflexivity.
- rewrite !chain4.
  destruct (sq_pow false (B2R m) 1 _ _ _ Hm ltac:(lia) I1 ltac:(lra) ltac:(bnd)) as (I2 & Q1).
  destruct (sq_pow false (B2R m) 2 _ _ _ Hm ltac:(lia) I2 ltac:(lra) ltac:(bnd)) as (_ & Q2).
  rewrite Q1, Q2. reflexivity.
- rewrite !chain5.
  destruct (sq_pow false (B2R m) 1 _ _ _ Hm ltac:(lia) I1 ltac:(lra) ltac:(bnd)) as (I2 & Q1).
  destruct (sq_pow false (B2R m) 2 _ _ _ Hm ltac:(lia) I2 ltac:(lra) ltac:(bnd)) as (I4 & Q2).
  destruct (mu_pow false m 4 _ _ _ Fm Hm ltac:(lia) I4 ltac:(lra) ltac:(bnd)) as (_ & Q3).
  rewrite Q1, Q2, Q3. reflexivity.
- rewrite !chain6.
  destruct (sq_pow false (B2R m) 1 _ _ _ Hm ltac:(lia) I1 ltac:(lra) ltac:(bnd)) as (I2 & Q1).
  destruct (mu_pow false m 2 _ _ _ Fm Hm ltac:(lia) I2 ltac:(lra) ltac:(bnd)) as (I3 & Q2).
  destruct (sq_pow false (B2R m) 3 _ _ _ Hm ltac:(lia) I3 ltac:(lra) ltac:(bnd)) as (_ & Q3).
  rewrite Q1, Q2, Q3. reflexivity.
- rewrite !chain7.
  destruct (sq_pow false (B2R m) 1 _ _ _ Hm ltac:(lia) I1 ltac:(lra) ltac:(bnd)) as (I2 & Q1).
  destruct (mu_pow false m 2 _ _ _ Fm Hm ltac:(lia) I2 ltac:(lra) ltac:(bnd)) as (I3 & Q2).
  destruct (sq_pow false (B2R m) 3 _ _ _ Hm ltac:(lia) I3 ltac:(lra) ltac:(bnd)) as (I6 & Q3).
  destruct (mu_pow false m 6 _ _ _ Fm Hm ltac:(lia) I6 ltac:(lra) ltac:(bnd)) as (_ & Q4).
  rewrite Q1, Q2, Q3, Q4. reflexivity.
- rewrite !chain8.
  destruct (sq_pow false (B2R m) 1 _ _ _ Hm ltac:(lia) I1 ltac:(lra) ltac:(bnd)) as (I2 & Q1).
  destruct (sq_pow false (B2R m) 2 _ _ _ Hm ltac:(lia) I2 ltac:(lra) ltac:(bnd)) as (I4 & Q2).
  destruct (sq_pow false (B2R m) 4 _ _ _ Hm ltac:(lia) I4 ltac:(lra) ltac:(bnd)) as (_ & Q3).
  rewrite Q1, Q2, Q3. reflexivity.
Qed.
