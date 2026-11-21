(** * The small powers of the dyadic [pown]

    [DyadicPow.pown_small fma x k g] of [Model.v] takes [x^k] for a finite
    normal [x > 0] in [[2^g, 2^(g+1))] and [1 <= |k| <= 8] as [(h, l,
    e)]: [x = m 2^(g+1)] with [m] in [[1/2, 1)], the [f64] whose bits are
    those of [x] under the exponent of 1/2, [m^|k|] as [h + l] from
    [small_loop] ([FastPowiLoop.small_loop_correct]), made [h = RN(h + l)]
    by [Fast.fast_two_sum] and scaled to [[1, 2)] by [Fast.normalize]
    ([FastRoundErr.normalize_correct]), and for [k < 0] the quotient of 1
    by it ([FastDiv.dd_div_correct]), scaled again. [pown_small_correct]
    shows that [x^k 2^-e] is within [2^-67] of [h + l], with [1 <= h < 2],
    [h = RN(h + l)] and [-1085 <= e], at the [x] and [k] that the
    underflow rule of [pown_pos] leaves, where the bound [2^((g+1) k)] of
    [x^k] for [k > 0], and [2^(g k)] for [k < 0], is above [2^-1075].
    [pown_small_dir_correct] and
    [pown_small_near_correct] then show that [pown_small_dir] and
    [pown_small_near] return, where they return, [x^k] rounded in their
    direction, from the tests of [FastRoundWideErr.v], and
    [pown_small_fma], [pown_small_dir_fma] and [pown_small_near_fma] that
    an FMA gives the same results ([FastPowiLoop.small_loop_fma] and
    [FastDiv.dd_div_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Fushimi Require Import Model Mpfr Elementary Encoding TwoSum TwoProduct DyDriver NearF64
  FastRound FastRoundErr FastRoundWideErr FastDiv FastPowiLoop.
From Fushimi Require Limbs FastLogReduce FastLogNorm DyPowRules.

Open Scope R_scope.

Local Ltac num := cbn [bpow radix_val radix2] in *; lra.

(** ** Helpers *)

(** As in [FastAhypAtanh.v]: RN keeps a number on the same side of a power
    of 2, and a normal [h = RN x] is within [2^-53 |h|] of [x]. *)
Local Lemma rn_ge_bpow :
  forall e y, (-1073 <= e)%Z -> bpow radix2 e <= y -> bpow radix2 e <= RN y.
Proof.
intros e y He Hy. apply round_ge_generic; [typeclasses eauto | typeclasses eauto | | exact Hy].
apply generic_format_bpow. unfold FLT_exp. lia.
Qed.

Local Lemma rn_low :
  forall h x, h = RN x -> bpow radix2 (-1022) <= Rabs h ->
  Rabs (x - h) <= bpow radix2 (-53) * Rabs h.
Proof.
intros h x Eh Hh.
assert (E : Rabs (RN x - x) <= / 2 * ulp radix2 fexp64 (RN x))
  by (apply error_le_half_ulp_round; typeclasses eauto).
rewrite <- Eh in E.
pose proof (ulp_FLT_le radix2 (-1074) 53 h Hh) as U. change (1 - 53)%Z with (-52)%Z in U.
rewrite Rabs_minus_sym.
apply Rle_trans with (/ 2 * ulp radix2 fexp64 h); [exact E|].
pose proof (Rabs_pos h). cbn [bpow radix_val radix2] in *. lra.
Qed.

(** [|l| <= 2^-53 h] for an [h = RN(h + l)] of at least [2^-1022]. *)
Local Lemma rn_low_pos :
  forall h l : f64, B2R h = RN (B2R h + B2R l) -> bpow radix2 (-1022) <= B2R h ->
  Rabs (B2R l) <= bpow radix2 (-53) * B2R h.
Proof.
intros h l Rh Hh.
pose proof (bpow_gt_0 radix2 (-1022)) as P0.
assert (Hn : bpow radix2 (-1022) <= Rabs (B2R h)) by (rewrite Rabs_pos_eq; lra).
pose proof (rn_low (B2R h) (B2R h + B2R l) Rh Hn) as L.
replace (B2R h + B2R l - B2R h) with (B2R l) in L by ring.
rewrite (Rabs_pos_eq (B2R h)) in L by lra. exact L.
Qed.

(** [r^a] is in [[2^-8, 1]] for [r] in [[1/2, 1)] and [1 <= a <= 8]. *)
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

Local Lemma bpow_pow : forall c n, bpow radix2 c ^ n = bpow radix2 (c * Z.of_nat n).
Proof.
intros c n. induction n as [|n IH].
- cbn [pow]. rewrite Z.mul_0_r. reflexivity.
- cbn [pow]. rewrite IH, <- bpow_plus. f_equal. rewrite Nat2Z.inj_succ. ring.
Qed.

(** The [f64] [m] whose bits are those of a finite [x > 0] under the
    exponent of 1/2 is in [[1/2, 1)], and [x = m 2^(g+1)] for the [g =
    expo x] of a normal [x] (as [FastLogReduce.split_normal]). *)
Local Lemma mant_bits :
  forall x, is_finite x = true -> 0 < B2R x ->
  is_finite (from_bits (Z.lor (Z.land (to_bits x) DyadicLog.frac) 0x3fe0000000000000)) = true /\
  / 2 <= B2R (from_bits (Z.lor (Z.land (to_bits x) DyadicLog.frac) 0x3fe0000000000000)) < 1 /\
  ((-1022 <= DyadicPow.expo x)%Z ->
   B2R x = B2R (from_bits (Z.lor (Z.land (to_bits x) DyadicLog.frac) 0x3fe0000000000000)) *
     bpow radix2 (DyadicPow.expo x + 1)).
Proof.
intros x Fx Hx.
pose proof (DyPowRules.expo_spec x Fx (Rgt_not_eq _ _ Hx)) as Hg.
rewrite Rabs_pos_eq in Hg by lra.
destruct (FastLogReduce.pos_bits x Fx Hx) as (c & Hc & Eb & Ev).
rewrite Eb.
assert (HcE : (c = c / 2 ^ 52 * 2 ^ 52 + c mod 2 ^ 52 /\ 0 <= c / 2 ^ 52 <= 2046 /\
  0 <= c mod 2 ^ 52 < 2 ^ 52)%Z) by zlia.
assert (Ef : Z.land c DyadicLog.frac = (c mod 2 ^ 52)%Z).
{ change DyadicLog.frac with (Z.ones 52). apply Z.land_ones. lia. }
rewrite Ef.
pose proof (magnitude_bounds c ltac:(lia)) as (Hb0 & Hb1).
set (E := (c / 2 ^ 52)%Z) in *. set (M := (c mod 2 ^ 52)%Z) in *.
clearbody E M. destruct HcE as (HcE & HE & HM).
replace 0x3fe0000000000000%Z with (1022 * 2 ^ 52)%Z by reflexivity.
rewrite Z.lor_comm, Limbs.lor_low by lia.
(* [m] is the pattern [1022 2^52 + M], so its value is [(M + 2^52) 2^-53]. *)
destruct (from_bits_finite false (1022 * 2 ^ 52 + M)) as (Fm & _ & Em);
  [split; [lia | simpl Z.pow in *; lia] |].
unfold sign_bit in Fm, Em. rewrite Z.add_0_l in Fm, Em. cbv iota in Em.
rewrite magnitude_split in Em by lia.
change (1022 =? 0)%Z with false in Em. cbv iota in Em.
change (Z.max 1022 1 - 1075)%Z with (-53)%Z in Em.
set (m := from_bits (1022 * 2 ^ 52 + M)) in *.
assert (Vm : B2R m = IZR (M + 2 ^ 52) * bpow radix2 (-53)) by (rewrite Em; reflexivity).
assert (I1 : IZR (2 ^ 52) <= IZR (M + 2 ^ 52)) by (apply IZR_le; lia).
assert (I2 : IZR (M + 2 ^ 52) < IZR (2 ^ 53)) by (apply IZR_lt; simpl Z.pow in *; lia).
change (IZR (2 ^ 52)) with (bpow radix2 52) in I1.
change (IZR (2 ^ 53)) with (bpow radix2 53) in I2.
split; [exact Fm|]. split; [rewrite Vm; num|].
intros Hg1.
destruct (Z.eq_dec E 0) as [E0|E0].
- (* A subnormal [x] is below [2^-1022 <= 2^g]. *)
  exfalso. rewrite E0 in Hb0. replace (0 - 1022)%Z with (-1022)%Z in Hb0 by lia.
  assert (B : bpow radix2 (-1022) <= bpow radix2 (DyadicPow.expo x)) by (apply bpow_le; lia).
  rewrite <- Ev in Hb0. lra.
- (* [2^(E-1023) <= x < 2^(E-1022)], so [g = E - 1023]. *)
  specialize (Hb1 E0). rewrite <- Ev in Hb0, Hb1.
  assert (G1 : (DyadicPow.expo x < E - 1022)%Z) by (apply (lt_bpow radix2); lra).
  assert (G2 : (E - 1023 < DyadicPow.expo x + 1)%Z) by (apply (lt_bpow radix2); lra).
  replace (DyadicPow.expo x + 1)%Z with (E - 1022)%Z by lia.
  rewrite Ev, HcE, magnitude_split by lia.
  replace (E =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact E0).
  replace (Z.max E 1 - 1075)%Z with (E - 1075)%Z by lia.
  rewrite Vm. unfold F2R; cbn [Fnum Fexp]. rewrite Rmult_assoc, <- bpow_plus.
  f_equal. f_equal. ring.
Qed.

(** [Fast.normalize] of an [h = RN(h + l)] in [[2^c, 2)] scales [h + l]
    by [2^-j] exactly, with [c <= j <= 0], into an [h'] in [[1, 2)]
    ([FastRoundErr.normalize_correct]). *)
Local Lemma norm :
  forall h l h' l' j c,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  (-1021 <= c)%Z -> bpow radix2 c <= B2R h < 2 -> Fast.normalize h l = (h', l', j) ->
  is_finite h' = true /\ is_finite l' = true /\ (c <= j <= 0)%Z /\
  B2R h' + B2R l' = (B2R h + B2R l) * bpow radix2 (- j) /\
  1 <= B2R h' < 2 /\ B2R h' = RN (B2R h' + B2R l').
Proof.
intros h l h' l' j c Fh Fl Rh Hc Hh E.
assert (Hh' : bpow radix2 (-1021) <= B2R h < 2).
{ split; [|lra]. apply Rle_trans with (bpow radix2 c); [apply bpow_le; exact Hc | lra]. }
pose proof (FastRoundErr.normalize_correct h l Fh Fl Rh Hh') as C.
rewrite E in C. cbv beta iota in C.
destruct C as (Fh' & Fl' & Hj & Eh & El & Bj & Rh').
assert (Hcj : (c <= j)%Z).
{ assert (L : bpow radix2 c < bpow radix2 (j + 1)) by lra. apply lt_bpow in L. lia. }
set (B := bpow radix2 (- j)) in *.
assert (PB : 0 < B) by apply bpow_gt_0.
assert (E1 : bpow radix2 j * B = 1).
{ unfold B. rewrite <- bpow_plus, Z.add_opp_diag_r. reflexivity. }
assert (E2 : bpow radix2 (j + 1) * B = 2).
{ unfold B. rewrite <- bpow_plus. replace (j + 1 + - j)%Z with 1%Z by lia. reflexivity. }
split; [exact Fh'|]. split; [exact Fl'|]. split; [lia|].
split; [rewrite Eh, El; ring|]. split; [|exact Rh'].
rewrite Eh. split.
- apply Rle_trans with (bpow radix2 j * B); [lra | apply Rmult_le_compat_r; lra].
- apply Rlt_le_trans with (bpow radix2 (j + 1) * B); [apply Rmult_lt_compat_r; lra | lra].
Qed.

(** The steps of [pown_small] after [small_loop]: for an [h0 + l0] within
    [2^-80 P] of a [P] in [[2^-8, 1]], with [|l0| <= 2^-49 h0],
    [Fast.fast_two_sum] makes [h1 = RN(h1 + l1)] with [h1 + l1 = h0 + l0]
    ([FastLogNorm.fts_exact]), and [Fast.normalize] scales it by [2^-j]
    into [h2] in [[1, 2)], with [-9 <= j <= 0] as [h1 >= 2^-9]. *)
Local Lemma mid :
  forall h0 l0 P h1 l1 h2 l2 j,
  is_finite h0 = true -> is_finite l0 = true -> 0 < B2R h0 ->
  Rabs (B2R l0) <= bpow radix2 (-49) * B2R h0 ->
  bpow radix2 (-8) <= P <= 1 ->
  Rabs (P - (B2R h0 + B2R l0)) <= bpow radix2 (-80) * P ->
  Fast.fast_two_sum h0 l0 = (h1, l1) -> Fast.normalize h1 l1 = (h2, l2, j) ->
  is_finite h2 = true /\ is_finite l2 = true /\ B2R h2 = RN (B2R h2 + B2R l2) /\
  1 <= B2R h2 < 2 /\ Rabs (B2R l2) <= bpow radix2 (-53) * B2R h2 /\ (-9 <= j <= 0)%Z /\
  Rabs (P * bpow radix2 (- j) - (B2R h2 + B2R l2)) <= bpow radix2 (-80) * (P * bpow radix2 (- j)).
Proof.
intros h0 l0 P h1 l1 h2 l2 j Fh0 Fl0 Hh0 Hl0 HP Herr E1 E2.
pose proof (Rabs_le_inv _ _ Herr) as Herr'.
pose proof (Rabs_le_inv _ _ Hl0) as Hl0'.
assert (HS : bpow radix2 (-9) <= B2R h0 + B2R l0 <= 3 / 2) by num.
destruct (FastLogNorm.fts_exact h0 l0 h1 l1 Fh0 Fl0) as (Fh1 & Fl1 & Rh1 & S1).
{ left. rewrite (Rabs_pos_eq (B2R h0)) by lra. num. }
{ rewrite Rabs_pos_eq; num. }
{ exact E1. }
assert (Rh1' : B2R h1 = RN (B2R h1 + B2R l1)) by (rewrite S1; exact Rh1).
assert (Hh1 : bpow radix2 (-9) <= B2R h1) by (rewrite Rh1; apply rn_ge_bpow; [lia | lra]).
assert (L1 : Rabs (B2R l1) <= bpow radix2 (-53) * B2R h1).
{ apply rn_low_pos; [exact Rh1' |].
  apply Rle_trans with (bpow radix2 (-9)); [apply bpow_le; lia | lra]. }
(* [h1 + l1 = h0 + l0 <= 3/2] and [|l1| <= 2^-53 h1] keep [h1] below 2. *)
assert (Hh1' : B2R h1 < 2) by (pose proof (Rabs_le_inv _ _ L1); num).
destruct (norm h1 l1 h2 l2 j (-9) Fh1 Fl1 Rh1' ltac:(lia) (conj Hh1 Hh1') E2)
  as (Fh2 & Fl2 & Hj & S2 & Hh2 & Rh2).
assert (L2 : Rabs (B2R l2) <= bpow radix2 (-53) * B2R h2).
{ apply rn_low_pos; [exact Rh2 |].
  apply Rle_trans with 1; [apply (bpow_le radix2 (-1022) 0); lia | lra]. }
split; [exact Fh2|]. split; [exact Fl2|]. split; [exact Rh2|]. split; [exact Hh2|].
split; [exact L2|]. split; [lia|].
rewrite S2, S1.
replace (P * bpow radix2 (- j) - (B2R h0 + B2R l0) * bpow radix2 (- j))
  with ((P - (B2R h0 + B2R l0)) * bpow radix2 (- j)) by ring.
rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (- j))) by apply bpow_ge_0.
rewrite <- Rmult_assoc. apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Herr].
Qed.

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (as in [FastExp.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

Local Lemma lit_err67 : B2R DyadicExp.err67 = bpow radix2 (-67).
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

(** The common prefix of [pown_small] for [1 <= a <= 8]: [small_loop]
    ([FastPowiLoop.small_loop_correct]), then [mid], with [P = m^a]. *)
Local Lemma pre :
  forall fma a m h0 l0 h1 l1 h2 l2 j,
  (1 <= a <= 8)%Z -> is_finite m = true -> / 2 <= B2R m < 1 ->
  DyadicPow.small_loop fma a m (Z.to_nat (DyadicPow.ilog2 a)) m zero = (h0, l0) ->
  Fast.fast_two_sum h0 l0 = (h1, l1) -> Fast.normalize h1 l1 = (h2, l2, j) ->
  bpow radix2 (-8) <= powerRZ (B2R m) a <= 1 /\
  is_finite h2 = true /\ is_finite l2 = true /\ B2R h2 = RN (B2R h2 + B2R l2) /\
  1 <= B2R h2 < 2 /\ Rabs (B2R l2) <= bpow radix2 (-53) * B2R h2 /\ (-9 <= j <= 0)%Z /\
  Rabs (powerRZ (B2R m) a * bpow radix2 (- j) - (B2R h2 + B2R l2))
    <= bpow radix2 (-80) * (powerRZ (B2R m) a * bpow radix2 (- j)).
Proof.
intros fma a m h0 l0 h1 l1 h2 l2 j Ha Fm Hm E0 E1 E2.
destruct (FastPowiLoop.small_loop_correct fma a m h0 l0 Ha Fm Hm E0)
  as (Fh0 & Fl0 & Hh0 & Hl0 & Herr).
pose proof (pow_range (B2R m) a Hm Ha) as HP.
split; [exact HP|].
exact (mid h0 l0 _ h1 l1 h2 l2 j Fh0 Fl0 Hh0 Hl0 HP Herr E1 E2).
Qed.

(** [x^k 2^-e] for [x = m 2^c] and [e = c k + j]. *)
Local Lemma pow_pos_scale :
  forall m c p j,
  powerRZ (m * bpow radix2 c) (Z.pos p) * bpow radix2 (- (c * Z.pos p + j)) =
  powerRZ m (Z.pos p) * bpow radix2 (- j).
Proof.
intros m c p j. cbn [powerRZ]. rewrite Rpow_mult_distr, bpow_pow, positive_nat_Z.
rewrite Rmult_assoc, <- bpow_plus. f_equal. f_equal. ring.
Qed.

(** [x^-a 2^-(j2 - e)] for [x = m 2^c] and [e = c a + j]. *)
Local Lemma pow_neg_scale :
  forall m c p j j2, 0 < m ->
  powerRZ (m * bpow radix2 c) (Z.neg p) * bpow radix2 (- (j2 - (c * Z.pos p + j))) =
  / (powerRZ m (Z.pos p) * bpow radix2 (- j)) * bpow radix2 (- j2).
Proof.
intros m c p j j2 Hm. cbn [powerRZ]. rewrite Rpow_mult_distr, bpow_pow, positive_nat_Z.
pose proof (pow_lt m (Pos.to_nat p) Hm) as Hp.
replace (- (j2 - (c * Z.pos p + j)))%Z with (c * Z.pos p + j + - j2)%Z by ring.
rewrite !bpow_plus, (bpow_opp radix2 j).
pose proof (bpow_gt_0 radix2 (c * Z.pos p)). pose proof (bpow_gt_0 radix2 j).
field. repeat split; apply Rgt_not_eq; lra.
Qed.

(** An [h + l] with [h] in [[1, 2)] and [|l| <= 2^-53 h] is in [[3/4, 3]]. *)
Local Lemma dd_range :
  forall h l, 1 <= h < 2 -> Rabs l <= bpow radix2 (-53) * h -> 3 / 4 <= h + l <= 3.
Proof.
intros h l Hh Hl. apply Rabs_le_inv in Hl.
assert (B : bpow radix2 (-53) * h <= bpow radix2 (-53) * 2)
  by (apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]).
num.
Qed.

(** A [W] within [2^-98 Q] of a [Q] in [[1/3, 4/3]] is in [[1/4, 7/5]]. *)
Local Lemma quo_range :
  forall Q W, / 3 <= Q <= 4 / 3 -> Rabs (W - Q) <= bpow radix2 (-98) * Q -> / 4 <= W <= 7 / 5.
Proof. intros Q W HQ HW. apply Rabs_le_inv in HW. num. Qed.

(** [V] within [2^-80 Q] and [W] within [2^-98 Q] of a [Q] in [(0, 4/3]]
    are within [2^-79] of each other. *)
Local Lemma tri :
  forall V Q W, 0 < Q <= 4 / 3 ->
  Rabs (V - Q) <= bpow radix2 (-80) * Q -> Rabs (W - Q) <= bpow radix2 (-98) * Q ->
  Rabs (V - W) <= bpow radix2 (-79).
Proof.
intros V Q W HQ HV HW. apply Rabs_le_inv in HV, HW. apply Rabs_le. num.
Qed.

(** The parts of an equation of [Some] triples ([injection] would try to
    compute the [expo x] in [e]). *)
Local Lemma some_eq :
  forall (h l h' l' : f64) (e e' : Z), Some (h, l, e) = Some (h', l', e') ->
  h = h' /\ l = l' /\ e = e'.
Proof.
intros h l h' l' e e' H.
apply (f_equal (fun o => match o with Some v => v | None => (h, l, e) end)) in H.
cbv beta iota in H. apply pair_equal_spec in H. destruct H as [H Ee].
apply pair_equal_spec in H. destruct H as [Eh El]. auto.
Qed.

(** ** [pown_small] *)

(** [x^k 2^-e] is within [2^-67] of [h + l], for a finite [x > 0] and [k
    <> 0] that the underflow rule of [pown_pos] leaves, where its bound of
    [x^k] is above [2^-1075]. *)
Theorem pown_small_correct :
  forall fma x k h l e,
  is_finite x = true -> 0 < B2R x -> k <> 0%Z ->
  (-1075 < if 0 <? k then (DyadicPow.expo x + 1) * k else DyadicPow.expo x * k)%Z ->
  DyadicPow.pown_small fma x k (DyadicPow.expo x) = Some (h, l, e) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  1 <= B2R h < 2 /\ (-1085 <= e)%Z /\
  Rabs (powerRZ (B2R x) k * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (-67).
Proof.
intros fma x k h l e Fx Hx Hk Hu H.
unfold DyadicPow.pown_small in H. cbv zeta in H.
destruct ((DyadicPow.small_max <? Z.abs k) || (DyadicPow.expo x <? -1022))%Z eqn:G;
  [discriminate H|].
apply Bool.orb_false_iff in G. destruct G as [G1 G2]. apply Z.ltb_ge in G1, G2.
assert (Ha : (1 <= Z.abs k <= 8)%Z) by (unfold DyadicPow.small_max in G1; lia).
destruct (mant_bits x Fx Hx) as (Fm & Hm & Ex). specialize (Ex G2).
set (m := from_bits (Z.lor (Z.land (to_bits x) DyadicLog.frac) 0x3fe0000000000000)) in *.
destruct (DyadicPow.small_loop fma (Z.abs k) m (Z.to_nat (DyadicPow.ilog2 (Z.abs k))) m zero)
  as [h0 l0] eqn:E0.
destruct (Fast.fast_two_sum h0 l0) as [h1 l1] eqn:E1.
destruct (Fast.normalize h1 l1) as [[h2 l2] j] eqn:E2.
destruct (pre fma (Z.abs k) m h0 l0 h1 l1 h2 l2 j Ha Fm Hm E0 E1 E2)
  as (HP & Fh2 & Fl2 & Rh2 & Hh2 & Hl2 & Hj & Herr).
rewrite Ex. clear Ex E0 E1 E2.
destruct k as [|p|p]; [lia | |].
- (* [k > 0]: [x^k 2^-e = m^k 2^-j]. *)
  change (Z.abs (Z.pos p)) with (Z.pos p) in *.
  change (0 <? Z.pos p)%Z with true in H, Hu. cbv beta iota in H, Hu.
  apply some_eq in H. destruct H as (Eh & El & Ee). subst h l e.
  split; [exact Fh2|]. split; [exact Fl2|]. split; [exact Rh2|]. split; [exact Hh2|].
  split; [lia|].
  rewrite pow_pos_scale.
  apply Rle_trans with (1 := Herr).
  assert (Bj : bpow radix2 (- j) <= bpow radix2 9) by (apply bpow_le; lia).
  pose proof (bpow_gt_0 radix2 (-8)) as B8.
  assert (PB : powerRZ (B2R m) (Z.pos p) * bpow radix2 (- j) <= 1 * bpow radix2 9)
    by (apply Rmult_le_compat; [lra | apply bpow_ge_0 | lra | exact Bj]).
  apply Rle_trans with (bpow radix2 (-80) * bpow radix2 9).
  + apply Rmult_le_compat_l; [apply bpow_ge_0 | lra].
  + rewrite <- bpow_plus. apply bpow_le. lia.
- (* [k < 0]: [x^k 2^-(j2 - e) = 2^-j2 / D] for [D = m^a 2^-j], within
     [2^-80 D] of [S = h2 + l2], and [qh + ql] is [1 / S] within [2^-98]
     ([FastDiv.dd_div_correct]), so [qh] is in [[1/4, 2)]. *)
  change (Z.abs (Z.neg p)) with (Z.pos p) in *.
  change (0 <? Z.neg p)%Z with false in H, Hu. cbv beta iota in H, Hu.
  destruct (Fast.dd_div fma Fast.one zero h2 l2) as [qh ql] eqn:E3. cbv beta iota in H.
  destruct (Fast.normalize qh ql) as [[qh2 ql2] j2] eqn:E4. cbv beta iota in H.
  apply some_eq in H. destruct H as (Eh & El & Ee). subst h l e.
  assert (Fo : is_finite Fast.one = true) by reflexivity.
  assert (Fz : is_finite zero = true) by reflexivity.
  assert (Z0 : B2R zero = 0) by reflexivity.
  assert (N1 : bpow radix2 (-80) <= 1 <= 4) by (cbn [bpow radix_val radix2]; lra).
  assert (N2 : Rabs 0 <= bpow radix2 (-50) * 1)
    by (rewrite Rabs_R0, Rmult_1_r; apply bpow_ge_0).
  assert (D1 : / 2 <= B2R h2 <= 4) by lra.
  assert (D2 : Rabs (B2R l2) <= bpow radix2 (-52) * B2R h2).
  { apply Rle_trans with (1 := Hl2). apply Rmult_le_compat_r; [lra | apply bpow_le; lia]. }
  pose proof (FastDiv.dd_div_correct fma Fast.one zero h2 l2 Fo Fz Fh2 Fl2) as C.
  rewrite E3, FastRound.one_R, Z0 in C.
  destruct (C N1 N2 D1 D2) as (Fqh & Fql & Rqh & Hq). clear C.
  pose proof (dd_range _ _ Hh2 Hl2) as HS.
  set (S := B2R h2 + B2R l2) in *.
  replace ((1 + 0) / S) with (/ S) in Hq by (unfold Rdiv; ring).
  assert (HQ : / 3 <= / S <= 4 / 3).
  { split; [apply Rinv_le_contravar; lra|].
    apply Rle_trans with (/ (3 / 4)); [apply Rinv_le_contravar; lra | right; field]. }
  set (Q := / S) in *.
  pose proof (quo_range Q (B2R qh + B2R ql) HQ Hq) as HW.
  pose proof (bpow_gt_0 radix2 (-2)) as B2.
  assert (Hqh : bpow radix2 (-2) <= B2R qh).
  { rewrite Rqh. apply rn_ge_bpow; [lia|]. change (bpow radix2 (-2)) with (/ 4). lra. }
  assert (Hqh' : B2R qh < 2).
  { assert (Hn : bpow radix2 (-1022) <= Rabs (B2R qh)).
    { rewrite Rabs_pos_eq by lra.
      apply Rle_trans with (bpow radix2 (-2)); [apply bpow_le; lia | exact Hqh]. }
    pose proof (rn_low _ _ Rqh Hn) as L.
    replace (B2R qh + B2R ql - B2R qh) with (B2R ql) in L by ring.
    rewrite (Rabs_pos_eq (B2R qh)) in L by lra. apply Rabs_le_inv in L.
    assert (B : bpow radix2 (-53) * B2R qh <= / 4 * B2R qh)
      by (apply Rmult_le_compat_r; [lra | cbn [bpow radix_val radix2]; lra]).
    lra. }
  destruct (norm qh ql qh2 ql2 j2 (-2) Fqh Fql Rqh ltac:(lia) (conj Hqh Hqh') E4)
    as (Fqh2 & Fql2 & Hj2 & S2 & Hh3 & Rh3).
  split; [exact Fqh2|]. split; [exact Fql2|]. split; [exact Rh3|]. split; [exact Hh3|].
  split; [change (Z.neg p) with (- Z.pos p)%Z in Hu; lia|].
  rewrite pow_neg_scale by lra. rewrite S2.
  set (D := powerRZ (B2R m) (Z.pos p) * bpow radix2 (- j)) in *.
  assert (PD : 0 < D).
  { apply Rmult_lt_0_compat; [pose proof (bpow_gt_0 radix2 (-8)); lra | apply bpow_gt_0]. }
  assert (PS : 0 < S) by lra.
  assert (HDQ : Rabs (/ D - Q) <= bpow radix2 (-80) * Q).
  { unfold Q.
    assert (PT : 0 <= / D * / S).
    { apply Rlt_le, Rmult_lt_0_compat; apply Rinv_0_lt_compat; assumption. }
    replace (/ D - / S) with ((S - D) * (/ D * / S))
      by (field; split; apply Rgt_not_eq; assumption).
    replace (bpow radix2 (-80) * / S) with (bpow radix2 (-80) * D * (/ D * / S))
      by (field; split; apply Rgt_not_eq; assumption).
    rewrite Rabs_mult, (Rabs_pos_eq (/ D * / S)) by exact PT.
    apply Rmult_le_compat_r; [exact PT|]. rewrite Rabs_minus_sym. exact Herr. }
  pose proof (tri (/ D) Q (B2R qh + B2R ql) ltac:(lra) HDQ Hq) as T.
  replace (/ D * bpow radix2 (- j2) - (B2R qh + B2R ql) * bpow radix2 (- j2))
    with ((/ D - (B2R qh + B2R ql)) * bpow radix2 (- j2)) by ring.
  rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (- j2))) by apply bpow_ge_0.
  apply Rle_trans with (bpow radix2 (-79) * bpow radix2 2).
  + apply Rmult_le_compat; [apply Rabs_pos | apply bpow_ge_0 | exact T | apply bpow_le; lia].
  + rewrite <- bpow_plus. apply bpow_le. lia.
Qed.

(** [pown_small] gives the same result with an FMA as without. *)
Theorem pown_small_fma :
  forall x k g, is_finite x = true -> 0 < B2R x ->
  DyadicPow.pown_small true x k g = DyadicPow.pown_small false x k g.
Proof.
intros x k g Fx Hx. unfold DyadicPow.pown_small. cbv zeta.
destruct ((DyadicPow.small_max <? Z.abs k) || (g <? -1022))%Z eqn:G; [reflexivity|].
apply Bool.orb_false_iff in G. destruct G as [G1 _]. apply Z.ltb_ge in G1.
unfold DyadicPow.small_max in G1.
destruct (mant_bits x Fx Hx) as (Fm & Hm & _).
set (m := from_bits (Z.lor (Z.land (to_bits x) DyadicLog.frac) 0x3fe0000000000000)) in *.
(* The loop, fast_two_sum and normalize: only the loop has an FMA, and for
   [k = 0] it runs no step. *)
assert (EL : DyadicPow.small_loop true (Z.abs k) m (Z.to_nat (DyadicPow.ilog2 (Z.abs k))) m zero =
             DyadicPow.small_loop false (Z.abs k) m (Z.to_nat (DyadicPow.ilog2 (Z.abs k))) m zero).
{ destruct (Z.eq_dec k 0) as [K0|K0].
  - subst k. replace (Z.to_nat (DyadicPow.ilog2 (Z.abs 0))) with O by (vm_compute; reflexivity).
    reflexivity.
  - apply FastPowiLoop.small_loop_fma; [lia | exact Fm | exact Hm]. }
rewrite EL.
destruct (DyadicPow.small_loop false (Z.abs k) m (Z.to_nat (DyadicPow.ilog2 (Z.abs k))) m zero)
  as [h0 l0] eqn:E0.
destruct (Fast.fast_two_sum h0 l0) as [h1 l1] eqn:E1.
destruct (Fast.normalize h1 l1) as [[h2 l2] j] eqn:E2.
destruct (0 <? k)%Z; [reflexivity|].
(* The ranges of the divisor [h2 + l2] of [FastDiv.dd_div_fma], from [pre],
   or from [mid] with [P = m] for [k = 0]. *)
assert (R : is_finite h2 = true /\ is_finite l2 = true /\ 1 <= B2R h2 < 2 /\
            Rabs (B2R l2) <= bpow radix2 (-53) * B2R h2).
{ destruct (Z.eq_dec k 0) as [K0|K0].
  - subst k. replace (Z.to_nat (DyadicPow.ilog2 (Z.abs 0))) with O in E0
      by (vm_compute; reflexivity).
    cbn [DyadicPow.small_loop] in E0. apply pair_equal_spec in E0. destruct E0 as [<- <-].
    assert (Fz : is_finite zero = true) by reflexivity.
    assert (Z0 : B2R zero = 0) by reflexivity.
    assert (Hz : Rabs (B2R zero) <= bpow radix2 (-49) * B2R m).
    { rewrite Z0, Rabs_R0. apply Rmult_le_pos; [apply bpow_ge_0 | lra]. }
    assert (HP : bpow radix2 (-8) <= B2R m <= 1).
    { split; [|lra]. apply Rle_trans with (/ 2); [cbn [bpow radix_val radix2]; lra | lra]. }
    assert (He : Rabs (B2R m - (B2R m + B2R zero)) <= bpow radix2 (-80) * B2R m).
    { replace (B2R m - (B2R m + B2R zero)) with 0 by (rewrite Z0; ring).
      rewrite Rabs_R0. apply Rmult_le_pos; [apply bpow_ge_0 | lra]. }
    destruct (mid m zero (B2R m) h1 l1 h2 l2 j Fm Fz ltac:(lra) Hz HP He E1 E2)
      as (F2 & F3 & _ & H4 & H5 & _).
    auto.
  - destruct (pre false (Z.abs k) m h0 l0 h1 l1 h2 l2 j ltac:(lia) Fm Hm E0 E1 E2)
      as (_ & F2 & F3 & _ & H4 & H5 & _).
    auto. }
destruct R as (Fh2 & Fl2 & Hh2 & Hl2).
assert (Fo : is_finite Fast.one = true) by reflexivity.
assert (Fz : is_finite zero = true) by reflexivity.
assert (N1 : bpow radix2 (-80) <= B2R Fast.one <= 4)
  by (rewrite FastRound.one_R; cbn [bpow radix_val radix2]; lra).
assert (N2 : Rabs (B2R zero) <= bpow radix2 (-50) * B2R Fast.one).
{ change (B2R zero) with 0. rewrite Rabs_R0, FastRound.one_R, Rmult_1_r. apply bpow_ge_0. }
assert (D1 : / 2 <= B2R h2 <= 4) by lra.
assert (D2 : Rabs (B2R l2) <= bpow radix2 (-52) * B2R h2).
{ apply Rle_trans with (1 := Hl2). apply Rmult_le_compat_r; [lra | apply bpow_le; lia]. }
rewrite (FastDiv.dd_div_fma Fast.one zero h2 l2 Fo Fz Fh2 Fl2 N1 N2 D1 D2).
reflexivity.
Qed.

(** ** The roundings *)

Theorem pown_small_dir_correct :
  forall fma x k up v,
  is_finite x = true -> 0 < B2R x -> k <> 0%Z ->
  (-1075 < if 0 <? k then (DyadicPow.expo x + 1) * k else DyadicPow.expo x * k)%Z ->
  DyadicPow.pown_small_dir fma x k (DyadicPow.expo x) up = Some v ->
  rounds up (powerRZ (B2R x) k) v.
Proof.
intros fma x k up v Fx Hx Hk Hu H. unfold DyadicPow.pown_small_dir in H.
destruct (DyadicPow.pown_small fma x k (DyadicPow.expo x)) as [[[h l] e]|] eqn:E;
  [|discriminate H].
destruct (pown_small_correct fma x k h l e Fx Hx Hk Hu E) as (Fh & Fl & Eh & Hh & He & Herr).
rewrite (scale_back (powerRZ (B2R x) k) e).
exact (round_dir_wide_err_correct h l e DyadicExp.err67 67 up v _ Fh Fl Eh ltac:(lra) He
  ltac:(lia) lit_err67 Herr H).
Qed.

Theorem pown_small_near_correct :
  forall fma x k v,
  is_finite x = true -> 0 < B2R x -> k <> 0%Z ->
  (-1075 < if 0 <? k then (DyadicPow.expo x + 1) * k else DyadicPow.expo x * k)%Z ->
  DyadicPow.pown_small_near fma x k (DyadicPow.expo x) = Some v ->
  near_round (powerRZ (B2R x) k) v.
Proof.
intros fma x k v Fx Hx Hk Hu H. unfold DyadicPow.pown_small_near in H.
destruct (DyadicPow.pown_small fma x k (DyadicPow.expo x)) as [[[h l] e]|] eqn:E;
  [|discriminate H].
destruct (pown_small_correct fma x k h l e Fx Hx Hk Hu E) as (Fh & Fl & Eh & Hh & He & Herr).
rewrite (scale_back (powerRZ (B2R x) k) e).
exact (round_near_wide_err_correct h l e DyadicExp.err67 67 v _ Fh Fl Eh ltac:(lra) He
  ltac:(lia) lit_err67 Herr H).
Qed.

Theorem pown_small_dir_fma :
  forall x k g up, is_finite x = true -> 0 < B2R x ->
  DyadicPow.pown_small_dir true x k g up = DyadicPow.pown_small_dir false x k g up.
Proof.
intros x k g up Fx Hx. unfold DyadicPow.pown_small_dir. rewrite (pown_small_fma x k g Fx Hx).
reflexivity.
Qed.

Theorem pown_small_near_fma :
  forall x k g, is_finite x = true -> 0 < B2R x ->
  DyadicPow.pown_small_near true x k g = DyadicPow.pown_small_near false x k g.
Proof.
intros x k g Fx Hx. unfold DyadicPow.pown_small_near. rewrite (pown_small_fma x k g Fx Hx).
reflexivity.
Qed.
