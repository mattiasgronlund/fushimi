(** * The series of [asin(√s) / √s]

    [asin u = u Σ_n a_n u^(2n)], with [a_n = b_n / (2n + 1)] and [b_n =
    Π_{k < n} (2k + 1) / (2k + 2)], the binomial coefficients of [(1 -
    v)^(-1/2) = Σ_n b_n v^n]. [asin_poly N s] is the sum of the first [N]
    terms of [F(s) = asin(√s) / √s = Σ_n a_n s^n], the function that
    [DyadicAtan.ASIN_TABLE] of [Model.v] tabulates ([FastAsinTable.v]).
    [asin_poly_bounds] bounds the remainder [asin u - u asin_poly N (u^2)]
    on [[0, U]] for [U < 1]; [asin_poly_lipschitz] bounds the slope of
    [asin_poly N] on [[0, 1/4 + 1/256]]; and [acos_half] is the half-angle
    formula [acos t = 2 asin √((1 - t) / 2)] that reduces [acos] above 1/2
    to [F] near 0.

    No power series is summed: the remainder bound goes through the mean
    value theorem twice. The truncated binomial series [B_N(v) = Σ_{n < N}
    b_n v^n] satisfies [2 (1 - v) B_N' - B_N = -2 N b_N v^(N-1)]
    ([asin_B_ode]), so [S(v) = 1 - B_N(v) √(1 - v)] has [S' = N b_N
    v^(N-1) / √(1 - v)], which lies in [[0, N b_N v^(N-1) / √(1 - V)]] on
    [[0, V]]. With [S(0) = 0] for [N > 0], that gives [0 <= 1/√(1 - v) -
    B_N(v) = S(v) / √(1 - v) <= b_N v^N / (1 - V)] ([asin_rem]), which is
    the derivative of the remainder of [asin] at [v = u^2]. *)

From Stdlib Require Import Reals Lra Lia.

Open Scope R_scope.

(** [b_n = Π_{k < n} (2k + 1) / (2k + 2)] *)
Fixpoint asin_b (n : nat) : R :=
  match n with
  | O => 1
  | S k => asin_b k * (2 * INR k + 1) / (2 * INR k + 2)
  end.

(** [a_n = b_n / (2n + 1)] *)
Definition asin_a (n : nat) : R := asin_b n / (2 * INR n + 1).

(** [Σ_{n < N} a_n s^n] *)
Fixpoint asin_poly (N : nat) (s : R) : R :=
  match N with
  | O => 0
  | S k => asin_poly k s + asin_a k * s ^ k
  end.

(** The ratio [b_(k+1) / b_k = (2k + 1) / (2k + 2)] lies in [(0, 1)]. *)
Local Lemma asin_ratio : forall k, 0 < (2 * INR k + 1) / (2 * INR k + 2) < 1.
Proof.
intros k. pose proof (pos_INR k) as Hk.
split; [apply Rdiv_lt_0_compat; lra |].
apply (Rmult_lt_reg_r (2 * INR k + 2)); [lra |].
unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

Local Lemma asin_b_S : forall k, asin_b (S k) = asin_b k * ((2 * INR k + 1) / (2 * INR k + 2)).
Proof. intros k. cbn [asin_b]. unfold Rdiv. ring. Qed.

Lemma asin_b_bounds : forall n, 0 < asin_b n <= 1.
Proof.
induction n as [| k IH]; [cbn [asin_b]; lra |].
rewrite asin_b_S. pose proof (asin_ratio k) as Hq.
split; [apply Rmult_lt_0_compat; lra |].
rewrite <- (Rmult_1_r 1). apply Rmult_le_compat; lra.
Qed.

(** ** Monotonicity through the mean value theorem *)

(** If [0 <= f' <= g'] on [[a, b]], then [0 <= f b - f a <= g b - g a]. *)
Local Lemma asin_dominate :
  forall f f' g g' a b, a <= b ->
  (forall c, a <= c <= b -> derivable_pt_lim f c (f' c)) ->
  (forall c, a <= c <= b -> derivable_pt_lim g c (g' c)) ->
  (forall c, a <= c <= b -> 0 <= f' c <= g' c) ->
  0 <= f b - f a <= g b - g a.
Proof.
intros f f' g g' a b Hab Hf Hg Hd.
destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | <-]; [| lra].
destruct (MVT_cor2 f f' a b Hlt Hf) as (c & Hc & Hc0).
destruct (MVT_cor2 (fun r => g r - f r) (fun r => g' r - f' r) a b Hlt) as (e & He & He0).
{ intros e He. apply (derivable_pt_lim_ext (g - f)%F); [intros z; reflexivity |].
  apply derivable_pt_lim_minus; [apply Hg | apply Hf]; exact He. }
pose proof (Hd c ltac:(lra)) as H1. pose proof (Hd e ltac:(lra)) as H2.
assert (P1 : 0 <= f' c * (b - a)) by (apply Rmult_le_pos; lra).
assert (P2 : 0 <= (g' e - f' e) * (b - a)) by (apply Rmult_le_pos; lra).
lra.
Qed.

Local Lemma asin_derive_eq :
  forall f x l l', derivable_pt_lim f x l -> l = l' -> derivable_pt_lim f x l'.
Proof. intros f x l l' H <-. exact H. Qed.

(** [n v v^(n-1) = n v^n], also at [n = 0]. *)
Local Lemma asin_pow_pred : forall n v, INR n * (v * v ^ pred n) = INR n * v ^ n.
Proof. intros [| n] v; simpl; ring. Qed.

(** ** The truncated binomial series of [(1 - v)^(-1/2)] *)

(** [B_N(v) = Σ_{n < N} b_n v^n] *)
Local Fixpoint asin_B (N : nat) (v : R) : R :=
  match N with
  | O => 0
  | S k => asin_B k v + asin_b k * v ^ k
  end.

(** [Σ_{n < N} b_n n v^(n-1)], the derivative of [B_N] *)
Local Fixpoint asin_dB (N : nat) (v : R) : R :=
  match N with
  | O => 0
  | S k => asin_dB k v + asin_b k * (INR k * v ^ pred k)
  end.

Local Lemma asin_B_S : forall k v, asin_B (S k) v = asin_B k v + asin_b k * v ^ k.
Proof. reflexivity. Qed.

Local Lemma asin_dB_S :
  forall k v, asin_dB (S k) v = asin_dB k v + asin_b k * (INR k * v ^ pred k).
Proof. reflexivity. Qed.

Local Lemma asin_B_derive : forall N v, derivable_pt_lim (asin_B N) v (asin_dB N v).
Proof.
intros N; induction N as [| k IH]; intros v.
- apply (derivable_pt_lim_ext (fct_cte 0)); [intros z; reflexivity |].
  apply derivable_pt_lim_const.
- apply (derivable_pt_lim_ext (asin_B k + mult_real_fct (asin_b k) (fun y => y ^ k))%F);
    [intros z; reflexivity |].
  rewrite asin_dB_S. apply derivable_pt_lim_plus; [apply IH |].
  apply derivable_pt_lim_scal. apply derivable_pt_lim_pow.
Qed.

(** Coefficient by coefficient, [2 (n + 1) b_(n+1) = (2n + 1) b_n] cancels
    every term but the last. *)
Local Lemma asin_B_ode :
  forall N v, 2 * (1 - v) * asin_dB N v - asin_B N v = - (2 * INR N * asin_b N * v ^ pred N).
Proof.
intros N; induction N as [| k IH]; intros v; [cbn [asin_dB asin_B INR]; ring |].
rewrite asin_dB_S, asin_B_S, asin_b_S, S_INR. cbn [Nat.pred].
pose proof (IH v) as H. pose proof (asin_pow_pred k v) as E. pose proof (pos_INR k) as Hk.
set (X := v ^ Nat.pred k) in *. set (Y := v ^ k) in *.
set (D := asin_dB k v) in *. set (B := asin_B k v) in *.
set (b := asin_b k) in *. set (n := INR k) in *.
replace (- (2 * (n + 1) * (b * ((2 * n + 1) / (2 * n + 2))) * Y))
  with (- (b * (2 * n + 1) * Y)) by (field; lra).
assert (E' : b * (n * (v * X)) = b * (n * Y)) by (rewrite E; reflexivity).
lra.
Qed.

Local Lemma asin_B_0 : forall k, asin_B (S k) 0 = 1.
Proof.
induction k as [| k IH]; [cbn [asin_B asin_b pow]; ring |].
rewrite asin_B_S, IH, pow_i by lia. ring.
Qed.

(** The algebra of [S' = (B_N - 2 (1 - v) B_N') / (2 √(1 - v))]. *)
Local Lemma asin_S_alg :
  forall s dB B c, 0 < s -> 2 * (s * s) * dB - B = - (2 * c) ->
  0 - (dB * s + B * (/ (2 * s) * (0 - 1))) = c / s.
Proof.
intros s dB B c Hs H.
assert (HB : B = 2 * (s * s) * dB + 2 * c) by lra. subst B.
field. lra.
Qed.

(** [S(v) = 1 - B_N(v) √(1 - v)] has the derivative [N b_N v^(N-1) / √(1 - v)]. *)
Local Lemma asin_S_derive :
  forall N v, v < 1 ->
  derivable_pt_lim (fun w => 1 - asin_B N w * sqrt (1 - w)) v
    (INR N * asin_b N * v ^ pred N / sqrt (1 - v)).
Proof.
intros N v Hv.
assert (Hs : 0 < sqrt (1 - v)) by (apply sqrt_lt_R0; lra).
assert (Hs2 : sqrt (1 - v) * sqrt (1 - v) = 1 - v) by (apply sqrt_sqrt; lra).
assert (Dsq : derivable_pt_lim (fun w => sqrt (1 - w)) v (/ (2 * sqrt (1 - v)) * (0 - 1))).
{ apply (derivable_pt_lim_ext (comp sqrt (fct_cte 1 - id)%F)); [intros z; reflexivity |].
  apply derivable_pt_lim_comp.
  - apply derivable_pt_lim_minus; [apply derivable_pt_lim_const | apply derivable_pt_lim_id].
  - apply derivable_pt_lim_sqrt. unfold minus_fct, fct_cte, id. lra. }
apply (derivable_pt_lim_ext (fct_cte 1 - asin_B N * (fun w => sqrt (1 - w)))%F);
  [intros z; reflexivity |].
eapply asin_derive_eq.
- apply derivable_pt_lim_minus; [apply derivable_pt_lim_const |].
  apply derivable_pt_lim_mult; [apply asin_B_derive | exact Dsq].
- cbv beta. apply asin_S_alg; [exact Hs |].
  rewrite Hs2. pose proof (asin_B_ode N v). lra.
Qed.

(** The remainder of the binomial series: [0 <= 1/√(1 - v) - B_N(v) <= b_N v^N / (1 - V)]. *)
Local Lemma asin_rem :
  forall N v V, 0 <= v <= V -> V < 1 ->
  0 <= / sqrt (1 - v) - asin_B N v <= asin_b N * v ^ N / (1 - V).
Proof.
intros N v V Hv HV.
assert (Hs : 0 < sqrt (1 - v)) by (apply sqrt_lt_R0; lra).
assert (HsV : 0 < sqrt (1 - V)) by (apply sqrt_lt_R0; lra).
assert (HsV2 : sqrt (1 - V) * sqrt (1 - V) = 1 - V) by (apply sqrt_sqrt; lra).
assert (Hle : sqrt (1 - V) <= sqrt (1 - v)) by (apply sqrt_le_1_alt; lra).
assert (Hinv : / sqrt (1 - v) <= / sqrt (1 - V)) by (apply Rinv_le_contravar; lra).
assert (Hi0 : 0 < / sqrt (1 - v)) by (apply Rinv_0_lt_compat; lra).
destruct N as [| k].
- (* [B_0 = 0]: [1/√(1 - v) <= 1/√(1 - V) <= 1/(1 - V)] as [1 - V <= √(1 - V) <= 1]. *)
  cbn [asin_B asin_b pow].
  assert (HsV1 : sqrt (1 - V) <= sqrt 1) by (apply sqrt_le_1_alt; lra).
  rewrite sqrt_1 in HsV1.
  assert (H1 : sqrt (1 - V) * sqrt (1 - V) <= sqrt (1 - V) * 1)
    by (apply Rmult_le_compat_l; lra).
  assert (H2 : / sqrt (1 - V) <= / (1 - V)) by (apply Rinv_le_contravar; lra).
  unfold Rdiv. lra.
- set (b := asin_b (S k)).
  set (K := b / sqrt (1 - V)).
  pose proof (asin_b_bounds (S k)) as Hb. fold b in Hb.
  assert (HK : 0 < K) by (apply Rdiv_lt_0_compat; lra).
  pose proof (asin_dominate (fun w => 1 - asin_B (S k) w * sqrt (1 - w))
    (fun w => INR (S k) * b * w ^ pred (S k) / sqrt (1 - w))
    (fun w => K * w ^ S k) (fun w => K * (INR (S k) * w ^ pred (S k))) 0 v
    (proj1 Hv)) as H.
  cbv beta in H.
  rewrite Rminus_0_r, sqrt_1, asin_B_0, pow_i in H by lia.
  replace (/ sqrt (1 - v) - asin_B (S k) v)
    with ((1 - asin_B (S k) v * sqrt (1 - v)) * / sqrt (1 - v)) by (field; lra).
  destruct H as [H0 H1].
  + intros c Hc. apply asin_S_derive. lra.
  + intros c Hc.
    apply (derivable_pt_lim_ext (mult_real_fct K (fun w => w ^ S k)));
      [intros z; reflexivity |].
    apply derivable_pt_lim_scal, derivable_pt_lim_pow.
  + intros c Hc.
    assert (Hc0 : 0 <= INR (S k) * b * c ^ pred (S k)).
    { apply Rmult_le_pos; [apply Rmult_le_pos; [apply pos_INR | lra] | apply pow_le; lra]. }
    assert (Hsc : sqrt (1 - V) <= sqrt (1 - c)) by (apply sqrt_le_1_alt; lra).
    assert (Hic : / sqrt (1 - c) <= / sqrt (1 - V)) by (apply Rinv_le_contravar; lra).
    assert (Hic0 : 0 < / sqrt (1 - c)) by (apply Rinv_0_lt_compat, sqrt_lt_R0; lra).
    replace (K * (INR (S k) * c ^ pred (S k)))
      with (INR (S k) * b * c ^ pred (S k) * / sqrt (1 - V)) by (unfold K; field; lra).
    unfold Rdiv. split; [apply Rmult_le_pos; lra |].
    apply Rmult_le_compat_l; lra.
  + split; [apply Rmult_le_pos; lra |].
    (* [S(v) / √(1 - v) <= K v^N / √(1 - V) = b v^N / (1 - V)] *)
    apply Rle_trans with (K * v ^ S k * / sqrt (1 - V)).
    * apply Rmult_le_compat; lra.
    * right. unfold K.
      transitivity (b * v ^ S k / (sqrt (1 - V) * sqrt (1 - V))); [field; lra |].
      rewrite HsV2. reflexivity.
Qed.

(** ** The remainder of [asin] *)

(** The derivative of [r ↦ r asin_poly N (r^2)] is [B_N(r^2)], as
    [(2n + 1) a_n = b_n]. *)
Local Lemma asin_odd_derive :
  forall N w, derivable_pt_lim (fun r => r * asin_poly N (r ^ 2)) w (asin_B N (w ^ 2)).
Proof.
intros N; induction N as [| k IH]; intros w.
- apply (derivable_pt_lim_ext (fct_cte 0));
    [intros z; cbn [asin_poly]; unfold fct_cte; ring |].
  apply derivable_pt_lim_const.
- apply (derivable_pt_lim_ext
           ((fun r => (r * asin_poly k (r ^ 2))%R) +
            mult_real_fct (asin_a k) (fun r => r ^ (2 * k + 1)))%F).
  { intros z. unfold plus_fct, mult_real_fct. cbn [asin_poly].
    rewrite <- pow_mult, pow_add. ring. }
  eapply asin_derive_eq.
  + apply derivable_pt_lim_plus; [apply IH |].
    apply derivable_pt_lim_scal, derivable_pt_lim_pow.
  + rewrite asin_B_S. replace (Nat.pred (2 * k + 1)) with (2 * k)%nat by lia.
    rewrite pow_mult.
    replace (INR (2 * k + 1)) with (2 * INR k + 1) by (rewrite plus_INR, mult_INR; simpl; ring).
    unfold asin_a. pose proof (pos_INR k). field. lra.
Qed.

Local Lemma asin_derive_lim : forall x, -1 < x < 1 -> derivable_pt_lim asin x (/ sqrt (1 - x ^ 2)).
Proof.
intros x Hx. apply (derive_pt_eq_1 _ _ _ (derivable_pt_asin x Hx)).
rewrite derive_pt_asin. unfold Rsqr. replace (x ^ 2) with (x * x) by ring.
unfold Rdiv. ring.
Qed.

(** The remainder after [N] terms, at [0 <= u <= U < 1]: the terms are
    positive, and the remainder is at most the next term over [1 - U^2]. *)
Theorem asin_poly_bounds :
  forall N u U, 0 <= u <= U -> U < 1 ->
  0 <= asin u - u * asin_poly N (u ^ 2) <=
    asin_b N * u ^ (2 * N + 1) / ((2 * INR N + 1) * (1 - U ^ 2)).
Proof.
intros N u U Hu HU.
assert (HU2 : U ^ 2 < 1) by nra.
pose proof (pos_INR N) as HN.
pose proof (asin_b_bounds N) as Hb.
set (K := asin_b N / ((2 * INR N + 1) * (1 - U ^ 2))).
pose proof (asin_dominate (fun r => asin r - r * asin_poly N (r ^ 2))
  (fun r => / sqrt (1 - r ^ 2) - asin_B N (r ^ 2))
  (fun r => K * r ^ (2 * N + 1)) (fun r => K * (INR (2 * N + 1) * r ^ pred (2 * N + 1)))
  0 u (proj1 Hu)) as H.
cbv beta in H.
rewrite asin_0, !pow_i in H by lia.
replace (asin_b N * u ^ (2 * N + 1) / ((2 * INR N + 1) * (1 - U ^ 2)))
  with (K * u ^ (2 * N + 1)) by (unfold K; field; lra).
destruct H as [H0 H1].
- intros c Hc.
  apply (derivable_pt_lim_ext (asin - (fun r => (r * asin_poly N (r ^ 2))%R))%F);
    [intros z; reflexivity |].
  apply derivable_pt_lim_minus; [| apply asin_odd_derive].
  apply asin_derive_lim. lra.
- intros c Hc.
  apply (derivable_pt_lim_ext (mult_real_fct K (fun w => w ^ (2 * N + 1))));
    [intros z; reflexivity |].
  apply derivable_pt_lim_scal, derivable_pt_lim_pow.
- intros c Hc.
  assert (Hc2 : 0 <= c ^ 2 <= U ^ 2) by (split; [apply pow_le | apply pow_incr]; lra).
  pose proof (asin_rem N (c ^ 2) (U ^ 2) Hc2 HU2) as R.
  replace (K * (INR (2 * N + 1) * c ^ pred (2 * N + 1)))
    with (asin_b N * (c ^ 2) ^ N / (1 - U ^ 2)).
  + exact R.
  + replace (Nat.pred (2 * N + 1)) with (2 * N)%nat by lia.
    rewrite pow_mult.
    replace (INR (2 * N + 1)) with (2 * INR N + 1) by (rewrite plus_INR, mult_INR; simpl; ring).
    unfold K. field. lra.
- split; lra.
Qed.

(** ** The slope of [asin_poly N] *)

(** [|a^n - b^n| <= n M^(n-1) |a - b|] on [[0, M]] *)
Local Lemma asin_pow_diff :
  forall n a b M, 0 <= a <= M -> 0 <= b <= M ->
  Rabs (a ^ n - b ^ n) <= INR n * M ^ pred n * Rabs (a - b).
Proof.
intros n; induction n as [| n IH]; intros a b M Ha Hb.
- replace (a ^ 0 - b ^ 0) with 0 by (simpl; ring). rewrite Rabs_R0. simpl. lra.
- replace (a ^ S n - b ^ S n) with (a * (a ^ n - b ^ n) + b ^ n * (a - b)) by (simpl; ring).
  eapply Rle_trans; [apply Rabs_triang |].
  rewrite !Rabs_mult, (Rabs_pos_eq a), (Rabs_pos_eq (b ^ n)) by (try apply pow_le; lra).
  pose proof (IH a b M Ha Hb) as H.
  assert (Hbn : b ^ n <= M ^ n) by (apply pow_incr; lra).
  assert (H1 : a * Rabs (a ^ n - b ^ n) <= M * (INR n * M ^ pred n * Rabs (a - b)))
    by (apply Rmult_le_compat; [lra | apply Rabs_pos | lra | exact H]).
  assert (H2 : b ^ n * Rabs (a - b) <= M ^ n * Rabs (a - b))
    by (apply Rmult_le_compat_r; [apply Rabs_pos | exact Hbn]).
  assert (H3 : M * (INR n * M ^ pred n * Rabs (a - b)) = INR n * M ^ n * Rabs (a - b)).
  { replace (M * (INR n * M ^ pred n * Rabs (a - b)))
      with (INR n * (M * M ^ pred n) * Rabs (a - b)) by ring.
    rewrite asin_pow_pred. reflexivity. }
  rewrite S_INR. cbn [Nat.pred]. lra.
Qed.

(** [Σ_{n < N} n a_n M^(n-1)], the slope bound of [asin_poly N] on [[0, M]] *)
Local Fixpoint asin_lip (N : nat) (M : R) : R :=
  match N with
  | O => 0
  | S k => asin_lip k M + asin_a k * (INR k * M ^ pred k)
  end.

Local Lemma asin_a_pos : forall n, 0 < asin_a n.
Proof.
intros n. unfold asin_a. pose proof (asin_b_bounds n). pose proof (pos_INR n).
apply Rdiv_lt_0_compat; lra.
Qed.

Local Lemma asin_poly_diff :
  forall N a b M, 0 <= a <= M -> 0 <= b <= M ->
  Rabs (asin_poly N a - asin_poly N b) <= asin_lip N M * Rabs (a - b).
Proof.
intros N; induction N as [| k IH]; intros a b M Ha Hb.
- cbn [asin_poly asin_lip]. rewrite Rminus_0_r, Rabs_R0. lra.
- cbn [asin_poly asin_lip].
  replace (asin_poly k a + asin_a k * a ^ k - (asin_poly k b + asin_a k * b ^ k))
    with ((asin_poly k a - asin_poly k b) + asin_a k * (a ^ k - b ^ k)) by ring.
  eapply Rle_trans; [apply Rabs_triang |].
  pose proof (asin_a_pos k) as Hak.
  rewrite Rabs_mult, (Rabs_pos_eq (asin_a k)) by lra.
  pose proof (IH a b M Ha Hb) as H1.
  pose proof (asin_pow_diff k a b M Ha Hb) as H2.
  assert (H3 : asin_a k * Rabs (a ^ k - b ^ k) <=
               asin_a k * (INR k * M ^ pred k * Rabs (a - b)))
    by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

(** [b_n <= b_2 = 3/8] for [n >= 2] *)
Local Lemma asin_b_le : forall n, asin_b (S (S n)) <= 3 / 8.
Proof.
induction n as [| n IH].
- rewrite !asin_b_S. cbn [asin_b INR]. lra.
- rewrite asin_b_S. pose proof (asin_ratio (S (S n))) as Hq.
  pose proof (asin_b_bounds (S (S n))) as Hb.
  assert (asin_b (S (S n)) * ((2 * INR (S (S n)) + 1) / (2 * INR (S (S n)) + 2)) <=
          asin_b (S (S n))) by (rewrite <- (Rmult_1_r (asin_b (S (S n)))) at 2;
                                apply Rmult_le_compat_l; lra).
  lra.
Qed.

(** [n a_n = n b_n / (2n + 1) <= b_n / 2 <= 3/16] for [n >= 2] *)
Local Lemma asin_na_le : forall n, INR (S (S n)) * asin_a (S (S n)) <= 3 / 16.
Proof.
intros n. unfold asin_a.
pose proof (asin_b_le n) as Hb. pose proof (asin_b_bounds (S (S n))) as Hb0.
pose proof (pos_INR (S (S n))) as Hm.
set (m := INR (S (S n))) in *. set (b := asin_b (S (S n))) in *.
apply (Rmult_le_reg_r (2 * m + 1)); [lra |].
replace (m * (b / (2 * m + 1)) * (2 * m + 1)) with (m * b) by (field; lra).
assert (m * b <= m * (3 / 8)) by (apply Rmult_le_compat_l; lra).
lra.
Qed.

(** With [M = 1/4 + 1/256] and [K = (3/16) / (1 - M) = 48/191], the
    geometric tail [Σ_{2 <= n < N} (3/16) M^(n-1)] is [K M - K M^(N-1)]:
    [Σ_{n < N} n a_n M^(n-1) <= a_1 + K M - K M^(N-1)] for [N >= 2], with
    [a_1 = 1/6]. *)
Local Lemma asin_lip_tail :
  forall k, asin_lip (S (S k)) (/ 4 + / 256) + 48 / 191 * (/ 4 + / 256) ^ S k <=
            / 6 + 48 / 191 * (/ 4 + / 256).
Proof.
induction k as [| k IH].
- cbn [asin_lip]. unfold asin_a. cbn [asin_b INR Nat.pred pow]. lra.
- change (asin_lip (S (S (S k))) (/ 4 + / 256)) with
    (asin_lip (S (S k)) (/ 4 + / 256) +
     asin_a (S (S k)) * (INR (S (S k)) * (/ 4 + / 256) ^ Nat.pred (S (S k)))).
  cbn [Nat.pred].
  set (X := (/ 4 + / 256) ^ S k) in *.
  assert (HX : 0 <= X) by (apply pow_le; lra).
  pose proof (asin_na_le k) as Hn.
  assert (H1 : INR (S (S k)) * asin_a (S (S k)) * X <= 3 / 16 * X)
    by (apply Rmult_le_compat_r; lra).
  change ((/ 4 + / 256) ^ S (S k)) with ((/ 4 + / 256) * X).
  lra.
Qed.

Local Lemma asin_lip_bound : forall N, asin_lip N (/ 4 + / 256) <= / 4.
Proof.
intros [| [| k]].
- cbn [asin_lip]. lra.
- cbn [asin_lip INR]. lra.
- pose proof (asin_lip_tail k) as H.
  assert (0 <= (/ 4 + / 256) ^ S k) by (apply pow_le; lra).
  lra.
Qed.

Lemma asin_poly_lipschitz :
  forall N a b, 0 <= a <= / 4 + / 256 -> 0 <= b <= / 4 + / 256 ->
  Rabs (asin_poly N a - asin_poly N b) <= / 4 * Rabs (a - b).
Proof.
intros N a b Ha Hb.
eapply Rle_trans; [apply (asin_poly_diff N a b (/ 4 + / 256) Ha Hb) |].
apply Rmult_le_compat_r; [apply Rabs_pos | apply asin_lip_bound].
Qed.

(** ** The half-angle formula *)

(** With [θ = acos t] in [[0, π]], [sin(θ/2) >= 0] and [sin(θ/2)^2 = (1 -
    cos θ) / 2 = (1 - t) / 2], so [θ/2 = asin √((1 - t) / 2)]. *)
Lemma acos_half : forall t, 0 <= t <= 1 -> acos t = 2 * asin (sqrt ((1 - t) / 2)).
Proof.
intros t Ht.
pose proof (acos_bound t) as Hb. pose proof PI_RGT_0 as HPI.
assert (Hc : cos (acos t) = t) by (apply cos_acos; lra).
set (th := acos t) in *.
assert (Hsin : sin (th / 2) = sqrt ((1 - t) / 2)).
{ assert (Hs0 : 0 <= sin (th / 2)) by (apply sin_ge_0; lra).
  rewrite <- Hc.
  replace (cos th) with (cos (2 * (th / 2))) by (f_equal; field).
  rewrite cos_2a_sin.
  replace ((1 - (1 - 2 * sin (th / 2) * sin (th / 2))) / 2) with (Rsqr (sin (th / 2)))
    by (unfold Rsqr; field).
  rewrite sqrt_Rsqr by exact Hs0. reflexivity. }
rewrite <- Hsin, asin_sin by lra. field.
Qed.
