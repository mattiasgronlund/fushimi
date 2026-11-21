(** * The tail of stage 0 of [asin] and [acos]

    [DyadicAtan.fast_asin_poly] of [Model.v] reduces [t] to an index [j]
    and an offset [tau], then evaluates row [j] of
    [DyadicAtan.ASIN_TABLE] at [tau] and multiplies by [zh + zl]: [t] for
    [t <= 1/2], and [√u] in double-double above ([FastAsinPoly.v] has the
    whole reduction). That last part is [tail] here. [tail_correct]
    bounds it relatively to [zh], and [tail_fma] shows it is the same
    with and without an FMA. The helpers that [FastAsinPolyRed.v],
    [FastAsinPolyB.v] and [FastAsinPoly.v] share are here too: the index
    ([idx], [sub_idx]), the exact product ([prod_exact]) and the rest of
    the series ([asin_ge], [series_rest]). *)


From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error Sterbenz.
From Fushimi Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct DyDriver NearF64
  FastDdSqrt.
From Stdlib Require Import QArith Qreals.
From Fushimi Require FastExpErr FastExpReduce FastAtanCore ConstTight FastRound.
From Fushimi Require Import AsinSeries FastAsinTable FastAsinPolyGappa.

Open Scope R_scope.

(** ** Helpers *)

(** [lit w H] adds [H : B2R w = n * / d] for the literal [w], as in
    [FastAtanCore.v]. *)
Local Ltac lit w H :=
  let q := eval vm_compute in (ConstTight.B2Q w) in
  assert (H : B2R w = Q2R q)
    by (rewrite ConstTight.B2Q_correct; f_equal; vm_compute; reflexivity);
  unfold Q2R in H; cbn [Qnum Qden] in H.

(** [Model.le x y] tests [x <= y]. *)
Lemma le_iff :
  forall x y, is_finite x = true -> is_finite y = true ->
  (Model.le x y = true <-> B2R x <= B2R y).
Proof.
intros x y Fx Fy. unfold Model.le. rewrite Bleb_correct by assumption.
destruct (Rle_bool_spec (B2R x) (B2R y)); split; intros; easy || lra.
Qed.

(** ** The reduction *)

(** [tail fma zh zl j tau] is the part of [fast_asin_poly] after the
    reduction: row [j] of the table at [tau], times [zh + zl]. *)
Definition tail (fma : bool) (zh zl : f64) (j : Z) (tau : f64) : f64 * f64 :=
  let c0h := DyadicAtan.asin_coef j 0 in
  let c0l := DyadicAtan.asin_coef j 1 in
  let c1 := DyadicAtan.asin_coef j 2 in
  let c2 := DyadicAtan.asin_coef j 3 in
  let c3 := DyadicAtan.asin_coef j 4 in
  let c4 := DyadicAtan.asin_coef j 5 in
  let c5 := DyadicAtan.asin_coef j 6 in
  let c6 := DyadicAtan.asin_coef j 7 in
  let q :=
    add c1 (mul tau (add c2 (mul tau (add c3 (mul tau (add c4 (mul tau (add c5 (mul tau c6))))))))) in
  let fl := add c0l (mul tau q) in
  let rh := mul zh c0h in
  let rl := add (Generic.two_prod_err fma zh c0h rh) (add (mul zh fl) (mul zl c0h)) in
  Fast.fast_two_sum rh rl.

(** [fast_asin_poly] for [t <= 1/2] ([zh = t], [zl = 0], [s = p = t^2]). *)
Lemma poly_tail_A :
  forall fma t, Model.le t DyadicLog.half = true ->
  DyadicAtan.fast_asin_poly fma t =
  let p := mul t t in
  let ks := add (mul p (from_bits 0x4070000000000000)) DyadicExp.shifter in
  let jd := sub ks DyadicExp.shifter in
  tail fma t zero (DyadicExp.low_i32 (to_bits ks))
    (add (sub p (mul jd (from_bits 0x3f70000000000000))) (Generic.two_prod_err fma t t p)).
Proof.
intros fma t L. unfold DyadicAtan.fast_asin_poly. rewrite L. reflexivity.
Qed.

(** [fast_asin_poly] for [t > 1/2] ([zh + zl = √u], [s = u/4]). *)
Lemma poly_tail_B :
  forall fma t zh zl, Model.le t DyadicLog.half = false ->
  Fast.dd_sqrt fma (sub DyadicExp.two (mul DyadicExp.two t)) zero = (zh, zl) ->
  DyadicAtan.fast_asin_poly fma t =
  let u := sub DyadicExp.two (mul DyadicExp.two t) in
  let ks := add (mul u (from_bits 0x4050000000000000)) DyadicExp.shifter in
  let jd := sub ks DyadicExp.shifter in
  tail fma zh zl (DyadicExp.low_i32 (to_bits ks))
    (sub (mul DyadicAtan.quarter u) (mul jd (from_bits 0x3f70000000000000))).
Proof.
intros fma t zh zl L E. unfold DyadicAtan.fast_asin_poly. rewrite L. cbv zeta. rewrite E.
reflexivity.
Qed.

(** The float [ks - SHIFTER] is the integer [j] nearest [2^k x] for [0 <=
    2^k x <= 64] ([k = 8] for [p], [6] for [u]), [ks.to_bits() as i32 as
    usize] is [j] ([FastExpReduce.shifter_bits]), and [jd 2^-8 = j / 256]
    exactly, as in [FastAtanCore.core_kf] and [FastAtanCore.core_index].
    There is no tie to exclude, as [2^k x <= 64]. *)
Lemma idx :
  forall x W k, is_finite x = true -> is_finite W = true -> B2R W = bpow radix2 k ->
  (0 <= k)%Z -> 0 <= B2R x * bpow radix2 k <= 64 ->
  let ks := add (mul x W) DyadicExp.shifter in
  exists j, (0 <= j <= 64)%Z /\ Rabs (B2R x * bpow radix2 k - IZR j) <= / 2 /\
    DyadicExp.low_i32 (to_bits ks) = j /\
    is_finite (mul (sub ks DyadicExp.shifter) (from_bits 0x3f70000000000000)) = true /\
    B2R (mul (sub ks DyadicExp.shifter) (from_bits 0x3f70000000000000)) = IZR j / 256.
Proof.
intros x W k Fx FW HW Hk Hx. cbv zeta.
assert (FS : is_finite DyadicExp.shifter = true) by reflexivity.
lit DyadicExp.shifter HS.
set (S := DyadicExp.shifter) in *.
assert (B : bpow radix2 52 = 4503599627370496 /\ bpow radix2 53 = 9007199254740992)
  by (split; reflexivity).
destruct B as (B52 & B53).
(* [2^k x] is exact. *)
destruct (mul_below_max x W Fx FW) as (FM & HM & _).
{ apply FastExpReduce.le_MAX. rewrite HW, Rabs_pos_eq by lra. lra. }
assert (EM : B2R (mul x W) = B2R x * bpow radix2 k).
{ rewrite HM, HW. apply round_generic; [typeclasses eauto|].
  apply mult_bpow_pos_exact_FLT; [apply generic_format_B2R | exact Hk]. }
set (M := mul x W) in *.
(* [2^k x + SHIFTER] is in [[2^52, 2^53)], so it rounds to an integer [m]. *)
destruct (add_below_max M S FM FS) as (FU & HU & _).
{ apply FastExpReduce.le_MAX, Rabs_le. rewrite EM, HS. lra. }
set (U := add M S) in *.
assert (Hv : bpow radix2 52 <= B2R M + B2R S < bpow radix2 53)
  by (rewrite EM, HS, B52, B53; lra).
rewrite (FastExpReduce.RN_int _ Hv) in HU.
pose proof (Znearest_half (fun x => negb (Z.even x)) (B2R M + B2R S)) as Hm.
set (m := Znearest (fun x => negb (Z.even x)) (B2R M + B2R S)) in *.
apply Rabs_le_inv in Hm.
set (n := (m - 6755399441055744)%Z).
assert (Hn : IZR n = B2R U - B2R S) by (unfold n; rewrite minus_IZR, HU, HS; lra).
assert (Hnr : Rabs (B2R x * bpow radix2 k - IZR n) <= / 2)
  by (apply Rabs_le; rewrite Hn, HU, <- EM; lra).
assert (Hn0 : (0 <= n)%Z).
{ assert (-1 < n)%Z; [|lia]. apply lt_IZR. apply Rabs_le_inv in Hnr. lra. }
assert (Hn64 : (n <= 64)%Z).
{ assert (n < 65)%Z; [|lia]. apply lt_IZR. apply Rabs_le_inv in Hnr. lra. }
(* [jd] is [n] exactly. *)
destruct (sub_below_max U S FU FS) as (Fkf & Hkf & _).
{ apply FastExpReduce.le_MAX, Rabs_le. rewrite <- Hn.
  assert (0 <= IZR n <= 64) by (split; apply IZR_le; lia). lra. }
assert (Ekf : B2R (sub U S) = IZR n).
{ rewrite Hkf, <- Hn. apply round_generic; [typeclasses eauto|].
  apply FastExpReduce.format_int. lia. }
exists n.
split; [lia|]. split; [exact Hnr|].
split; [apply (FastExpReduce.shifter_bits _ _ Fkf Ekf); lia|].
(* [jd 2^-8 = n / 256] exactly. *)
assert (F8 : is_finite (from_bits 0x3f70000000000000) = true) by reflexivity.
lit (from_bits 0x3f70000000000000) H8.
assert (B8 : bpow radix2 (-8) = / 256) by reflexivity.
assert (H8' : B2R (from_bits 0x3f70000000000000) = bpow radix2 (-8)) by (rewrite H8, B8; lra).
assert (Hnb : 0 <= IZR n <= 64) by (split; apply IZR_le; lia).
destruct (FastExpErr.mul_e (sub U S) (from_bits 0x3f70000000000000) Fkf F8) as (Fc & Hc & _).
{ rewrite Ekf, H8'. apply Rabs_le. rewrite B8. lra. }
split; [exact Fc|].
assert (G : generic_format radix2 fexp64 (IZR n * bpow radix2 (-8))).
{ apply FastExpReduce.format_mult; [|lia].
  apply Z.abs_lt; split; [lia|]. apply Z.le_lt_trans with 64%Z; [lia | reflexivity]. }
rewrite Hc, Ekf, H8', round_generic by first [exact G | typeclasses eauto]. rewrite B8. lra.
Qed.

(** [s - j/256] is exact for the [j] nearest [256 s]: by Sterbenz's lemma
    for [j >= 1], and as [s - 0] for [j = 0]. *)
Lemma sub_idx :
  forall s y j, is_finite s = true -> is_finite y = true -> 0 <= B2R s <= 1 ->
  (0 <= j)%Z -> B2R y = IZR j / 256 -> Rabs (B2R s * 256 - IZR j) <= / 2 ->
  is_finite (sub s y) = true /\ B2R (sub s y) = B2R s - IZR j / 256.
Proof.
intros s y j Fs Fy Hs Hj Hy Hr.
apply Rabs_le_inv in Hr.
destruct (sub_below_max s y Fs Fy) as (Fd & Ed & _).
{ apply FastExpReduce.le_MAX, Rabs_le. rewrite Hy. lra. }
split; [exact Fd|]. rewrite Ed, Hy. apply round_generic; [typeclasses eauto|].
destruct (Z.eq_dec j 0) as [->|Hj1].
- replace (B2R s - 0 / 256) with (B2R s) by lra. apply generic_format_B2R.
- assert (H1 : 1 <= IZR j) by (apply IZR_le; lia).
  rewrite <- Hy. apply sterbenz; try typeclasses eauto; try apply generic_format_B2R.
  rewrite Hy. lra.
Qed.

(** ** The tail *)

(** Bounds on products, for [lra]. *)
Lemma scale_le :
  forall z x k, 0 <= z -> Rabs x <= k -> - (k * z) <= z * x <= k * z.
Proof.
intros z x k Hz Hx. apply Rabs_le_inv. rewrite Rabs_mult, (Rabs_pos_eq z Hz).
rewrite (Rmult_comm k z). apply Rmult_le_compat_l; assumption.
Qed.

Lemma prod_le :
  forall x y a b, Rabs x <= a -> Rabs y <= b -> - (a * b) <= x * y <= a * b.
Proof.
intros x y a b Hx Hy. apply Rabs_le_inv. rewrite Rabs_mult.
apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hx | exact Hy].
Qed.

(** A rounding error [c |w| + t] with [|w| <= k]. *)
Local Lemma err_le :
  forall x y w c k t, 0 <= c -> Rabs (x - y) <= c * Rabs w + t -> Rabs w <= k ->
  - (c * k + t) <= x - y <= c * k + t.
Proof.
intros x y w c k t Hc H Hw. apply Rabs_le_inv.
apply Rle_trans with (1 := H). apply Rplus_le_compat_r, Rmult_le_compat_l; assumption.
Qed.

(** [x y] is exact as a pair for [2^-60 <= |x y| <= 4] and [|x|, |y| <=
    2] ([FastAtanCore.two_prod_is_exact_of]). *)
Lemma prod_exact :
  forall fma x y, is_finite x = true -> is_finite y = true ->
  bpow radix2 (-60) <= Rabs (B2R x * B2R y) <= 4 -> Rabs (B2R x) <= 2 -> Rabs (B2R y) <= 2 ->
  Generic.two_prod_is_exact fma x y (mul x y) = true.
Proof.
intros fma x y Fx Fy Hp Hx Hy.
destruct (FastExpErr.mul_e x y Fx Fy ltac:(lra)) as (Fp & Ep & _).
assert (Hl : bpow radix2 (-60) <= Rabs (B2R (mul x y))).
{ rewrite Ep. apply abs_round_ge_generic; [typeclasses eauto .. | | lra].
  apply generic_format_bpow. unfold FLT_exp. lia. }
assert (Hu : Rabs (B2R (mul x y)) <= 4).
{ rewrite Ep. change 4 with (bpow radix2 2).
  apply abs_round_le_generic; [typeclasses eauto .. | | change (bpow radix2 2) with 4; lra].
  apply generic_format_bpow. unfold FLT_exp. lia. }
apply FastAtanCore.two_prod_is_exact_of.
- split.
  + apply FastAtanCore.exponent_ge; [exact Fp|].
    apply Rle_trans with (2 := Hl). apply bpow_le. lia.
  + cut (Generic.exponent (mul x y) < 3)%Z; [lia|].
    apply FastAtanCore.exponent_lt; [exact Fp | lia |]. change (bpow radix2 3) with 8. lra.
- cut (Generic.exponent x < 2)%Z; [lia|].
  apply FastAtanCore.exponent_lt; [exact Fx | lia |]. change (bpow radix2 2) with 4. lra.
- cut (Generic.exponent y < 2)%Z; [lia|].
  apply FastAtanCore.exponent_lt; [exact Fy | lia |]. change (bpow radix2 2) with 4. lra.
Qed.

(** The tail is [(zh + zl) P] for [P = asin_poly 34 (j/256 + tau)], within
    [25/4 2^-64 zh], and within [9/2 2^-64 zh] for [zl = 0], units [u =
    2^-64]: [asin_table_close] (11/16 u, times [zh + zl]), [asin_fl_gappa]
    for [fl] (7/4 u), the roundings of [zh fl], [zl c0h], their sum and
    [rl] (each about 7/8 u, as [|fl| <= 7/8 2^-11]), and the dropped [zl
    fl] (7/8 u). [rh + rl] is exact as [zh c0h] is exact as a pair
    ([prod_exact]), and so is [fast_two_sum], as [|rl| <= |rh|]. For [zl =
    0], [zl c0h] and its sum are exact and [zl fl] is 0. *)
Lemma tail_correct :
  forall fma zh zl j tau ch cl,
  is_finite zh = true -> is_finite zl = true -> is_finite tau = true ->
  bpow radix2 (-28) <= B2R zh <= 2 -> Rabs (B2R zl) <= bpow radix2 (-53) * B2R zh ->
  Rabs (B2R tau) <= / 512 + bpow radix2 (-55) -> (0 <= j <= 64)%Z ->
  tail fma zh zl j tau = (ch, cl) ->
  let P := asin_poly 34 (IZR j / 256 + B2R tau) in
  is_finite ch = true /\ is_finite cl = true /\ B2R ch = RN (B2R ch + B2R cl) /\
  Rabs P <= 2 /\
  Rabs (B2R ch + B2R cl - (B2R zh + B2R zl) * P) <= 25 / 4 * bpow radix2 (-64) * B2R zh /\
  (B2R zl = 0 -> Rabs (B2R ch + B2R cl - B2R zh * P) <= 9 / 2 * bpow radix2 (-64) * B2R zh).
Proof.
intros fma zh zl j tau ch cl Fzh Fzl Ftau Hzh Hzl Htau Hj E. cbv zeta.
destruct (asin_coef_facts j Hj) as (Fc & Hc0 & Hc1 & Hc2 & Hc3).
pose proof (asin_table_close j (B2R tau) Hj Htau) as HT.
unfold asin_table_poly in HT. cbv zeta in HT. rewrite Rplus_assoc in HT.
pose proof (Fc 0%nat ltac:(lia)) as Fc0. pose proof (Fc 1%nat ltac:(lia)) as Fc1.
pose proof (Fc 2%nat ltac:(lia)) as Fc2. pose proof (Fc 3%nat ltac:(lia)) as Fc3.
pose proof (Fc 4%nat ltac:(lia)) as Fc4. pose proof (Fc 5%nat ltac:(lia)) as Fc5.
pose proof (Fc 6%nat ltac:(lia)) as Fc6. pose proof (Fc 7%nat ltac:(lia)) as Fc7.
pose proof (Hc3 3%nat ltac:(lia)) as Hc3'. pose proof (Hc3 4%nat ltac:(lia)) as Hc4.
pose proof (Hc3 5%nat ltac:(lia)) as Hc5. pose proof (Hc3 6%nat ltac:(lia)) as Hc6.
pose proof (Hc3 7%nat ltac:(lia)) as Hc7.
clear Fc Hc3.
unfold tail in E. cbv zeta in E.
set (c0h := DyadicAtan.asin_coef j 0) in *.
set (c0l := DyadicAtan.asin_coef j 1) in *.
set (c1 := DyadicAtan.asin_coef j 2) in *.
set (c2 := DyadicAtan.asin_coef j 3) in *.
set (c3 := DyadicAtan.asin_coef j 4) in *.
set (c4 := DyadicAtan.asin_coef j 5) in *.
set (c5 := DyadicAtan.asin_coef j 6) in *.
set (c6 := DyadicAtan.asin_coef j 7) in *.
pose proof (asin_fl_gappa tau c0l c1 c2 c3 c4 c5 c6 Ftau Fc1 Fc2 Fc3 Fc4 Fc5 Fc6 Fc7
  Htau Hc1 Hc2 Hc3' Hc4 Hc5 Hc6 Hc7) as G.
cbv zeta in G. destruct G as (Ffl & Hfl & Gfl).
set (q := add c1 (mul tau (add c2 (mul tau (add c3 (mul tau (add c4 (mul tau
  (add c5 (mul tau c6)))))))))) in *.
set (fl := add c0l (mul tau q)) in *.
set (Eg := B2R c0l + B2R tau * (B2R c1 + B2R tau * (B2R c2 + B2R tau * (B2R c3 +
  B2R tau * (B2R c4 + B2R tau * (B2R c5 + B2R tau * B2R c6)))))) in *.
set (P := asin_poly 34 (IZR j / 256 + B2R tau)) in *.
assert (B : bpow radix2 (-53) = / 9007199254740992 /\
            bpow radix2 (-64) = / 18446744073709551616 /\
            bpow radix2 (-66) = / 73786976294838206464 /\
            bpow radix2 (-68) = / 295147905179352825856 /\
            bpow radix2 (-11) = / 2048 /\ bpow radix2 (-28) = / 268435456)
  by (repeat split; reflexivity).
destruct B as (B53 & B64 & B66 & B68 & B11 & B28).
rewrite B53 in Hzl. rewrite B66 in Gfl. rewrite B68 in HT. rewrite B11 in Hfl.
rewrite B28 in Hzh. rewrite B64.
assert (Hz0 : 0 <= B2R zh) by lra.
assert (Btiny : 0 <= bpow radix2 (-1075) <= / 1267650600228229401496703205376 * B2R zh).
{ split; [apply bpow_ge_0|].
  apply Rle_trans with (bpow radix2 (-100) * bpow radix2 (-28)).
  - rewrite <- bpow_plus. apply bpow_le. lia.
  - change (bpow radix2 (-100)) with (/ 1267650600228229401496703205376).
    rewrite B28. apply Rmult_le_compat_l; lra. }
(* The products, as linear facts in [zh]. *)
pose proof (scale_le (B2R zh) (B2R fl) _ Hz0 Hfl) as M1.
pose proof (scale_le (B2R zh) (B2R fl - Eg) _ Hz0 Gfl) as M2.
pose proof (scale_le (B2R zh) (P - (B2R c0h + Eg)) _ Hz0 HT) as M3.
assert (Hc0a : Rabs (B2R c0h) <= 17 / 16) by (rewrite Rabs_pos_eq; lra).
assert (HEg : Rabs Eg <= 7 / 8 * / 2048 + 7 * / 73786976294838206464)
  by (apply Rabs_le_inv in Hfl; apply Rabs_le_inv in Gfl; apply Rabs_le; lra).
pose proof (prod_le (B2R zl) (B2R c0h) _ _ Hzl Hc0a) as M4.
pose proof (prod_le (B2R zl) (P - (B2R c0h + Eg)) _ _ Hzl HT) as M5.
pose proof (prod_le (B2R zl) Eg _ _ Hzl HEg) as M6.
assert (M7 : B2R zh <= B2R zh * B2R c0h <= 17 / 16 * B2R zh)
  by (clear - Hz0 Hc0; split; nra).
(* [rh = RN (zh c0h)], and [pe = zh c0h - rh] exactly. *)
destruct (FastExpErr.mul_e zh c0h Fzh Fc0) as (Frh & Erh & Hrh).
{ rewrite Rabs_pos_eq; lra. }
pose proof (err_le _ _ _ (bpow radix2 (-53)) (17 / 16 * B2R zh) _ (bpow_ge_0 _ _) Hrh
  ltac:(rewrite Rabs_pos_eq; lra)) as R1. rewrite B53 in R1.
assert (X : Generic.two_prod_is_exact fma zh c0h (mul zh c0h) = true).
{ apply prod_exact; try assumption.
  - rewrite Rabs_pos_eq by lra. change (bpow radix2 (-60)) with (/ 1152921504606846976). lra.
  - rewrite Rabs_pos_eq; lra.
  - lra. }
destruct (two_prod_err_correct fma zh c0h Fzh Fc0 X) as (_ & _ & _ & Fpe & Epe).
set (rh := mul zh c0h) in *.
set (pe := Generic.two_prod_err fma zh c0h rh) in *.
(* [a = RN (zh fl)], [b = RN (zl c0h)], [ab = RN (a + b)], [rl = RN (pe + ab)]. *)
destruct (FastExpErr.mul_e zh fl Fzh Ffl) as (Fa & Ea & Ha).
{ apply Rabs_le. lra. }
pose proof (err_le _ _ _ (bpow radix2 (-53)) (7 / 8 * / 2048 * B2R zh) _ (bpow_ge_0 _ _) Ha
  ltac:(apply Rabs_le; lra)) as R2. rewrite B53 in R2.
destruct (FastExpErr.mul_e zl c0h Fzl Fc0) as (Fb & Eb & Hb).
{ apply Rabs_le. lra. }
pose proof (err_le _ _ _ (bpow radix2 (-53)) (/ 9007199254740992 * B2R zh * (17 / 16)) _ (bpow_ge_0 _ _) Hb
  ltac:(apply Rabs_le; lra)) as R3. rewrite B53 in R3.
set (a := mul zh fl) in *. set (b := mul zl c0h) in *.
destruct (FastExpErr.add_e a b Fa Fb) as (Fab & Eab & Hab).
{ apply Rabs_le. lra. }
pose proof (err_le _ _ _ (bpow radix2 (-53)) ((7 / 8 * / 2048 + / 4503599627370496) * B2R zh) _ (bpow_ge_0 _ _) Hab
  ltac:(apply Rabs_le; lra)) as R4. rewrite B53 in R4.
set (ab := add a b) in *.
destruct (FastExpErr.add_e pe ab Fpe Fab) as (Frl & Erl & Hrl).
{ apply Rabs_le. lra. }
pose proof (err_le _ _ _ (bpow radix2 (-53)) ((7 / 8 * / 2048 + / 1125899906842624) * B2R zh) _ (bpow_ge_0 _ _) Hrl
  ltac:(apply Rabs_le; lra)) as R5. rewrite B53 in R5.
set (rl := add pe ab) in *.
(* [fast_two_sum] is exact. *)
destruct (FastAtanCore.lc_fts rh rl ch cl Frh Frl) as (Fch & Fcl & Ech & Esum).
{ left. rewrite (Rabs_pos_eq (B2R rh)) by lra. apply Rabs_le. lra. }
{ apply Rabs_le. lra. }
{ exact E. }
split; [exact Fch|]. split; [exact Fcl|]. split; [rewrite Esum; exact Ech|].
split; [apply Rabs_le_inv in HT; apply Rabs_le_inv in HEg; apply Rabs_le; lra|].
split; [rewrite Esum; apply Rabs_le; lra|].
(* For [zl = 0]: [b = 0] and [ab = a]. *)
intros L0.
assert (Eb0 : B2R b = 0) by (rewrite Eb, L0, Rmult_0_l; apply round_0; typeclasses eauto).
assert (Eab0 : B2R ab = B2R a).
{ rewrite Eab, Eb0, Rplus_0_r. apply round_generic; [typeclasses eauto | apply generic_format_B2R]. }
rewrite L0 in M4, M5, M6.
rewrite Esum. apply Rabs_le. lra.
Qed.

(** ** The series *)

(** [asin w >= w] for [0 <= w <= 1/2] ([asin_poly_bounds] with one term). *)
Lemma asin_ge : forall w, 0 <= w <= / 2 -> w <= asin w.
Proof.
intros w Hw. destruct (asin_poly_bounds 1 w (/ 2) Hw ltac:(lra)) as (H & _).
replace (asin_poly 1 (w ^ 2)) with 1 in H by (cbn; unfold asin_a; cbn; field). lra.
Qed.

(** The rest of the series of [asin w] after 34 terms is under [2^-67 w]
    for [0 <= w <= 1/2]: [asin_poly_bounds] bounds it by [b_34 w^69 / (69
    (1 - 1/4))], with [b_34 <= 1] and [w^68 <= 2^-68]. *)
Lemma series_rest :
  forall w, 0 <= w <= / 2 ->
  0 <= asin w - w * asin_poly 34 (w ^ 2) <= bpow radix2 (-67) * w.
Proof.
intros w Hw.
destruct (asin_poly_bounds 34 w (/ 2) Hw ltac:(lra)) as (H0 & H1).
split; [exact H0|]. apply Rle_trans with (1 := H1).
pose proof (asin_b_bounds 34) as Hb. pose proof (pos_INR 34) as HI.
assert (H68 : 0 <= w ^ 68 <= bpow radix2 (-68)).
{ split; [apply pow_le; lra|].
  apply Rle_trans with ((/ 2) ^ 68); [apply pow_incr; lra|].
  rewrite pow_inv, pow_IZR. reflexivity. }
assert (HD : 3 / 4 <= (2 * INR 34 + 1) * (1 - (/ 2) ^ 2)) by (cbn [pow]; lra).
change (w ^ (2 * 34 + 1)) with (w * w ^ 68).
apply Rmult_le_reg_r with ((2 * INR 34 + 1) * (1 - (/ 2) ^ 2)); [lra|].
unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
assert (HwM : 0 <= w * w ^ 68) by (apply Rmult_le_pos; lra).
apply Rle_trans with (w * bpow radix2 (-68)).
- apply Rle_trans with (1 * (w * w ^ 68)).
  + apply Rmult_le_compat_r; lra.
  + rewrite Rmult_1_l. apply Rmult_le_compat_l; lra.
- assert (B : bpow radix2 (-67) = 2 * bpow radix2 (-68)) by (cbn [bpow radix_val radix2]; lra).
  assert (Hwb : 0 <= w * bpow radix2 (-68)) by (apply Rmult_le_pos; [lra | apply bpow_ge_0]).
  rewrite B. set (D := (2 * INR 34 + 1) * (1 - (/ 2) ^ 2)) in *. nra.
Qed.

(** ** Without an FMA *)

(** [tail] is the same with and without an FMA: only [Generic.two_prod_err
    zh c0h rh] depends on it, and [zh c0h] is exact as a pair
    ([prod_exact]: [1 <= c0h <= 17/16] by [asin_coef_facts], so [2^-28 <=
    zh c0h <= 17/8]), so both give the same [f64]
    ([FastRound.two_prod_err_fma_eq]). *)
Lemma tail_fma :
  forall zh zl j tau,
  is_finite zh = true -> bpow radix2 (-28) <= B2R zh <= 2 -> (0 <= j <= 64)%Z ->
  tail true zh zl j tau = tail false zh zl j tau.
Proof.
intros zh zl j tau Fzh Hzh Hj.
destruct (asin_coef_facts j Hj) as (Fc & Hc0 & _).
pose proof (Fc 0%nat ltac:(lia)) as Fc0.
assert (B : bpow radix2 (-60) <= bpow radix2 (-28)) by (apply bpow_le; lia).
pose proof (bpow_ge_0 radix2 (-28)) as P.
assert (Hp : bpow radix2 (-60) <= Rabs (B2R zh * B2R (DyadicAtan.asin_coef j 0)) <= 4).
{ assert (H1 : B2R zh <= B2R zh * B2R (DyadicAtan.asin_coef j 0))
    by (rewrite <- (Rmult_1_r (B2R zh)) at 1; apply Rmult_le_compat_l; lra).
  assert (H2 : B2R zh * B2R (DyadicAtan.asin_coef j 0) <= 2 * (17 / 16))
    by (apply Rmult_le_compat; lra).
  rewrite Rabs_pos_eq by lra. split; lra. }
assert (Hz : Rabs (B2R zh) <= 2) by (rewrite Rabs_pos_eq; lra).
assert (Hc : Rabs (B2R (DyadicAtan.asin_coef j 0)) <= 2) by (rewrite Rabs_pos_eq; lra).
unfold tail. cbv zeta.
rewrite (FastRound.two_prod_err_fma_eq _ _ Fzh Fc0 (prod_exact true _ _ Fzh Fc0 Hp Hz Hc)
  (prod_exact false _ _ Fzh Fc0 Hp Hz Hc)).
reflexivity.
Qed.
