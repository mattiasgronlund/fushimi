(** * [Nat::from_dec]

    [from_dec_correct] shows that [Nat::from_dec] returns the limbs of the
    number that its decimal digits spell. [dec_chunks] reads up to 38
    digits at a time into a [u128] ([dec_u128_correct]) and adds them to
    the limbs so far times [10 ^ 38] ([mul_add_u128_correct]); the carry is
    not 0 for limbs that are not 0, so that [push_u128] keeps the top limb
    nonzero ([push_u128_correct]). Above [DEC_CUTOFF] digits, the others
    are read 19 at a time by [mul_add_u64] ([NatOps.mul_add_u64_correct]). *)

From Stdlib Require Import ZArith Lia List.
From Fushimi Require Import Model Limbs NatOps NatDigits.

Open Scope Z_scope.

Lemma push_u128_correct :
  forall x c, limbs_ok x -> 0 <= c < 2 ^ 128 -> nat_ok x \/ c <> 0 ->
  nat_ok (NatLimbs.push_u128 x c) /\
  Limbs.val (NatLimbs.push_u128 x c) = Limbs.val x + c * 2 ^ (64 * Z.of_nat (length x)).
Proof.
intros x c Hx Hc Hok. unfold NatLimbs.push_u128. cbv zeta.
rewrite Z.shiftr_div_pow2 by lia.
destruct (Z.eqb_spec c 0) as [->|Hc0].
- (* No limb for 0. *)
  rewrite Z.div_0_l, Z.eqb_refl by lia. cbv beta iota.
  split; [destruct Hok as [H|H]; [exact H | contradiction] | ring].
- pose proof (Z.div_mod c (2 ^ 64) ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound c (2 ^ 64) ltac:(lia)) as B0.
  destruct (Z.eqb_spec (c / 2 ^ 64) 0) as [Hh|Hh]; cbv beta iota.
  + (* One limb below 2^64, which is [c] and not 0. *)
    rewrite Z.mod_small by lia.
    split.
    * split; [apply limbs_ok_app; [exact Hx | constructor; [lia | constructor]]|].
      right. rewrite length_app. cbn [length].
      rewrite Nat.add_sub. unfold Limbs.limb. now rewrite nth_middle.
    * rewrite val_app. cbn [Limbs.val]. ring.
  + (* Two limbs above, the top one [c / 2^64], in [1, 2^64) as [c < 2^128]. *)
    assert (Bh : 0 < c / 2 ^ 64 < 2 ^ 64).
    { split; [pose proof (Z.div_pos c (2 ^ 64) ltac:(lia) ltac:(lia)); lia|].
      apply Z.div_lt_upper_bound; lia. }
    rewrite (Z.mod_small (c / 2 ^ 64)) by lia.
    split.
    * split.
      { apply limbs_ok_app; [apply limbs_ok_app; [exact Hx|]|]; constructor; (lia || constructor). }
      right. rewrite length_app. cbn [length].
      rewrite Nat.add_sub. unfold Limbs.limb. rewrite nth_middle. lia.
    * rewrite !val_app, length_app. cbn [Limbs.val length].
      rewrite Nat.add_1_r, pow64_S.
      set (P := 2 ^ (64 * Z.of_nat (length x))).
      assert (E : c * P = P * (c mod 2 ^ 64) + 2 ^ 64 * P * (c / 2 ^ 64)).
      { rewrite D at 1. ring. }
      rewrite E. ring.
Qed.

(** The loop of [mul_add_u128], for [m = m1 * 2^64 + m0] with [m0 < 2^64]
    and [m1 < 2^63]. *)
Lemma mul_add_u128_from_correct :
  forall x m0 m1 c, limbs_ok x -> 0 <= m0 < 2 ^ 64 -> 0 <= m1 < 2 ^ 63 -> 0 <= c < 2 ^ 127 ->
  exists s c', NatLimbs.mul_add_u128_from x m0 m1 c = Some (s, c') /\
  limbs_ok s /\ length s = length x /\ 0 <= c' < 2 ^ 127 /\
  Limbs.val s + c' * 2 ^ (64 * Z.of_nat (length x)) = Limbs.val x * (m1 * 2 ^ 64 + m0) + c.
Proof.
induction x as [|l x IH]; intros m0 m1 c Hx Hm0 Hm1 Hc.
- exists nil, c. cbn [NatLimbs.mul_add_u128_from].
  split; [reflexivity|]. split; [constructor|]. split; [reflexivity|]. split; [exact Hc|].
  cbn [Limbs.val length]. rewrite pow64_0. ring.
- apply limbs_ok_cons in Hx as [Hl Hx].
  cbn [NatLimbs.mul_add_u128_from].
  rewrite !Z.shiftr_div_pow2 by lia.
  (* c = c1 * 2^64 + c0 with c1 < 2^63. *)
  pose proof (Z.div_mod c (2 ^ 64) ltac:(lia)) as Dc.
  pose proof (Z.mod_pos_bound c (2 ^ 64) ltac:(lia)) as Bc0.
  assert (Bc1 : 0 <= c / 2 ^ 64 < 2 ^ 63).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  (* t = l * m0 + c0 <= (2^64 - 1)^2 + 2^64 - 1 = (2^64 - 1) 2^64 < 2^128. *)
  assert (Blm0 : 0 <= l * m0 <= (2 ^ 64 - 1) * (2 ^ 64 - 1)) by nia.
  remember (l * m0 + c mod 2 ^ 64) as t eqn:Et.
  assert (Bt : 0 <= t <= (2 ^ 64 - 1) * 2 ^ 64) by lia.
  rewrite (checked_u_some 128 t) by lia. cbv beta iota.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod t (2 ^ 64) ltac:(lia)) as Dt.
  pose proof (Z.mod_pos_bound t (2 ^ 64) ltac:(lia)) as Bt0.
  assert (Bt1 : 0 <= t / 2 ^ 64 < 2 ^ 64).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  (* l * m1 + c1 + t / 2^64
     <= (2^64 - 1) (2^63 - 1) + 2^63 - 1 + 2^64 - 1 = 2^127 - 1. *)
  assert (Blm1 : 0 <= l * m1 <= (2 ^ 64 - 1) * (2 ^ 63 - 1)) by nia.
  rewrite (checked_u_some 128 (l * m1 + c / 2 ^ 64 + t / 2 ^ 64)) by lia. cbv beta iota.
  destruct (IH m0 m1 (l * m1 + c / 2 ^ 64 + t / 2 ^ 64) Hx Hm0 Hm1 ltac:(lia))
    as (s & c' & E & Hs & Hlen & Hc' & Hv).
  rewrite E. exists (t mod 2 ^ 64 :: s), c'.
  split; [reflexivity|].
  split; [apply limbs_ok_cons; split; [exact Bt0 | exact Hs]|].
  split; [cbn [length]; now rewrite Hlen|]. split; [exact Hc'|].
  cbn [Limbs.val length]. rewrite pow64_S.
  (* l * m + c = t + (l * m1 + c1) * 2^64, so the limb is t mod 2^64 and
     the carry into the rest l * m1 + c1 + t / 2^64. *)
  replace (t mod 2 ^ 64 + 2 ^ 64 * Limbs.val s
           + c' * (2 ^ 64 * 2 ^ (64 * Z.of_nat (length x))))
    with (t mod 2 ^ 64 + 2 ^ 64 * (Limbs.val s + c' * 2 ^ (64 * Z.of_nat (length x))))
    by ring.
  rewrite Hv. lia.
Qed.

Lemma mul_add_u128_correct :
  forall x m c, limbs_ok x -> 0 <= m < 2 ^ 127 -> 0 <= c < 2 ^ 127 ->
  exists s c', NatLimbs.mul_add_u128 x m c = Some (s, c') /\
  limbs_ok s /\ length s = length x /\ 0 <= c' < 2 ^ 127 /\
  Limbs.val s + c' * 2 ^ (64 * Z.of_nat (length x)) = Limbs.val x * m + c.
Proof.
intros x m c Hx Hm Hc. unfold NatLimbs.mul_add_u128.
rewrite Z.shiftr_div_pow2 by lia.
(* m = m1 * 2^64 + m0, with m1 = m / 2^64 < 2^63. *)
assert (Bm1 : 0 <= m / 2 ^ 64 < 2 ^ 63).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
rewrite (Z.mod_small (m / 2 ^ 64)) by lia.
pose proof (Z.div_mod m (2 ^ 64) ltac:(lia)) as Dm.
pose proof (Z.mod_pos_bound m (2 ^ 64) ltac:(lia)) as Bm0.
destruct (mul_add_u128_from_correct x (m mod 2 ^ 64) (m / 2 ^ 64) c Hx Bm0 Bm1 Hc)
  as (s & c' & E & Hs & Hlen & Hc' & Hv).
replace (m / 2 ^ 64 * 2 ^ 64 + m mod 2 ^ 64) with m in Hv by lia.
exists s, c'. auto.
Qed.

Lemma dec_u128_correct :
  forall s, Forall dec_digit s -> (length s <= 38)%nat ->
  NatLimbs.dec_u128 s = Some (digits_val 10 s).
Proof.
intros s Hs Hlen. unfold NatLimbs.dec_u128. cbv zeta.
pose proof Hs as Hs'. rewrite <- (firstn_skipn (length s - 19) s) in Hs'.
apply Forall_app in Hs' as [Hh Hl].
assert (Lh : length (firstn (length s - 19) s) = (length s - 19)%nat)
  by (rewrite length_firstn; lia).
assert (Ll : length (skipn (length s - 19) s) = (length s - (length s - 19))%nat)
  by apply length_skipn.
(* At most 19 digits in front of the last 19, and at most 19 of those. *)
rewrite (digits_dec _ Hh) by lia. rewrite (digits_dec _ Hl) by lia. cbv beta iota.
pose proof (digits_val_dec_bounds _ Hh) as Bh. pose proof (digits_val_dec_bounds _ Hl) as Bl.
rewrite Lh in Bh. rewrite Ll in Bl.
assert (E : digits_val 10 s =
  digits_val 10 (firstn (length s - 19) s) * 10 ^ Z.of_nat (length (skipn (length s - 19) s))
  + digits_val 10 (skipn (length s - 19) s)).
{ rewrite <- digits_val_app, firstn_skipn. reflexivity. }
rewrite Ll in E. unfold NatLimbs.TEN19.
destruct (Nat.le_gt_cases 19 (length s)) as [H19|H19].
- (* The last 19 digits are a tail of exactly 19, so the head counts 10^19 times. *)
  replace (length s - (length s - 19))%nat with 19%nat in E, Bl by lia.
  change (Z.of_nat 19) with 19 in E, Bl.
  assert (Ph : 10 ^ Z.of_nat (length s - 19) <= 10 ^ 19) by (apply Z.pow_le_mono_r; lia).
  rewrite checked_u_some by lia. now rewrite E.
- (* Fewer than 19 digits: no head, and the tail is [s]. *)
  replace (length s - 19)%nat with 0%nat in E, Bl |- * by lia.
  cbn [firstn skipn] in E, Bl |- *. rewrite Nat.sub_0_r in Bl.
  change (digits_val 10 nil) with 0 in E |- *.
  assert (Pl : 10 ^ Z.of_nat (length s) <= 10 ^ 19) by (apply Z.pow_le_mono_r; lia).
  rewrite checked_u_some by lia. reflexivity.
Qed.

(** ** Chunks *)

(** [take_chunks j k s] cuts [s] of [j * k] bytes into [j] pieces of [k]. *)
Lemma take_chunks_spec :
  forall j k s, length s = (j * k)%nat ->
  concat (NatLimbs.take_chunks j k s) = s /\
  Forall (fun c => length c = k) (NatLimbs.take_chunks j k s).
Proof.
induction j as [|j IH]; intros k s Hs; cbn [NatLimbs.take_chunks concat].
- split; [|constructor]. destruct s; [reflexivity | cbn in Hs; discriminate Hs].
- destruct (IH k (skipn k s)) as [E F].
  { rewrite length_skipn, Hs. lia. }
  split; [rewrite E; apply firstn_skipn|].
  constructor; [rewrite length_firstn, Hs; lia | exact F].
Qed.

(** [chunks_exact k] drops nothing from [s] of a multiple of [k] bytes. *)
Lemma chunks_exact_spec :
  forall k s j, k <> 0%nat -> length s = (j * k)%nat ->
  concat (NatLimbs.chunks_exact k s) = s /\
  Forall (fun c => length c = k) (NatLimbs.chunks_exact k s).
Proof.
intros k s j Hk Hs. unfold NatLimbs.chunks_exact.
rewrite Hs, Nat.div_mul by exact Hk. now apply take_chunks_spec.
Qed.

(** ** [dec_chunks] *)

(** The [for] loop of [dec_chunks] appends the digits of its chunks of 38
    to the digits [pre] that [x] holds. *)
Lemma dec_chunks_loop_correct :
  forall cs x pre, Forall (fun c => length c = 38%nat) cs -> Forall dec_digit (concat cs) ->
  nat_ok x -> Limbs.val x = digits_val 10 pre ->
  exists y, NatLimbs.dec_chunks_loop cs x = Some y /\ nat_ok y /\
  Limbs.val y = digits_val 10 (pre ++ concat cs).
Proof.
induction cs as [|c cs IH]; intros x pre Hl Hd Hx Hv; cbn [NatLimbs.dec_chunks_loop concat].
- exists x. rewrite app_nil_r. auto.
- apply Forall_cons_iff in Hl as [Hc Hl].
  apply Forall_app in Hd as [Hdc Hd].
  rewrite (dec_u128_correct c Hdc) by lia. cbv beta iota.
  pose proof (digits_val_dec_bounds c Hdc) as Bd. rewrite Hc in Bd.
  change (Z.of_nat 38) with 38 in Bd.
  (* 10^38 < 2^127, and so is the chunk. *)
  destruct (mul_add_u128_correct x NatLimbs.TEN38 (digits_val 10 c) (proj1 Hx))
    as (x' & carry & E & Hx' & Hlen & Hcarry & Hv').
  { unfold NatLimbs.TEN38. lia. }
  { lia. }
  rewrite E. cbv beta iota. unfold NatLimbs.TEN38 in Hv'.
  assert (Hok : nat_ok x' \/ carry <> 0).
  { destruct x as [|a x0].
    - (* [x = 0] has no limbs, nor has [x'], which is then 0 too. *)
      left. destruct x' as [|b x']; [exact nat_ok_nil | discriminate Hlen].
    - (* For [x] of [n] limbs, x * 10^38 >= 2^(64 (n - 1)) * 10^38 > 2^(64 n),
         and [x'] is below 2^(64 n), so the carry is not 0. *)
      right. intros ->.
      pose proof (proj1 (nat_ok_iff_val (a :: x0) (proj1 Hx) ltac:(discriminate)) Hx) as Hlow.
      replace (length (a :: x0) - 1)%nat with (length x0) in Hlow by (cbn [length]; lia).
      pose proof (val_bounds x' Hx') as Bx'. rewrite Hlen in Bx'. cbn [length] in Bx'.
      rewrite pow64_S in Bx'. pose proof (pow64_pos (length x0)). lia. }
  destruct (push_u128_correct x' carry Hx' ltac:(lia) Hok) as [Hp Hpv].
  destruct (IH (NatLimbs.push_u128 x' carry) (pre ++ c) Hl Hd Hp) as (y & Ey & Hy & Hyv).
  { rewrite Hpv, Hlen, Hv', digits_val_app, Hc, <- Hv. reflexivity. }
  exists y. split; [exact Ey|]. split; [exact Hy|]. now rewrite Hyv, app_assoc.
Qed.

Lemma dec_chunks_correct :
  forall s, Forall dec_digit s ->
  exists x, NatLimbs.dec_chunks s = Some x /\ nat_ok x /\ Limbs.val x = digits_val 10 s.
Proof.
intros s Hs. unfold NatLimbs.dec_chunks. cbv zeta.
pose proof (Nat.div_mod (length s) 38 ltac:(lia)) as D.
pose proof (Nat.mod_upper_bound (length s) 38 ltac:(lia)) as B.
pose proof Hs as Hs'. rewrite <- (firstn_skipn (length s mod 38) s) in Hs'.
apply Forall_app in Hs' as [Hh Ht].
assert (Lh : length (firstn (length s mod 38) s) = (length s mod 38)%nat)
  by (rewrite length_firstn; lia).
(* The first [length s mod 38 < 38] digits. *)
rewrite (dec_u128_correct _ Hh) by lia. cbv beta iota.
pose proof (digits_val_dec_bounds _ Hh) as Bh. rewrite Lh in Bh.
assert (P38 : 10 ^ Z.of_nat (length s mod 38) <= 10 ^ 38) by (apply Z.pow_le_mono_r; lia).
assert (Bh' : 0 <= digits_val 10 (firstn (length s mod 38) s) < 2 ^ 128) by lia.
destruct (push_u128_correct nil _ ltac:(constructor) Bh' (or_introl nat_ok_nil)) as [Hp Hpv].
cbn [Limbs.val length] in Hpv. rewrite pow64_0 in Hpv.
(* Then the others, a multiple of 38. *)
destruct (chunks_exact_spec 38 (skipn (length s mod 38) s) (length s / 38)) as [Ec Lc].
{ lia. }
{ rewrite length_skipn. lia. }
assert (Hd : Forall dec_digit (concat (NatLimbs.chunks_exact 38 (skipn (length s mod 38) s))))
  by now rewrite Ec.
destruct (dec_chunks_loop_correct _ _ (firstn (length s mod 38) s) Lc Hd Hp ltac:(lia))
  as (y & Ey & Hy & Hyv).
exists y. split; [exact Ey|]. split; [exact Hy|]. now rewrite Hyv, Ec, firstn_skipn.
Qed.

(** ** [from_dec] *)

(** The [for] loop of [from_dec] appends the digits of its chunks of 19 to
    the digits [pre] that [n] holds. *)
Lemma from_dec_loop_correct :
  forall cs n pre, Forall (fun c => length c = 19%nat) cs -> Forall dec_digit (concat cs) ->
  nat_ok n -> Limbs.val n = digits_val 10 pre ->
  exists y, NatLimbs.from_dec_loop cs n = Some y /\ nat_ok y /\
  Limbs.val y = digits_val 10 (pre ++ concat cs).
Proof.
induction cs as [|c cs IH]; intros n pre Hl Hd Hn Hv; cbn [NatLimbs.from_dec_loop concat].
- exists n. rewrite app_nil_r. auto.
- apply Forall_cons_iff in Hl as [Hc Hl].
  apply Forall_app in Hd as [Hdc Hd].
  rewrite (digits_dec c Hdc) by lia. cbv beta iota.
  pose proof (digits_val_dec_bounds c Hdc) as Bd. rewrite Hc in Bd.
  change (Z.of_nat 19) with 19 in Bd.
  (* 10^19 < 2^64, and so is the chunk. *)
  destruct (mul_add_u64_correct n NatLimbs.TEN19 (digits_val 10 c) Hn) as (n' & E & Hn' & Hv').
  { unfold NatLimbs.TEN19. lia. }
  { lia. }
  rewrite E. cbv beta iota.
  destruct (IH n' (pre ++ c) Hl Hd Hn') as (y & Ey & Hy & Hyv).
  { rewrite Hv', digits_val_app, Hc, <- Hv. reflexivity. }
  exists y. split; [exact Ey|]. split; [exact Hy|]. now rewrite Hyv, app_assoc.
Qed.

(** [Nat::from_dec(s)] *)
Theorem from_dec_correct :
  forall s, Forall dec_digit s ->
  NatLimbs.from_dec s = Some (NatLimbs.to_limbs (digits_val 10 s)).
Proof.
intros s Hs. unfold NatLimbs.from_dec.
destruct (Nat.leb_spec (length s) 19) as [H19|H19].
- (* Below 10^19 < 2^64: one limb, or none for 0. *)
  rewrite (digits_dec s Hs H19). cbv beta iota.
  pose proof (digits_val_dec_bounds s Hs) as B.
  assert (P : 10 ^ Z.of_nat (length s) <= 10 ^ 19) by (apply Z.pow_le_mono_r; lia).
  assert (Bc : 0 <= digits_val 10 s < 2 ^ 128) by lia.
  destruct (push_u128_correct nil _ ltac:(constructor) Bc (or_introl nat_ok_nil)) as [Hp Hpv].
  cbn [Limbs.val length] in Hpv. rewrite pow64_0 in Hpv.
  f_equal. rewrite <- (to_limbs_val _ Hp). f_equal. lia.
- cbv zeta. unfold NatLimbs.DEC_CUTOFF.
  (* The tail has [rest = q * 19] digits, q = ceil((length s - 1000) / 19),
     and [rest <= length s]: it is 0 up to 1000 digits, and at most
     length s - 1000 + 18 above. *)
  pose proof (Nat.div_mod (length s - 1000 + 18) 19 ltac:(lia)) as D.
  set (q := ((length s - 1000 + 18) / 19)%nat) in *.
  assert (Hq : (q * 19 <= length s)%nat) by lia.
  pose proof Hs as Hs'. rewrite <- (firstn_skipn (length s - q * 19) s) in Hs'.
  apply Forall_app in Hs' as [Hh Ht].
  destruct (dec_chunks_correct _ Hh) as (x & E & Hx & Hxv).
  rewrite E. cbv beta iota.
  destruct (chunks_exact_spec 19 (skipn (length s - q * 19) s) q) as [Ec Lc].
  { lia. }
  { rewrite length_skipn. lia. }
  assert (Hd : Forall dec_digit (concat (NatLimbs.chunks_exact 19 (skipn (length s - q * 19) s))))
    by now rewrite Ec.
  destruct (from_dec_loop_correct _ _ _ Lc Hd Hx Hxv) as (y & Ey & Hy & Hyv).
  rewrite Ey. f_equal. rewrite <- (to_limbs_val _ Hy). f_equal.
  now rewrite Hyv, Ec, firstn_skipn.
Qed.
