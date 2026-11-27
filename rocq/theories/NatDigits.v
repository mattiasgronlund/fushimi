(** * The digits of a number, and [Nat::from_hex]

    A literal spells a number by its ASCII digits, the most significant
    first. [digits_val] gives the number that the digits [s] spell in a
    base, [dec_digit] and [hex_digit] say which bytes are digits, and this
    file, [NatFromDec.v] and [NatToDec.v] state what [Nat] reads and writes
    in their terms. These definitions are not Rust: like
    [nat_ok] in [NatOps.v], they are checked by reading.

    [digits] of [src/nat.rs] reads at most 19 decimal or 16 hexadecimal
    digits into a [u64] ([digits_dec], [digits_hex]), and [from_hex_correct]
    shows that [Nat::from_hex] returns the limbs of the number that its
    hexadecimal digits spell. *)

From Stdlib Require Import ZArith Lia List.
From Fushimi Require Import Model Limbs NatOps.

Open Scope Z_scope.

(** An ASCII decimal digit, [0] to [9]. *)
Definition dec_digit (c : Z) : Prop := 48 <= c <= 57.

(** An ASCII hexadecimal digit: [0] to [9], [A] to [F] or [a] to [f]. *)
Definition hex_digit (c : Z) : Prop := 48 <= c <= 57 \/ 65 <= c <= 70 \/ 97 <= c <= 102.

(** The value of the digit [c]. *)
Definition digit_value (c : Z) : Z :=
  if c <=? 57 then c - 48 else if c <=? 70 then c - 55 else c - 87.

(** The number that the digits [s] spell in base [radix], the first digit
    the most significant, and 0 for no digits. *)
Definition digits_val (radix : Z) (s : list Z) : Z :=
  fold_left (fun n c => n * radix + digit_value c) s 0.

(** The fold that [digits_val] runs, from [n] instead of 0, puts [n] in
    front of the digits [t]. *)
Lemma digits_val_fold :
  forall r t n,
  fold_left (fun n c => n * r + digit_value c) t n =
  n * r ^ Z.of_nat (length t) + fold_left (fun n c => n * r + digit_value c) t 0.
Proof.
intros r t. induction t as [|c t IH]; intros n.
- cbn [fold_left length Z.of_nat]. rewrite Z.pow_0_r. ring.
- cbn [fold_left length].
  rewrite (IH (n * r + digit_value c)), (IH (0 * r + digit_value c)).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma digits_val_app :
  forall r s t,
  digits_val r (s ++ t) = digits_val r s * r ^ Z.of_nat (length t) + digits_val r t.
Proof.
intros r s t. unfold digits_val. rewrite fold_left_app. apply digits_val_fold.
Qed.

Lemma digits_val_cons :
  forall r c t,
  digits_val r (c :: t) = digit_value c * r ^ Z.of_nat (length t) + digits_val r t.
Proof.
intros r c t. unfold digits_val. cbn [fold_left].
rewrite (digits_val_fold r t (0 * r + digit_value c)). ring.
Qed.

(** Digits whose values are below [r] spell a number below [r ^ n] for [n]
    digits. *)
Lemma digits_val_bounds :
  forall r (P : Z -> Prop), 0 < r -> (forall c, P c -> 0 <= digit_value c < r) ->
  forall s, Forall P s -> 0 <= digits_val r s < r ^ Z.of_nat (length s).
Proof.
intros r P Hr HP s. induction s as [|c s IH]; intros Hs.
- unfold digits_val. cbn [fold_left length Z.of_nat]. rewrite Z.pow_0_r. lia.
- apply Forall_cons_iff in Hs. destruct Hs as [Hc Hs].
  specialize (IH Hs). specialize (HP c Hc).
  rewrite digits_val_cons. cbn [length]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  (* [d r^n + v <= (r - 1) r^n + r^n - 1 < r r^n]. *)
  pose proof (Z.pow_pos_nonneg r (Z.of_nat (length s)) Hr ltac:(lia)) as P0.
  assert (H1 : digit_value c * r ^ Z.of_nat (length s) <= (r - 1) * r ^ Z.of_nat (length s))
    by (apply Z.mul_le_mono_nonneg_r; lia).
  split; [nia | lia].
Qed.

Lemma digit_value_dec : forall c, dec_digit c -> 0 <= digit_value c < 10.
Proof.
intros c Hc. unfold dec_digit in Hc. unfold digit_value.
destruct (Z.leb_spec c 57); cbv beta iota; lia.
Qed.

Lemma digit_value_hex : forall c, hex_digit c -> 0 <= digit_value c < 16.
Proof.
intros c Hc. unfold hex_digit in Hc. unfold digit_value.
destruct (Z.leb_spec c 57), (Z.leb_spec c 70); cbv beta iota; lia.
Qed.

Lemma digits_val_dec_bounds :
  forall s, Forall dec_digit s -> 0 <= digits_val 10 s < 10 ^ Z.of_nat (length s).
Proof.
intros s Hs. exact (digits_val_bounds 10 dec_digit ltac:(lia) digit_value_dec s Hs).
Qed.

Lemma digits_val_hex_bounds :
  forall s, Forall hex_digit s -> 0 <= digits_val 16 s < 16 ^ Z.of_nat (length s).
Proof.
intros s Hs. exact (digits_val_bounds 16 hex_digit ltac:(lia) digit_value_hex s Hs).
Qed.

(** Rewrites each comparison of [Z]s in the goal to [true] or [false] when
    [lia] decides it. *)
Ltac zbool :=
  repeat (match goal with
    | |- context [?a <=? ?b] =>
        first [rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia]
    | |- context [?a <? ?b] =>
        first [rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia]
    end; cbn [andb]).

Lemma to_digit_dec : forall c, dec_digit c -> NatLimbs.to_digit c 10 = Some (digit_value c).
Proof.
intros c Hc. unfold dec_digit in Hc. unfold NatLimbs.to_digit, digit_value. zbool. reflexivity.
Qed.

Lemma to_digit_hex : forall c, hex_digit c -> NatLimbs.to_digit c 16 = Some (digit_value c).
Proof.
intros c Hc. unfold hex_digit in Hc. unfold NatLimbs.to_digit, digit_value.
destruct Hc as [Hc|[Hc|Hc]]; zbool; reflexivity.
Qed.

(** [digits] reads the digits [s] after [n] when the number that they
    spell after [n] fits a [u64]: each partial sum is at most that number. *)
Lemma digits_from_correct :
  forall radix s n, 0 < radix ->
  Forall (fun c => NatLimbs.to_digit c radix = Some (digit_value c) /\
                   0 <= digit_value c < radix) s ->
  0 <= n -> n * radix ^ Z.of_nat (length s) + digits_val radix s < 2 ^ 64 ->
  NatLimbs.digits_from s radix n = Some (n * radix ^ Z.of_nat (length s) + digits_val radix s).
Proof.
intros radix s. induction s as [|c s IH]; intros n Hr Hs Hn Hb.
- cbn [NatLimbs.digits_from length Z.of_nat]. unfold digits_val. cbn [fold_left].
  rewrite Z.pow_0_r. f_equal; ring.
- apply Forall_cons_iff in Hs. destruct Hs as [[Hd Hc] Hs].
  pose proof (digits_val_bounds radix _ Hr (fun c H => proj2 H) s Hs) as Bs.
  pose proof (Z.pow_pos_nonneg radix (Z.of_nat (length s)) Hr ltac:(lia)) as P0.
  rewrite digits_val_cons in Hb |- *. cbn [length] in Hb |- *.
  rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hb |- * by lia.
  cbn [NatLimbs.digits_from]. rewrite Hd. cbn beta iota.
  assert (H0 : 0 <= n * radix + digit_value c) by nia.
  assert (H1 : n * radix + digit_value c <=
               (n * radix + digit_value c) * radix ^ Z.of_nat (length s)).
  { rewrite <- (Z.mul_1_r (n * radix + digit_value c)) at 1.
    apply Z.mul_le_mono_nonneg_l; lia. }
  assert (H2 : (n * radix + digit_value c) * radix ^ Z.of_nat (length s) + digits_val radix s
               < 2 ^ 64) by (rewrite Z.mul_add_distr_r; nia).
  rewrite checked_u_some by lia. cbn beta iota.
  rewrite IH by first [exact Hr | exact Hs | exact H0 | exact H2].
  f_equal; ring.
Qed.

(** At most 19 decimal digits spell a number below [10 ^ 19 < 2 ^ 64]. *)
Lemma digits_dec :
  forall s, Forall dec_digit s -> (length s <= 19)%nat ->
  NatLimbs.digits s 10 = Some (digits_val 10 s).
Proof.
intros s Hs Hl. unfold NatLimbs.digits.
pose proof (digits_val_dec_bounds s Hs) as B.
assert (Hp : 10 ^ Z.of_nat (length s) <= 10 ^ 19) by (apply Z.pow_le_mono_r; lia).
rewrite digits_from_correct.
- f_equal; ring.
- lia.
- eapply Forall_impl; [|exact Hs]. intros c Hc.
  split; [exact (to_digit_dec c Hc) | exact (digit_value_dec c Hc)].
- lia.
- lia.
Qed.

(** At most 16 hexadecimal digits spell a number below [16 ^ 16 = 2 ^ 64]. *)
Lemma digits_hex :
  forall s, Forall hex_digit s -> (length s <= 16)%nat ->
  NatLimbs.digits s 16 = Some (digits_val 16 s).
Proof.
intros s Hs Hl. unfold NatLimbs.digits.
pose proof (digits_val_hex_bounds s Hs) as B.
assert (Hp : 16 ^ Z.of_nat (length s) <= 16 ^ 16) by (apply Z.pow_le_mono_r; lia).
rewrite digits_from_correct.
- f_equal; ring.
- lia.
- eapply Forall_impl; [|exact Hs]. intros c Hc.
  split; [exact (to_digit_hex c Hc) | exact (digit_value_hex c Hc)].
- lia.
- lia.
Qed.

(** The pieces of at most 16 digits that [take_rchunks j 16 s] cuts from
    the end of [s], for [length s <= 16 j], read as the limbs of the number
    that [s] spells, the least significant first: each piece but the last
    has 16 digits, and [16 ^ 16 = 2 ^ 64]. *)
Lemma take_rchunks_hex :
  forall j s, Forall hex_digit s -> (length s <= 16 * j)%nat ->
  exists v,
  NatLimbs.map_some (fun c => NatLimbs.digits c 16) (NatLimbs.take_rchunks j 16 s) = Some v /\
  limbs_ok v /\ Limbs.val v = digits_val 16 s.
Proof.
induction j as [|j IH]; intros s Hs Hl.
- destruct s as [|c s]; [|cbn [length] in Hl; lia].
  exists nil. split; [reflexivity|]. split; [constructor | reflexivity].
- cbn [NatLimbs.take_rchunks NatLimbs.map_some].
  remember (length s - 16)%nat as k eqn:Ek.
  pose proof (firstn_skipn k s) as Es.
  assert (Hs' : Forall hex_digit (firstn k s) /\ Forall hex_digit (skipn k s))
    by (apply Forall_app; rewrite Es; exact Hs).
  destruct Hs' as [Hf Hk].
  assert (Lk : length (skipn k s) = (length s - k)%nat) by apply length_skipn.
  assert (Lf : length (firstn k s) = k) by (rewrite length_firstn; lia).
  rewrite (digits_hex _ Hk ltac:(lia)). cbn beta iota.
  destruct (IH (firstn k s) Hf ltac:(lia)) as (vs & E & Hvs & Vvs).
  rewrite E. cbn beta iota. eexists. split; [reflexivity|].
  pose proof (digits_val_hex_bounds _ Hk) as B.
  assert (Hp : 16 ^ Z.of_nat (length (skipn k s)) <= 2 ^ 64)
    by (change (2 ^ 64) with (16 ^ 16); apply Z.pow_le_mono_r; lia).
  split; [constructor; [cbv beta; lia | exact Hvs]|].
  assert (Ev : digits_val 16 s = digits_val 16 (firstn k s ++ skipn k s)) by now rewrite Es.
  cbn [Limbs.val]. rewrite Vvs, Ev, digits_val_app.
  destruct (Nat.le_gt_cases 16 (length s)) as [H16|H16].
  + (* Each piece but the last has 16 digits. *)
    replace (length (skipn k s)) with 16%nat by lia.
    change (16 ^ Z.of_nat 16) with (2 ^ 64). ring.
  + (* The last piece is all of [s]: nothing is left in front of it. *)
    replace k with 0%nat by lia.
    change (digits_val 16 (firstn 0 s)) with 0. ring.
Qed.

(** [Nat::from_hex(s)] *)
Theorem from_hex_correct :
  forall s, Forall hex_digit s ->
  NatLimbs.from_hex s = Some (NatLimbs.to_limbs (digits_val 16 s)).
Proof.
intros s Hs. unfold NatLimbs.from_hex, NatLimbs.rchunks.
(* [(length s + 15) / 16] pieces of at most 16 digits cover [s]. *)
assert (Hl : (length s <= 16 * ((length s + 16 - 1) / 16))%nat).
{ pose proof (Nat.div_mod (length s + 16 - 1) 16 ltac:(lia)).
  pose proof (Nat.mod_upper_bound (length s + 16 - 1) 16 ltac:(lia)). lia. }
destruct (take_rchunks_hex _ s Hs Hl) as (v & E & Hv & Vv).
rewrite E. cbn beta iota. f_equal.
destruct (from_limbs_correct v Hv) as [Hok Hval].
rewrite <- Vv, <- Hval. symmetry. now apply to_limbs_val.
Qed.
