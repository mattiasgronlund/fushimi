(** * [Nat::to_dec]

    [to_dec_correct] shows that [Nat::to_dec] writes the decimal digits of
    the number that its limbs hold, with no zero in front, and [0] for 0.
    [div_rem_ten19] divides by [10 ^ 19] with [div_ten19]
    ([NatDivTen19.v]) and leaves limbs with no zero limb at the top
    ([div_rem_ten19_correct]). The [while] loop of [to_dec] ends within the
    fuel [2 * length x] of [NatLimbs.to_dec], as each pass divides by
    [10 ^ 19 > 2 ^ 63]. [write_digits] writes the digits of a number below
    [10 ^ n] with zeros in front to fill [n] bytes ([write_digits_correct]),
    and [top_digits] those of a [u64] with no zero in front
    ([top_digits_correct]). *)

From Stdlib Require Import ZArith Lia List.
From Flocq Require Import Core.Core.
From Fushimi Require Import Model Limbs NatOps NatDigits NatDivTen19.

Open Scope Z_scope.

(** ** [div_rem_ten19] *)

(** The [for] loop of [div_rem_ten19], from the top limb down: a quotient
    limb for each limb, as each remainder is below [10 ^ 19], and the last
    remainder. *)
Lemma div_rem_ten19_from_correct :
  forall x, limbs_ok x ->
  exists qs r, NatLimbs.div_rem_ten19_from x = Some (qs, r) /\ limbs_ok qs /\
  length qs = length x /\ Limbs.val x = Limbs.val qs * 10 ^ 19 + r /\ 0 <= r < 10 ^ 19.
Proof.
induction x as [|l x IH]; intros H.
- exists nil, 0. split; [reflexivity|]. split; [constructor|]. split; [reflexivity|].
  split; [cbn [Limbs.val]; lia | lia].
- apply limbs_ok_cons in H as [Hl Hx].
  destruct (IH Hx) as (qs & r & E & Hqs & Hlen & Hv & Hr).
  cbn [NatLimbs.div_rem_ten19_from]. rewrite E. cbv beta iota.
  rewrite (div_ten19_correct r l Hr Hl).
  pose proof (Z.div_mod (r * 2 ^ 64 + l) (10 ^ 19) ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (r * 2 ^ 64 + l) (10 ^ 19) ltac:(lia)) as B.
  (* [r < 10 ^ 19], so [(r 2 ^ 64 + l) / 10 ^ 19 < 2 ^ 64]. *)
  assert (Hq : 0 <= (r * 2 ^ 64 + l) / 10 ^ 19 < 2 ^ 64).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  exists ((r * 2 ^ 64 + l) / 10 ^ 19 :: qs), ((r * 2 ^ 64 + l) mod 10 ^ 19).
  split; [reflexivity|]. split; [apply limbs_ok_cons; split; assumption|].
  split; [cbn [length]; lia|]. split; [|exact B].
  cbn [Limbs.val]. rewrite Hv. lia.
Qed.

(** The [pop] of [div_rem_ten19]: limbs [q] that hold at least
    [2 ^ (64 (n - 2))] for their length [n >= 2] have at most their top limb
    0, and the [pop] of a zero limb at the top leaves none. *)
Lemma pop_top_zero :
  forall q, limbs_ok q ->
  ((2 <= length q)%nat -> 2 ^ (64 * Z.of_nat (length q - 2)) <= Limbs.val q) ->
  nat_ok (match q with nil => nil | _ => if last q 0 =? 0 then removelast q else q end) /\
  Limbs.val (match q with nil => nil | _ => if last q 0 =? 0 then removelast q else q end) =
  Limbs.val q.
Proof.
intros q Hq Hb. destruct q as [|b q0]; [split; [exact nat_ok_nil | reflexivity]|].
cbv beta iota.
assert (Hne : b :: q0 <> nil) by discriminate.
destruct (exists_last Hne) as (q' & a & Eq). rewrite Eq in Hq, Hb |- *.
rewrite last_last, removelast_last.
rewrite length_app, val_app in Hb. cbn [length Limbs.val] in Hb.
apply limbs_ok_app_inv in Hq as [Hq' Ha]. apply limbs_ok_cons in Ha as [Ha _].
destruct (Z.eqb_spec a 0) as [-> | Ha0]; cbv beta iota.
- split; [| rewrite val_app; cbn [Limbs.val]; lia].
  destruct q' as [|b' q'']; [exact nat_ok_nil|].
  apply (proj2 (nat_ok_iff_val (b' :: q'') Hq' ltac:(discriminate))).
  assert (H2 : (2 <= length (b' :: q'') + 1)%nat) by (cbn [length]; lia).
  specialize (Hb H2).
  replace (length (b' :: q'') + 1 - 2)%nat with (length (b' :: q'') - 1)%nat in Hb by lia.
  lia.
- split; [| reflexivity].
  split; [apply limbs_ok_app; [exact Hq' | apply limbs_ok_cons; split; [exact Ha | constructor]]|].
  right. unfold Limbs.limb. rewrite length_app. cbn [length].
  replace (length q' + 1 - 1)%nat with (length q') by lia.
  rewrite nth_middle. exact Ha0.
Qed.

Theorem div_rem_ten19_correct :
  forall x, nat_ok x ->
  exists q r, NatLimbs.div_rem_ten19 x = Some (q, r) /\ nat_ok q /\
  Limbs.val q = Limbs.val x / 10 ^ 19 /\ r = Limbs.val x mod 10 ^ 19.
Proof.
intros x Hx.
destruct (div_rem_ten19_from_correct x (proj1 Hx)) as (qs & r & E & Hqs & Hlen & Hv & Hr).
unfold NatLimbs.div_rem_ten19. rewrite E. cbv beta iota.
assert (Vq : Limbs.val qs = Limbs.val x / 10 ^ 19).
{ rewrite Hv, Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
assert (Vr : r = Limbs.val x mod 10 ^ 19).
{ rewrite Hv, Z.add_comm, Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity. }
destruct (pop_top_zero qs Hqs) as [Ok Vp].
{ (* [x >= 2 ^ (64 (n - 1))] for its [n >= 2] limbs, and [2 ^ 64 > 10 ^ 19]. *)
  intros H2. rewrite Hlen in H2 |- *. rewrite Vq.
  assert (Hne : x <> nil) by (intros ->; cbn in H2; lia).
  pose proof (proj1 (nat_ok_iff_val x (proj1 Hx) Hne) Hx) as Hb.
  replace (64 * Z.of_nat (length x - 1)) with (64 * Z.of_nat (length x - 2) + 64) in Hb by lia.
  rewrite Z.pow_add_r in Hb by lia.
  pose proof (Z.pow_pos_nonneg 2 (64 * Z.of_nat (length x - 2)) ltac:(lia) ltac:(lia)).
  apply Z.div_le_lower_bound; lia. }
eexists. exists r. split; [reflexivity|].
split; [exact Ok|]. split; [lia | exact Vr].
Qed.

(** ** [write_digits] *)

(** [DEC_PAIRS[i]] spells [i < 100] with two digits. *)
Lemma dec_pair_correct :
  forall i, 0 <= i < 100 ->
  length (NatLimbs.dec_pair i) = 2%nat /\ Forall dec_digit (NatLimbs.dec_pair i) /\
  digits_val 10 (NatLimbs.dec_pair i) = i.
Proof.
intros i Hi. unfold NatLimbs.dec_pair.
pose proof (Z.div_mod i 10 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound i 10 ltac:(lia)) as B.
assert (Q : 0 <= i / 10 < 10) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
split; [reflexivity|]. split.
- constructor; [unfold dec_digit; lia|]. constructor; [unfold dec_digit; lia|]. constructor.
- unfold digits_val, digit_value. cbn [fold_left].
  destruct (Z.leb_spec (48 + i / 10) 57); [|lia].
  destruct (Z.leb_spec (48 + i mod 10) 57); [|lia].
  cbv beta iota. lia.
Qed.

(** The digit [d < 10] spells [d]. *)
Lemma digits_val_digit : forall d, 0 <= d < 10 -> digits_val 10 (48 + d :: nil) = d.
Proof.
intros d Hd. unfold digits_val, digit_value. cbn [fold_left].
destruct (Z.leb_spec (48 + d) 57); [|lia]. cbv beta iota. lia.
Qed.

(** [k] passes of the [for] loop of [write_digits] write the last [2 k]
    digits of [c] and leave [c / 100 ^ k]. *)
Lemma write_pairs_correct :
  forall k c, 0 <= c ->
  exists w, NatLimbs.write_pairs k c = (w, c / 100 ^ Z.of_nat k) /\
  length w = (2 * k)%nat /\ Forall dec_digit w /\ digits_val 10 w = c mod 100 ^ Z.of_nat k.
Proof.
induction k as [|k IH]; intros c Hc.
- exists nil. cbn [NatLimbs.write_pairs]. change (100 ^ Z.of_nat 0) with 1.
  rewrite Z.div_1_r, Z.mod_1_r. split; [reflexivity|]. split; [reflexivity|].
  split; [constructor | reflexivity].
- assert (Hc' : 0 <= c / 100) by (apply Z.div_pos; lia).
  destruct (IH (c / 100) Hc') as (w & E & Hl & Hf & Hv).
  cbn [NatLimbs.write_pairs]. rewrite E.
  destruct (dec_pair_correct (c mod 100) (Z.mod_pos_bound c 100 ltac:(lia))) as (Pl & Pf & Pv).
  pose proof (Z.pow_pos_nonneg 100 (Z.of_nat k) ltac:(lia) ltac:(lia)) as P.
  assert (E100 : 100 ^ Z.of_nat (S k) = 100 * 100 ^ Z.of_nat k)
    by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity).
  exists (w ++ NatLimbs.dec_pair (c mod 100)). rewrite E100.
  split; [rewrite Z.div_div by lia; reflexivity|].
  split; [rewrite length_app, Pl, Hl; lia|].
  split; [apply Forall_app; split; assumption|].
  (* [c mod 100 ^ (k + 1) = c mod 100 + 100 ((c / 100) mod 100 ^ k)] *)
  rewrite digits_val_app, Pl, Hv, Pv, Z.rem_mul_r by lia.
  change (10 ^ Z.of_nat 2) with 100. lia.
Qed.

Lemma write_digits_correct :
  forall n c, 0 <= c < 10 ^ Z.of_nat n ->
  exists t, NatLimbs.write_digits n c = Some t /\ length t = n /\
  Forall dec_digit t /\ digits_val 10 t = c.
Proof.
intros n c Hc. unfold NatLimbs.write_digits.
destruct (write_pairs_correct (n / 2) c (proj1 Hc)) as (w & E & Hl & Hf & Hv).
rewrite E. cbv beta iota.
pose proof (Nat.div_mod_eq n 2) as En.
pose proof (Nat.mod_upper_bound n 2 ltac:(lia)) as Bn.
assert (Ek : 100 ^ Z.of_nat (n / 2) = 10 ^ (2 * Z.of_nat (n / 2))).
{ rewrite Z.pow_mul_r by lia. reflexivity. }
assert (Ew : 10 ^ Z.of_nat (length w) = 100 ^ Z.of_nat (n / 2)).
{ rewrite Hl, Nat2Z.inj_mul, Ek. reflexivity. }
pose proof (Z.pow_pos_nonneg 100 (Z.of_nat (n / 2)) ltac:(lia) ltac:(lia)) as P.
pose proof (Z.div_mod c (100 ^ Z.of_nat (n / 2)) ltac:(lia)) as D.
destruct (Nat.eqb_spec (n mod 2) 1) as [Ho | Ho].
- (* An odd [n]: the first digit is [c / 100 ^ (n / 2) < 10]. *)
  assert (Hn : Z.of_nat n = 2 * Z.of_nat (n / 2) + 1) by lia.
  rewrite Hn, Z.pow_add_r, <- Ek in Hc by lia.
  assert (Hd : 0 <= c / 100 ^ Z.of_nat (n / 2) < 10).
  { split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  destruct (Z.ltb_spec (c / 100 ^ Z.of_nat (n / 2)) 10); [|lia].
  rewrite Z.mod_small by lia. rewrite checked_u_some by lia.
  exists (48 + c / 100 ^ Z.of_nat (n / 2) :: w).
  split; [reflexivity|]. split; [cbn [length]; lia|].
  split; [constructor; [unfold dec_digit; lia | exact Hf]|].
  change (48 + c / 100 ^ Z.of_nat (n / 2) :: w)
    with ((48 + c / 100 ^ Z.of_nat (n / 2) :: nil) ++ w).
  rewrite digits_val_app, (digits_val_digit _ Hd), Ew, Hv. lia.
- (* An even [n]: [c < 100 ^ (n / 2)]. *)
  assert (Hn : Z.of_nat n = 2 * Z.of_nat (n / 2)) by lia.
  rewrite Hn, <- Ek in Hc.
  exists w. split; [reflexivity|]. split; [lia|]. split; [exact Hf|].
  rewrite Hv. apply Z.mod_small. lia.
Qed.

(** ** [top_digits] *)

(** [c | 1] is [c] for an odd [c] and [c + 1] for an even one. *)
Lemma lor_1 : forall c, 0 <= c -> Z.lor c 1 = 2 * (c / 2) + 1.
Proof.
intros c Hc. pose proof (Z.div_mod c 2 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound c 2 ltac:(lia)) as B.
apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
destruct (Z.eq_dec i 0) as [-> | Hi0].
- rewrite Z.testbit_odd_0. apply Bool.orb_true_r.
- replace i with (Z.succ (Z.pred i)) by lia.
  assert (Tc : Z.testbit c (Z.succ (Z.pred i)) = Z.testbit (c / 2) (Z.pred i)).
  { destruct (Z.eq_dec (c mod 2) 0) as [E0 | E1].
    - assert (Ec : c = 2 * (c / 2)) by lia. rewrite Ec at 1.
      apply Z.testbit_even_succ. lia.
    - assert (Ec : c = 2 * (c / 2) + 1) by lia. rewrite Ec at 1.
      apply Z.testbit_odd_succ. lia. }
  assert (T1 : Z.testbit 1 (Z.succ (Z.pred i)) = false).
  { change 1 with (2 * 0 + 1) at 1. rewrite Z.testbit_odd_succ by lia. apply Z.testbit_0_l. }
  rewrite Tc, T1, Z.testbit_odd_succ by lia. apply Bool.orb_false_r.
Qed.

Lemma skipn_repeat_app : forall k (w : list Z), skipn k (repeat 0 k ++ w) = w.
Proof. induction k as [|k IH]; intros w; [reflexivity | exact (IH w)]. Qed.

Lemma top_digits_correct :
  forall c, 0 <= c < 2 ^ 64 ->
  exists t n, NatLimbs.top_digits c = Some (t, n) /\
  Forall dec_digit (skipn (20 - n) t) /\ digits_val 10 (skipn (20 - n) t) = c /\
  (skipn (20 - n) t = 48 :: nil \/ exists d t', skipn (20 - n) t = d :: t' /\ d <> 48).
Proof.
intros c Hc.
destruct (Z.eq_dec c 0) as [-> | Hc0].
{ exists (repeat 0 19 ++ 48 :: nil), 1%nat. split; [vm_compute; reflexivity|].
  change (skipn (20 - 1) (repeat 0 19 ++ 48 :: nil)) with (48 :: nil).
  split; [constructor; [unfold dec_digit; lia | constructor]|].
  split; [reflexivity | left; reflexivity]. }
pose proof (lor_1 c (proj1 Hc)) as L.
pose proof (Z.div_mod c 2 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound c 2 ltac:(lia)) as B.
(* [c | 1] has [k] digits, [1 <= k <= 20], as [c | 1 <= 2 ^ 64 - 1 < 10 ^ 20]. *)
pose proof (Zdigits_correct radix10 (Z.lor c 1)) as Z1.
pose proof (Zdigits_gt_0 radix10 (Z.lor c 1) ltac:(lia)) as Z2.
change (radix_val radix10) with 10 in Z1.
rewrite Z.abs_eq in Z1 by lia.
assert (Z3 : Zdigits radix10 (Z.lor c 1) <= 20).
{ apply Zdigits_le_Zpower. change (radix_val radix10) with 10. rewrite Z.abs_eq by lia. lia. }
(* [c] has [k] digits too: [c <= c | 1], and for an even [c], [c + 1] is
   odd, so it is not [10 ^ (k - 1)] for [k >= 2]. *)
assert (Hlo : 10 ^ (Zdigits radix10 (Z.lor c 1) - 1) <= c).
{ destruct (Z.eq_dec (Zdigits radix10 (Z.lor c 1)) 1) as [E1 | E1].
  - rewrite E1. change (10 ^ (1 - 1)) with 1. lia.
  - replace (Zdigits radix10 (Z.lor c 1) - 1) with (Z.succ (Zdigits radix10 (Z.lor c 1) - 2))
      in Z1 |- * by lia.
    rewrite Z.pow_succ_r in Z1 |- * by lia.
    pose proof (Z.pow_nonneg 10 (Zdigits radix10 (Z.lor c 1) - 2) ltac:(lia)). lia. }
assert (Eil : ilog10 (Z.lor c 1) = Some (Zdigits radix10 (Z.lor c 1) - 1)).
{ unfold ilog10. destruct (Z.eqb_spec (Z.lor c 1) 0); [lia | reflexivity]. }
unfold NatLimbs.top_digits. rewrite Eil. cbv beta iota zeta.
assert (Hn : Z.of_nat (Z.to_nat (Zdigits radix10 (Z.lor c 1) - 1 + 1)) =
  Zdigits radix10 (Z.lor c 1)) by (rewrite Z2Nat.id; lia).
assert (Hc' : 0 <= c < 10 ^ Z.of_nat (Z.to_nat (Zdigits radix10 (Z.lor c 1) - 1 + 1)))
  by (rewrite Hn; lia).
destruct (write_digits_correct _ c Hc') as (w & Ew & Lw & Fw & Vw).
rewrite Ew.
exists (repeat 0 (20 - Z.to_nat (Zdigits radix10 (Z.lor c 1) - 1 + 1)) ++ w),
  (Z.to_nat (Zdigits radix10 (Z.lor c 1) - 1 + 1)).
rewrite skipn_repeat_app.
split; [reflexivity|]. split; [exact Fw|]. split; [exact Vw|].
right. destruct w as [|d w']; [cbn [length] in Lw; lia|].
exists d, w'. split; [reflexivity|]. intros Ed. subst d.
(* A 0 in front leaves [k - 1] digits, which spell less than [10 ^ (k - 1) <= c]. *)
apply Forall_cons_iff in Fw as [_ Fw'].
pose proof (digits_val_dec_bounds w' Fw') as Bw.
change (48 :: w') with ((48 :: nil) ++ w') in Vw.
rewrite digits_val_app in Vw. change (digits_val 10 (48 :: nil)) with 0 in Vw.
rewrite <- Lw in Hn. cbn [length] in Hn.
assert (El : Z.of_nat (length w') = Zdigits radix10 (Z.lor c 1) - 1) by lia.
rewrite El in Bw, Vw. lia.
Qed.

(** ** [to_dec] *)

(** The number that the chunks [cs] of 19 digits spell, the top one first. *)
Fixpoint chunks_val (cs : list Z) : Z :=
  match cs with
  | nil => 0
  | c :: cs' => c * 10 ^ (19 * Z.of_nat (length cs')) + chunks_val cs'
  end.

(** The [for] loop of [to_dec] over the chunks appends their digits. *)
Lemma to_dec_chunks_correct :
  forall cs s, Forall (fun c => 0 <= c < 10 ^ 19) cs ->
  exists d, NatLimbs.to_dec_chunks cs s = Some (s ++ d) /\
  length d = (19 * length cs)%nat /\ Forall dec_digit d /\ digits_val 10 d = chunks_val cs.
Proof.
induction cs as [|c cs IH]; intros s H.
- exists nil. rewrite app_nil_r. split; [reflexivity|]. split; [reflexivity|].
  split; [constructor | reflexivity].
- apply Forall_cons_iff in H as [Hc H].
  destruct (write_digits_correct 19 c Hc) as (w & Ew & Lw & Fw & Vw).
  destruct (IH (s ++ w) H) as (d & Ed & Ld & Fd & Vd).
  exists (w ++ d). split.
  + cbn [NatLimbs.to_dec_chunks]. rewrite Ew. cbv beta iota. rewrite Ed, app_assoc.
    reflexivity.
  + split; [rewrite length_app, Lw, Ld; cbn [length]; lia|].
    split; [apply Forall_app; split; assumption|].
    rewrite digits_val_app, Vw, Vd, Ld, Nat2Z.inj_mul. reflexivity.
Qed.

(** The [while] loop of [to_dec], with fuel [f >= 1] for [x < 2 ^ (64 + 63 (f - 1))]:
    each pass divides by [10 ^ 19 > 2 ^ 63], and [x < 2 ^ 64] has one limb.
    A quotient of [x >= 2 ^ 64] is at least 1, so the limb [top] that is
    left is not 0. *)
Lemma to_dec_loop_correct :
  forall f x chunks,
  nat_ok x -> x <> nil -> (1 <= f)%nat ->
  Limbs.val x < 2 ^ (64 + 63 * (Z.of_nat f - 1)) ->
  Forall (fun c => 0 <= c < 10 ^ 19) chunks ->
  exists top cs, NatLimbs.to_dec_loop f x chunks = Some (top, cs) /\
  0 < top < 2 ^ 64 /\ Forall (fun c => 0 <= c < 10 ^ 19) cs /\
  top * 10 ^ (19 * Z.of_nat (length cs)) + chunks_val cs =
  Limbs.val x * 10 ^ (19 * Z.of_nat (length chunks)) + chunks_val chunks.
Proof.
induction f as [|f IH]; intros x chunks Hx Hne Hf Hb Hc; [lia|].
cbn [NatLimbs.to_dec_loop].
destruct (Nat.ltb_spec 1 (length x)) as [Hl | Hl].
- destruct (div_rem_ten19_correct x Hx) as (q & r & E & Hq & Vq & Er).
  rewrite E.
  pose proof (proj1 (nat_ok_iff_val x (proj1 Hx) Hne) Hx) as Hlo.
  assert (H64 : 2 ^ 64 <= Limbs.val x).
  { eapply Z.le_trans; [|exact Hlo]. apply Z.pow_le_mono_r; lia. }
  assert (Hf' : (1 <= f)%nat).
  { destruct (Nat.eq_dec f 0) as [-> | ?]; [|lia].
    replace (64 + 63 * (Z.of_nat 1 - 1)) with 64 in Hb by lia. lia. }
  assert (Hq0 : q <> nil).
  { intros ->. cbn [Limbs.val] in Vq.
    pose proof (Z.div_le_lower_bound (Limbs.val x) (10 ^ 19) 1 ltac:(lia) ltac:(lia)). lia. }
  assert (Hbq : Limbs.val q < 2 ^ (64 + 63 * (Z.of_nat f - 1))).
  { rewrite Vq. apply Z.div_lt_upper_bound; [lia|].
    replace (64 + 63 * (Z.of_nat (S f) - 1)) with (64 + 63 * (Z.of_nat f - 1) + 63)
      in Hb by lia.
    rewrite Z.pow_add_r in Hb by lia.
    pose proof (Z.pow_pos_nonneg 2 (64 + 63 * (Z.of_nat f - 1)) ltac:(lia) ltac:(lia)).
    lia. }
  assert (Hc' : Forall (fun c => 0 <= c < 10 ^ 19) (r :: chunks)).
  { constructor; [rewrite Er; apply Z.mod_pos_bound; lia | exact Hc]. }
  destruct (IH q (r :: chunks) Hq Hq0 Hf' Hbq Hc') as (top & cs & E' & Ht & Hcs & Hv).
  exists top, cs. split; [exact E'|]. split; [exact Ht|]. split; [exact Hcs|].
  rewrite Hv. cbn [length chunks_val]. rewrite Nat2Z.inj_succ.
  replace (19 * Z.succ (Z.of_nat (length chunks))) with (19 * Z.of_nat (length chunks) + 19)
    by lia.
  rewrite Z.pow_add_r by lia. rewrite Vq, Er.
  transitivity ((10 ^ 19 * (Limbs.val x / 10 ^ 19) + Limbs.val x mod 10 ^ 19) *
    10 ^ (19 * Z.of_nat (length chunks)) + chunks_val chunks); [ring|].
  rewrite <- (Z.div_mod (Limbs.val x) (10 ^ 19)) by lia. reflexivity.
- destruct x as [|l [|l2 x']]; [exfalso; exact (Hne eq_refl) | | cbn [length] in Hl; lia].
  apply nat_ok_cons in Hx as (Hl0 & _ & Hz). specialize (Hz eq_refl).
  exists l, chunks. split; [reflexivity|]. split; [lia|]. split; [exact Hc|].
  cbn [Limbs.val]. ring.
Qed.

(** [String::from_utf8] of ASCII digits. *)
Lemma from_utf8_digits : forall s, Forall dec_digit s -> NatLimbs.from_utf8 s = Some s.
Proof.
intros s H. unfold NatLimbs.from_utf8.
replace (forallb (fun b => b <? 128) s) with true; [reflexivity|].
symmetry. apply forallb_forall. intros b Hb.
rewrite Forall_forall in H. specialize (H b Hb). unfold dec_digit in H.
apply Z.ltb_lt. lia.
Qed.

(** What [to_dec] does after the loop: [top_digits] of [top > 0], with no
    zero in front, then the digits of the chunks. *)
Lemma to_dec_tail :
  forall top cs, 0 < top < 2 ^ 64 -> Forall (fun c => 0 <= c < 10 ^ 19) cs ->
  exists w n t, NatLimbs.top_digits top = Some (w, n) /\
  NatLimbs.to_dec_chunks cs (skipn (20 - n) w) = Some t /\ NatLimbs.from_utf8 t = Some t /\
  Forall dec_digit t /\ digits_val 10 t = top * 10 ^ (19 * Z.of_nat (length cs)) + chunks_val cs /\
  exists c t', t = c :: t' /\ c <> 48.
Proof.
intros top cs Ht Hcs.
destruct (top_digits_correct top ltac:(lia)) as (w & n & Ew & Fw & Vw & Hw).
destruct (to_dec_chunks_correct cs (skipn (20 - n) w) Hcs) as (d & Ed & Ld & Fd & Vd).
assert (F : Forall dec_digit (skipn (20 - n) w ++ d)) by (apply Forall_app; split; assumption).
exists w, n, (skipn (20 - n) w ++ d).
split; [exact Ew|]. split; [exact Ed|]. split; [apply from_utf8_digits; exact F|].
split; [exact F|]. split.
- rewrite digits_val_app, Vw, Vd, Ld, Nat2Z.inj_mul. reflexivity.
- destruct Hw as [E1 | (c & t' & E1 & Hc)].
  + exfalso. rewrite E1 in Vw. change (digits_val 10 (48 :: nil)) with 0 in Vw. lia.
  + rewrite E1. exists c, (t' ++ d). split; [reflexivity | exact Hc].
Qed.

(** [x.to_dec()] for the [Nat] [x] that holds [a]: its digits, with no
    zero in front unless it is [0]. *)
Theorem to_dec_correct :
  forall a, 0 <= a ->
  exists t, NatLimbs.to_dec (NatLimbs.to_limbs a) = Some t /\
  Forall dec_digit t /\ digits_val 10 t = a /\
  (t = 48 :: nil \/ exists c t', t = c :: t' /\ c <> 48).
Proof.
intros a Ha.
destruct (to_limbs_correct a Ha) as [Hok Hv].
revert Hok Hv. generalize (NatLimbs.to_limbs a). intros x Hok Hv.
destruct x as [|l [|l2 x]].
- (* [a = 0] *)
  exists (48 :: nil). cbn [Limbs.val] in Hv. subst a.
  split; [reflexivity|]. split; [constructor; [unfold dec_digit; lia | constructor]|].
  split; [reflexivity | left; reflexivity].
- (* One limb, which is [top]. *)
  apply nat_ok_cons in Hok as (Hl & _ & Hz). specialize (Hz eq_refl).
  cbn [Limbs.val] in Hv.
  destruct (to_dec_tail l nil ltac:(lia) ltac:(constructor))
    as (w & n & t & E1 & E2 & E3 & F & V & H).
  exists t. unfold NatLimbs.to_dec. cbv beta iota.
  rewrite E1. cbv beta iota. rewrite E2. cbv beta iota. rewrite E3.
  split; [reflexivity|]. split; [exact F|]. split; [|right; exact H].
  rewrite V. change (10 ^ (19 * Z.of_nat (length (@nil Z)))) with 1. cbn [chunks_val]. lia.
- (* Two limbs or more: [x < 2 ^ (64 n) <= 2 ^ (64 + 63 (2 n - 1))] for the
     fuel [2 n] of the loop. *)
  assert (Hb : Limbs.val (l :: l2 :: x) <
    2 ^ (64 + 63 * (Z.of_nat (2 * length (l :: l2 :: x)) - 1))).
  { eapply Z.lt_le_trans; [exact (proj2 (val_bounds _ (proj1 Hok)))|].
    apply Z.pow_le_mono_r; lia. }
  destruct (to_dec_loop_correct (2 * length (l :: l2 :: x)) (l :: l2 :: x) nil Hok
    ltac:(discriminate) ltac:(cbn [length]; lia) Hb ltac:(constructor))
    as (top & cs & E & Ht & Hcs & Hv').
  destruct (to_dec_tail top cs Ht Hcs) as (w & n & t & E1 & E2 & E3 & F & V & H).
  exists t. unfold NatLimbs.to_dec. cbv beta iota.
  rewrite E. cbv beta iota. rewrite E1. cbv beta iota. rewrite E2. cbv beta iota. rewrite E3.
  split; [reflexivity|]. split; [exact F|]. split; [|right; exact H].
  rewrite V, Hv'. change (10 ^ (19 * Z.of_nat (length (@nil Z)))) with 1.
  cbn [chunks_val]. lia.
Qed.
