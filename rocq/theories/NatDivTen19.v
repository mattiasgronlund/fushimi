(** * [div_ten19] of [src/nat.rs]

    [div_ten19] divides [u1 * 2 ^ 64 + u0] by [d = 10 ^ 19] with
    [u1 < d], by Algorithm 4 of Möller and Granlund, "Improved division by
    invariant integers", IEEE Transactions on Computers 60(2), 2011, with
    the reciprocal [v = floor((2 ^ 128 - 1) / d) - 2 ^ 64]. [d >= 2 ^ 63] is
    normalized. [div_ten19_correct] proves, for this [d], what the paper
    proves for every normalized [d]: the candidate quotient, which the code
    computes mod [2 ^ 64], is at most one away from the quotient, and the
    two corrections give the quotient and the remainder. The proof also
    covers a candidate of [2 ^ 64], which wraps to 0. It also shows that
    [q1 += 1] and [r -= d], which Rust checks for overflow in a debug build,
    do not overflow. *)

From Stdlib Require Import ZArith Lia.
From Fushimi Require Import Model Limbs.

Open Scope Z_scope.

(** A pair [(a, b)] with [u = a * d + b] and [0 <= b < d] is the
    quotient and the remainder of [u] by [d]. *)
Lemma div_ten19_div_mod :
  forall u d a b, 0 <= b < d -> u = a * d + b -> Some (a, b) = Some (u / d, u mod d).
Proof.
  intros u d a b Hb Hu.
  assert (Hu' : u = d * a + b) by (rewrite Hu; ring).
  rewrite <- (Z.div_unique u d a b (or_introl Hb) Hu').
  rewrite <- (Z.mod_unique u d a b (or_introl Hb) Hu').
  reflexivity.
Qed.

Lemma div_ten19_mod_shift : forall a b k n, n <> 0 -> a = b + k * n -> a mod n = b mod n.
Proof. intros a b k n Hn ->. apply Z.mod_add. exact Hn. Qed.

Theorem div_ten19_correct :
  forall u1 u0, 0 <= u1 < 10 ^ 19 -> 0 <= u0 < 2 ^ 64 ->
  NatLimbs.div_ten19 u1 u0 =
  Some ((u1 * 2 ^ 64 + u0) / 10 ^ 19, (u1 * 2 ^ 64 + u0) mod 10 ^ 19).
Proof.
  (* The paper's proof that Algorithm 4 is correct, for B = 2 ^ 64 and
     d = 10 ^ 19, with the constants as literals so that [lia] works
     on linear facts: k = V + B = floor((B ^ 2 - 1) / d)
     = 34028236692093846346, and e = B ^ 2 - 1 - k d
     = 3374607431768211455, with 0 <= e < d. *)
  intros u1 u0 H1 H0.
  unfold NatLimbs.div_ten19, NatLimbs.TEN19.
  assert (HV : NatLimbs.div_ten19_V = 15581492618384294730) by (vm_compute; reflexivity).
  rewrite HV. clear HV.
  (* [u1 << 64 | u0] is u = u1 B + u0. *)
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (u1 * 2 ^ 64)) by lia.
  rewrite lor_low by lia.
  remember (u1 * 2 ^ 64 + u0) as u eqn:Hu.
  (* q = V u1 + u = k u1 + u0 < B ^ 2, as u1 <= d - 1, k d <= B ^ 2 - 1
     and k >= B: the checked [u128] sum does not overflow. *)
  remember (15581492618384294730 * u1 + u) as q eqn:Hq.
  rewrite (checked_u_ok 128 q) by lia.
  cbv beta iota zeta.
  (* q = qh B + q0, with qh < B, so [as u64] keeps qh. *)
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod q (2 ^ 64) ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound q (2 ^ 64) ltac:(lia)) as Hq0b.
  remember (q / 2 ^ 64) as qh eqn:Hqh.
  remember (q mod 2 ^ 64) as q0 eqn:Hq0.
  assert (Hqhb : 0 <= qh < 2 ^ 64) by lia.
  rewrite (Z.mod_small qh) by lia.
  (* The candidate quotient c = qh + 1 is at most B; q1 is c mod B, which
     is 0 when c = B. *)
  remember ((qh + 1) mod 2 ^ 64) as q1 eqn:Hq1.
  assert (Hq1c : (qh + 1 < 2 ^ 64 /\ q1 = qh + 1) \/ (qh + 1 = 2 ^ 64 /\ q1 = 0)).
  { destruct (Z.lt_ge_cases (qh + 1) (2 ^ 64)).
    - left. split; [lia |]. rewrite Hq1. apply Z.mod_small. lia.
    - right. split; [lia |]. rewrite Hq1. replace (qh + 1) with (2 ^ 64) by lia.
      apply Z.mod_same. lia. }
  (* r is the candidate remainder rt = u - c d mod B, as u ≡ u0 mod B and
     q1 ≡ c mod B. *)
  remember ((u0 - (q1 * 10 ^ 19) mod 2 ^ 64) mod 2 ^ 64) as r eqn:Hr.
  remember (u - (qh + 1) * 10 ^ 19) as rt eqn:Hrt.
  assert (Hrm : r = rt mod 2 ^ 64).
  { rewrite Hr, Zminus_mod_idemp_r. symmetry.
    destruct Hq1c as [[_ Hc] | [Hc Hc']].
    - apply div_ten19_mod_shift with u1; lia.
    - apply div_ten19_mod_shift with (u1 - 10 ^ 19); lia. }
  clear Hr Hq1 Hqh Hq0.
  (* The paper's bounds on rt, from B rt = (1 + e) u1 + (B - d) u0
     + d (q0 - B) (a linear identity in u1, u0 and q0 here):
     max(B - d, q0) - B <= rt < max(B - d, q0), where rt > q0 - B as d < B. *)
  assert (Hlo : - 10 ^ 19 <= rt) by lia.
  assert (Hlo2 : q0 - 2 ^ 64 < rt) by lia.
  assert (Hhi : (q0 <= 2 ^ 64 - 10 ^ 19 -> rt < 2 ^ 64 - 10 ^ 19) /\
                (2 ^ 64 - 10 ^ 19 <= q0 -> rt < q0)) by lia.
  (* So -B < rt < B: r is rt + B when rt < 0, and rt otherwise. *)
  assert (Hrc : (rt < 0 /\ r = rt + 2 ^ 64) \/ (0 <= rt /\ r = rt)).
  { rewrite Hrm. destruct (Z.lt_ge_cases rt 0).
    - left. split; [lia |]. apply mod_add_once. lia.
    - right. split; [lia |]. apply Z.mod_small. lia. }
  clear Hrm.
  destruct (Z.ltb_spec q0 r) as [Hlt | Hge]; cbv beta iota.
  - (* r > q0: either rt < 0, or 0 <= rt and q0 < rt < B - d. Either way
       the first correction gives c - 1 = qh (undoing a wrap of c to 0)
       and rt + d, which is in [0, B), so it does not wrap. *)
    assert (E1 : (q1 - 1) mod 2 ^ 64 = qh).
    { destruct Hq1c as [[_ ->] | [Hc ->]].
      - replace (qh + 1 - 1) with qh by ring. apply Z.mod_small. lia.
      - rewrite mod_add_once by lia. lia. }
    assert (E2 : (r + 10 ^ 19) mod 2 ^ 64 = rt + 10 ^ 19).
    { destruct Hrc as [[Hn ->] | [Hp ->]].
      - rewrite mod_sub_once by lia. lia.
      - apply Z.mod_small. lia. }
    rewrite E1, E2.
    destruct (Z.leb_spec (10 ^ 19) (rt + 10 ^ 19)).
    + (* 0 <= rt < B - d < d: the quotient is c, which is below B as
         c d <= u < B d, and the remainder is rt. *)
      rewrite (checked_u_ok 64 (qh + 1)) by lia.
      rewrite (checked_u_ok 64 (rt + 10 ^ 19 - 10 ^ 19)) by lia.
      cbv beta iota. apply div_ten19_div_mod; lia.
    + (* rt < 0: the quotient is c - 1 and the remainder rt + d. *)
      apply div_ten19_div_mod; lia.
  - (* r <= q0: rt >= 0, as rt < 0 would give r = rt + B > q0. So r = rt,
       and c < B, as c d <= u < B d, so q1 = c. *)
    assert (Hp : 0 <= rt /\ r = rt) by lia.
    destruct Hp as [Hp ->].
    assert (Hq1e : q1 = qh + 1) by lia.
    rewrite Hq1e.
    destruct (Z.leb_spec (10 ^ 19) rt).
    + (* d <= rt < B < 2 d: the quotient is c + 1, below B as
         (c + 1) d <= u < B d, and the remainder rt - d. *)
      rewrite (checked_u_ok 64 (qh + 1 + 1)) by lia.
      rewrite (checked_u_ok 64 (rt - 10 ^ 19)) by lia.
      cbv beta iota. apply div_ten19_div_mod; lia.
    + (* 0 <= rt < d: the quotient is c and the remainder rt. *)
      apply div_ten19_div_mod; lia.
Qed.
