(** Reusable facts for ranking recursion by a nonnegative integer
    expression. *)

From Stdlib Require Import ZArith Lia.

Local Open Scope Z_scope.

(** Negative values are clamped to zero.  A caller proves nonnegativity on
    every recursive edge before using [z_rank_strict]. *)
Definition z_rank (value : Z) : nat := Z.to_nat value.

Lemma z_rank_strict (next current : Z) :
  0 <= next ->
  next < current ->
  (z_rank next < z_rank current)%nat.
Proof.
  intros Hnext Hlt.
  unfold z_rank.
  assert (Hcurrent : 0 <= current) by lia.
  exact ((proj1 (Z2Nat.inj_lt next current Hnext Hcurrent)) Hlt).
Qed.

(** A clamped next rank may be negative.  It still decreases whenever the
    current integer rank is positive. *)
Lemma z_rank_strict_from_positive (next current : Z) :
  0 < current ->
  next < current ->
  (z_rank next < z_rank current)%nat.
Proof.
  intros Hcurrent Hlt.
  destruct (Z_lt_ge_dec next 0) as [Hnegative | Hnonnegative].
  - assert (Hnext_rank : Z.to_nat next = 0%nat).
    { destruct next; simpl in *; lia. }
    unfold z_rank.
    rewrite Hnext_rank.
    change (Z.to_nat 0 < Z.to_nat current)%nat.
    exact ((proj1 (Z2Nat.inj_lt 0 current ltac:(lia) ltac:(lia))) Hcurrent).
  - apply z_rank_strict; lia.
Qed.
