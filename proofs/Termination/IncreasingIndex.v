(** Ranking lemmas for loops that advance an index toward a fixed upper
    bound. *)

From Stdlib Require Import ZArith Lia.
From RocqOfOCaml.Termination Require Import Common.

Local Open Scope Z_scope.

Definition increasing_index_rank (limit index : Z) : nat :=
  z_rank (limit - index).

Lemma increasing_index_positive_step_decreases
    (limit index step : Z) :
  index < limit ->
  0 < step ->
  (increasing_index_rank limit (index + step) <
   increasing_index_rank limit index)%nat.
Proof.
  intros Hindex Hstep.
  unfold increasing_index_rank.
  apply z_rank_strict_from_positive; lia.
Qed.
