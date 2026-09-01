(** Ranking lemmas for positive integer loops that halve their argument. *)

From Stdlib Require Import ZArith Lia.
From RocqOfOCaml.Termination Require Import Common.

Local Open Scope Z_scope.

Definition binary_exponentiation_rank (exponent : Z) : nat :=
  z_rank exponent.

Lemma positive_halving_decreases (exponent : Z) :
  0 < exponent ->
  (binary_exponentiation_rank (exponent / 2) <
   binary_exponentiation_rank exponent)%nat.
Proof.
  intros Hexponent.
  unfold binary_exponentiation_rank.
  apply z_rank_strict.
  - apply Z.div_pos; lia.
  - apply Z.div_lt; lia.
Qed.
