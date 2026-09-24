(** Generic immutable-array bounds lemmas.  They establish when translated
    operations return before consulting their [Unreachable] fallback. *)

From Stdlib Require Import ZArith Lia List.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.OCamlIarray.

Local Open Scope Z_scope.

Lemma iarray_get_in_bounds {A : Set} `{Unreachable A}
    (values : list A) (index : Z) (value : A) :
  0 <= index ->
  List.nth_error values (Z.to_nat index) = Some value ->
  OCamlIarray.get values index = value.
Proof.
  intros Hindex Hvalue.
  unfold OCamlIarray.get.
  destruct (index <? 0) eqn:Hnegative.
  - apply Z.ltb_lt in Hnegative; lia.
  - now rewrite Hvalue.
Qed.

Lemma iarray_get_fallback_irrelevant {A : Set}
    (first second : Unreachable A) (values : list A) (index : Z) (value : A) :
  0 <= index ->
  List.nth_error values (Z.to_nat index) = Some value ->
  @OCamlIarray.get A first values index =
  @OCamlIarray.get A second values index.
Proof.
  intros Hindex Hvalue.
  rewrite (iarray_get_in_bounds (H := first) values index value Hindex Hvalue).
  rewrite (iarray_get_in_bounds (H := second) values index value Hindex Hvalue).
  reflexivity.
Qed.

(** An in-bounds child has smaller weight than a node containing the array. *)
Lemma list_element_weight_lt {A : Set} (weight : A -> nat)
    (values : list A) (index : nat) (value : A) :
  nth_error values index = Some value ->
  (weight value < S (List.fold_right (fun value total => weight value + total) 0 values))%nat.
Proof.
  revert index.
  induction values as [|head tail IH]; intros [|index] Hget;
    cbn in Hget; try discriminate.
  - inversion Hget; subst; cbn; lia.
  - specialize (IH index Hget); cbn; lia.
Qed.

Lemma iarray_get_weight_lt {A : Set}
    `{RocqOfOCaml.Basics.Unreachable A}
    (weight : A -> nat) (values : list A) (index : Z) :
  0 <= index -> index < OCamlIarray.length values ->
  (weight (OCamlIarray.get values index) <
   S (List.fold_right (fun value total => weight value + total) 0 values))%nat.
Proof.
  intros Hindex Hbound.
  destruct (nth_error values (Z.to_nat index)) as [value|] eqn:Hget.
  - rewrite (iarray_get_in_bounds values index value Hindex Hget).
    eapply list_element_weight_lt; exact Hget.
  - apply nth_error_None in Hget.
    unfold OCamlIarray.length in Hbound; lia.
Qed.
