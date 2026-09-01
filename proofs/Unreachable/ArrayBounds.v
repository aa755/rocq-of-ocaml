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
