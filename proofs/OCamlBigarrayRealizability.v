From Stdlib Require Import Ascii String ZArith Lia.
Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.Bigstring.
Require Import RocqOfOCaml.OCamlBigarray.

(** [Array1.get] is executable and has the same typed exceptional branch as
    [OCamlString.get].  In-range reads reduce to the byte at that index. *)
Lemma bigarray_get_is_string_get `{Unreachable ascii}
    (value : Bigstring.t) (index : int) :
  OCamlBigarray.Array1.get value index = OCamlString.get value index.
Proof. reflexivity. Qed.

Print Assumptions bigarray_get_is_string_get.

Lemma in_bounds_string_get_exists (value : string) (index : nat) :
  (index < Strings.String.length value)%nat ->
  exists character, Strings.String.get index value = Some character.
Proof.
  revert index.
  induction value as [|character rest IH]; intros [|index] bounded;
    cbn in *; try lia.
  - eexists. reflexivity.
  - apply IH. lia.
Qed.

Lemma bigarray_get_in_bounds_fallback_irrelevant
    (left right : Unreachable ascii)
    (value : Bigstring.t) (index : int) :
  (0 <= index < OCamlString.length value)%Z ->
  @OCamlBigarray.Array1.get left value index =
    @OCamlBigarray.Array1.get right value index.
Proof.
  intro bounded.
  unfold OCamlBigarray.Array1.get, OCamlString.get.
  assert (index <? 0 = false)%Z as nonnegative.
  { apply Z.ltb_ge. lia. }
  rewrite nonnegative.
  destruct (Strings.String.get (Z.to_nat index) value)
    as [character|] eqn:chosen; [reflexivity|].
  destruct (in_bounds_string_get_exists value (Z.to_nat index))
    as [character exists_at_index].
  { unfold OCamlString.length in bounded. lia. }
  rewrite chosen in exists_at_index. discriminate.
Qed.

Print Assumptions bigarray_get_in_bounds_fallback_irrelevant.
