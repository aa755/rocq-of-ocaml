From Stdlib Require Import Ascii.
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
