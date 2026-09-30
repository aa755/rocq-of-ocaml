From Stdlib Require Import Ascii.
Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.Bigstring.
Require Import RocqOfOCaml.OCamlBigarray.

(** An axiom with this signature can be implemented by a closed term.  This
    witnesses logical realisability, not agreement with native Bigarray
    reads.  The explicit application also guards against reinstating a
    polymorphic [get] that can inhabit arbitrary result types. *)
Definition bigarray_get_witness : Bigstring.t -> int -> ascii :=
  fun _ _ => Ascii.ascii_of_nat 0.

Definition bigarray_get_signature : Bigstring.t -> int -> ascii :=
  @OCamlBigarray.Array1.get.
