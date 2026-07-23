Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.

(** Compatibility model for the portion of OCaml's [Uchar] interface exposed
    by [Stdlib.String].

    OCaml deliberately keeps [utf_decode] abstract: its concrete integer
    encoding is a runtime implementation detail.  The Monad VM never inspects
    values of this type, so the Gallina model keeps the carrier abstract too. *)
Parameter utf_decode : Set.
