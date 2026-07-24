Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.

(** Typed boundary for the subset of [digestif] used by the VM.

    Cryptographic correctness is not reimplemented here.  Each algorithm is
    an explicit parameter satisfying the OCaml module interface used by the
    translation. *)
Module S.
  Record signature : Set := {
    digest_string : option int -> option int -> string -> string;
    to_raw_string : string -> string;
  }.
End S.

Definition S := S.signature.

Parameter KECCAK_256 : S.
Parameter SHA256 : S.
Parameter RMD160 : S.
