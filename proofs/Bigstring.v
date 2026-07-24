Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.

(** [Bigstring.t] is a mutable C-backed bigarray in OCaml.  The translated VM
    only constructs values for cryptographic FFI calls and reads returned
    values through [OCamlBigarray.Array1.get], which is modeled separately.
    A string carrier preserves the byte-oriented interface without claiming
    to model allocation, mutation, or aliasing. *)
Definition t : Set := string.

Parameter init : int -> (int -> ascii) -> t.

Definition of_string (value : string) : t := value.
