Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.

Local Open Scope Z_scope.

Definition t : Set := int32.

Definition modulus : Z := 2 ^ 32.
Definition sign_bit : Z := 2 ^ 31.

Definition repr (value : Z) : t :=
  let unsigned := value mod modulus in
  if Z.leb sign_bit unsigned then unsigned - modulus else unsigned.

Definition of_int : int -> t := repr.

(** The Gallina compatibility type for OCaml [int] is unbounded [Z], so this
    conversion itself cannot overflow. *)
Definition to_int (value : t) : int := value.
