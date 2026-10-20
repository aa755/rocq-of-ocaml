Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.OCamlMachineInt.
Require Import RocqOfOCaml.OCamlInt.
Require Import RocqOfOCaml.OCamlInt32.

Local Open Scope Z_scope.

(** Executable two's-complement arithmetic, with [Z] as the carrier. *)
Module Width <: OCamlMachineInt.Width.
  Definition bits := 64%Z.
End Width.
Include OCamlMachineInt.Make Width.

Definition of_int : int -> t := repr.
Definition to_int : t -> int := OCamlInt.repr.
Definition unsigned_to_int (value : t) : option int :=
  let value := unsigned value in
  if Z.leb value OCamlInt.max_int then Some value else None.

Definition of_int32 : int32 -> t := repr.
Definition to_int32 : t -> int32 := OCamlInt32.repr.
Definition of_nativeint : nativeint -> t := repr.
Definition to_nativeint (value : t) : nativeint := value.

(** Existing float compatibility approximations are not fixed by the
    machine-integer arithmetic model. They are outside its equivalence claim. *)
Definition of_float : float -> t := repr.
Definition to_float (value : t) : float := value.
Parameter bits_of_float : float -> t.
Parameter float_of_bits : t -> float.
Definition seeded_hash : int -> t -> int := OCamlHash.seeded_int64.
Definition hash : t -> int := seeded_hash 0.
