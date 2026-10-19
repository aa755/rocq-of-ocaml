Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.OCamlMachineInt.
Require Import RocqOfOCaml.OCamlInt.
Require Import RocqOfOCaml.OCamlInt32.

(** The supported native word size is 64 bits, not the tagged [int] width. *)
Module Width <: OCamlMachineInt.Width.
  Definition bits := 64%Z.
End Width.
Include OCamlMachineInt.Make Width.

Definition of_int : int -> t := repr.
Definition to_int : t -> int := OCamlInt.repr.
Definition of_int32 : int32 -> t := repr.
Definition to_int32 : t -> int32 := OCamlInt32.repr.
Definition unsigned_to_int (value : t) : option int :=
  let value := unsigned value in
  if Z.leb value OCamlInt.max_int then Some value else None.
