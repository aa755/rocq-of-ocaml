Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.OCamlMachineInt.
Require Import RocqOfOCaml.OCamlInt.

Module Width <: OCamlMachineInt.Width.
  Definition bits := 32%Z.
End Width.
Include OCamlMachineInt.Make Width.

Definition of_int : int -> t := repr.
(** Sign extension into a 63-bit [int] loses no bits for canonical inputs. *)
Definition to_int (value : t) : int := value.
Definition unsigned_to_int (value : t) : option int := Some (unsigned value).
