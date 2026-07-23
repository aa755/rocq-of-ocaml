From Stdlib Require Import Numbers.DecimalString.
Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.

Definition to_string (value : Z) : string :=
  NilZero.string_of_int (Z.to_int value).

Definition of_string_opt (value : string) : option Z :=
  match NilZero.int_of_string value with
  | Some parsed => Some (Z.of_int parsed)
  | None => None
  end.

Definition of_string (value : string) : Z :=
  match of_string_opt value with
  | Some parsed => parsed
  | None => axiom
  end.

(** Zarith supports a printf-like formatting language.  Numeric formatting is
    currently used for JSON/debug rendering, not VM state transitions. *)
Parameter format : string -> Z -> string.
