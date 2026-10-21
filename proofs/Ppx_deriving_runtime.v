Require Import RocqOfOCaml.Libraries.

(** Types re-exported by [ppx_deriving_runtime] in generated OCaml code. *)
Definition string : Set := String.string.
Definition bool : Set := Datatypes.bool.
Definition op_andand : bool -> bool -> bool := andb.
