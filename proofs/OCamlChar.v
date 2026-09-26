Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.

Local Open Scope Z_scope.

(** Executable compatibility model for the [Stdlib.Char] operations used by
    the Monad VM.  OCaml chars and Gallina [ascii] values are both bytes. *)

Definition t : Set := ascii.

Definition code (character : t) : int :=
  Z.of_N (N_of_ascii character).

Definition unsafe_chr (value : int) : t :=
  ascii_of_N (Z.to_N (value mod 256)).

Definition chr `{Unreachable t} (value : int) : t :=
  if andb (Z.leb 0 value) (Z.ltb value 256) then
    unsafe_chr value
  else
    unreachable.

Definition equal : t -> t -> bool := Ascii.eqb.

Definition compare (left right : t) : int :=
  match N.compare (N_of_ascii left) (N_of_ascii right) with
  | Lt => -1
  | Eq => 0
  | Gt => 1
  end.

Definition lt (left right : t) : bool :=
  N.ltb (N_of_ascii left) (N_of_ascii right).

Definition le (left right : t) : bool :=
  N.leb (N_of_ascii left) (N_of_ascii right).

Definition gt (left right : t) : bool :=
  N.ltb (N_of_ascii right) (N_of_ascii left).

Definition ge (left right : t) : bool :=
  N.leb (N_of_ascii right) (N_of_ascii left).

Definition min (left right : t) : t :=
  if le left right then left else right.

Definition max (left right : t) : t :=
  if ge left right then left else right.
