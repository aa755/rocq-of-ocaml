Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.

Local Open Scope Z_scope.

Definition t : Set := int.

Definition equal : t -> t -> bool := Z.eqb.

Definition compare (left right : t) : int :=
  match Z.compare left right with
  | Lt => -1
  | Eq => 0
  | Gt => 1
  end.

Definition shift_left (value count : int) : int :=
  Z.shiftl value count.

Definition shift_right_logical (value count : int) : int :=
  Z.shiftr value count.
