Require Import RocqOfOCaml.RocqOfOCaml.

Definition t : Set := nat.

Definition zero : t := O.

Definition succ (value : t) : t := S value.

Definition pred `{Unreachable t} (value : t) : t :=
  match value with
  | O => unreachable
  | S value => value
  end.

Definition to_int (value : t) : Z := Z.of_nat value.
