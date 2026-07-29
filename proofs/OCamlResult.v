Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.OCamlSeq.

Import ListNotations.
Local Open Scope Z_scope.

Definition t (a e : Set) : Set := sum a e.

Definition ok {a e : Set} (value : a) : t a e := inl value.
Definition _error {e a : Set} (error : e) : t a e := inr error.

Definition value {a e : Set} (result : t a e) (default : a) : a :=
  match result with inl value => value | inr _ => default end.

Definition get_ok {a e : Set} `{Unreachable a} (result : t a e) : a :=
  match result with inl value => value | inr _ => unreachable end.

Definition get_ok' {a : Set} `{Unreachable a}
    (result : t a string) : a := get_ok result.

Definition get_error {a e : Set} `{Unreachable e} (result : t a e) : e :=
  match result with inl _ => unreachable | inr error => error end.

Definition error_to_failure {a : Set} `{Unreachable a}
    (result : t a string) : a :=
  get_ok result.

Definition bind {a e b : Set}
    (result : t a e) (function_value : a -> t b e) : t b e :=
  match result with
  | inl value => function_value value
  | inr error => inr error
  end.

Definition join {a e : Set} (result : t (t a e) e) : t a e :=
  bind result (fun value => value).

Definition map {a b e : Set}
    (function_value : a -> b) (result : t a e) : t b e :=
  match result with
  | inl value => inl (function_value value)
  | inr error => inr error
  end.

Definition product {a e b : Set}
    (left : t a e) (right : t b e) : t (a * b) e :=
  match left, right with
  | inl left_value, inl right_value => inl (left_value, right_value)
  | inr error, _ | _, inr error => inr error
  end.

Definition map_error {e f a : Set}
    (function_value : e -> f) (result : t a e) : t a f :=
  match result with
  | inl value => inl value
  | inr error => inr (function_value error)
  end.

Definition fold {a c e : Set}
    (ok_value : a -> c) (error_value : e -> c) (result : t a e) : c :=
  match result with
  | inl value => ok_value value
  | inr error => error_value error
  end.

Definition retract {a : Set} (result : t a a) : a :=
  match result with inl value | inr value => value end.

Definition iter {a e : Set}
    (function_value : a -> unit) (result : t a e) : unit :=
  match result with
  | inl value => function_value value
  | inr _ => tt
  end.

Definition iter_error {e a : Set}
    (function_value : e -> unit) (result : t a e) : unit :=
  match result with
  | inl _ => tt
  | inr error => function_value error
  end.

Definition is_ok {a e : Set} (result : t a e) : bool :=
  match result with inl _ => true | inr _ => false end.

Definition is_error {a e : Set} (result : t a e) : bool :=
  negb (is_ok result).

Definition equal {a e : Set}
    (equal_ok : a -> a -> bool) (equal_error : e -> e -> bool)
    (left right : t a e) : bool :=
  match left, right with
  | inl left_value, inl right_value => equal_ok left_value right_value
  | inr left_error, inr right_error => equal_error left_error right_error
  | _, _ => false
  end.

Definition compare {a e : Set}
    (compare_ok : a -> a -> int) (compare_error : e -> e -> int)
    (left right : t a e) : int :=
  match left, right with
  | inl left_value, inl right_value => compare_ok left_value right_value
  | inr left_error, inr right_error => compare_error left_error right_error
  | inl _, inr _ => -1
  | inr _, inl _ => 1
  end.

Definition to_option {a e : Set} (result : t a e) : option a :=
  match result with inl value => Some value | inr _ => None end.

Definition to_list {a e : Set} (result : t a e) : list a :=
  match result with inl value => [value] | inr _ => [] end.

Definition to_seq {a e : Set} (result : t a e) : OCamlSeq.t a :=
  match result with
  | inl value => OCamlSeq.singleton value
  | inr _ => OCamlSeq.empty
  end.

Module Syntax.
End Syntax.
