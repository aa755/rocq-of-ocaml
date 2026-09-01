Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.OCamlSeq.

Import ListNotations.
Local Open Scope Z_scope.

(** Executable finite-list model of OCaml's immutable arrays. *)

Definition t (a : Set) : Set := list a.

Definition length {a : Set} (values : t a) : int :=
  Z.of_nat (List.length values).

Definition of_list {a : Set} (values : list a) : t a := values.

Definition to_list {a : Set} (values : t a) : list a := values.

Fixpoint init_nat {a : Set}
    (remaining : nat) (index : int) (element : int -> a) : t a :=
  match remaining with
  | O => []
  | S remaining' =>
      element index :: init_nat remaining' (index + 1) element
  end.

Definition init {a : Set} `{Unreachable (t a)}
    (count : int) (element : int -> a) : t a :=
  if Z.ltb count 0
  then unreachable
  else init_nat (Z.to_nat count) 0 element.

Definition get {a : Set} `{Unreachable a}
    (values : t a) (index : int) : a :=
  if Z.ltb index 0 then
    unreachable
  else
    match List.nth_error values (Z.to_nat index) with
    | Some value => value
    | None => unreachable
    end.

Definition map {a b : Set} (function_value : a -> b) (values : t a) : t b :=
  List.map function_value values.

Fixpoint mapi_from {a b : Set}
    (function_value : int -> a -> b) (index : int) (values : t a) : t b :=
  match values with
  | [] => []
  | value :: values' =>
      function_value index value ::
      mapi_from function_value (index + 1) values'
  end.

Definition mapi {a b : Set}
    (function_value : int -> a -> b) (values : t a) : t b :=
  mapi_from function_value 0 values.

Fixpoint fold_left {a acc : Set}
    (function_value : acc -> a -> acc) (state : acc) (values : t a) : acc :=
  match values with
  | [] => state
  | value :: values' =>
      fold_left function_value (function_value state value) values'
  end.

Definition fold_right {a acc : Set}
    (function_value : a -> acc -> acc) (values : t a) (state : acc) : acc :=
  List.fold_right function_value state values.

Fixpoint exists2_same_length {a b : Set}
    (predicate : a -> b -> bool) (left : t a) (right : t b) : bool :=
  match left, right with
  | [], [] => false
  | left_head :: left_tail, right_head :: right_tail =>
      orb (predicate left_head right_head)
        (exists2_same_length predicate left_tail right_tail)
  | _, _ => false
  end.

Definition _exists2 {a b : Set} `{Unreachable bool}
    (predicate : a -> b -> bool) (left : t a) (right : t b) : bool :=
  if Nat.eqb (List.length left) (List.length right) then
    exists2_same_length predicate left right
  else
    RocqOfOCaml.Basics.Stdlib.invalid_arg "Iarray.exists2".

Fixpoint find_mapi_from {a b : Set}
    (function_value : int -> a -> option b)
    (index : int) (values : t a) : option b :=
  match values with
  | [] => None
  | value :: values' =>
      match function_value index value with
      | Some result => Some result
      | None => find_mapi_from function_value (index + 1) values'
      end
  end.

Definition find_mapi {a b : Set}
    (function_value : int -> a -> option b) (values : t a) : option b :=
  find_mapi_from function_value 0 values.

Definition to_seq {a : Set} (values : t a) : OCamlSeq.t a :=
  OCamlSeq.of_list values.

Definition of_seq {a : Set} (values : OCamlSeq.t a) : t a :=
  OCamlSeq.to_list values.
