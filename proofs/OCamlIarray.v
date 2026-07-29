Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.OCamlSeq.

Import ListNotations.
Local Open Scope Z_scope.

(** Executable finite-list model of OCaml's immutable arrays. *)

Definition t (a : Set) : Set := list a.

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
