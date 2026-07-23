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

Definition init {a : Set} (count : int) (element : int -> a) : t a :=
  init_nat (Z.to_nat count) 0 element.

Definition get {a : Set} (values : t a) (index : int) : a :=
  match List.nth_error values (Z.to_nat index) with
  | Some value => value
  | None => axiom
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

Fixpoint to_seq_node {a : Set} (values : t a) : OCamlSeq.node a :=
  match values with
  | [] => OCamlSeq.Nil
  | value :: values' =>
      OCamlSeq.Cons value (fun _ => to_seq_node values')
  end.

Definition to_seq {a : Set} (values : t a) : OCamlSeq.t a :=
  fun _ => to_seq_node values.

#[bypass_check(guard)]
Fixpoint of_seq_guarded {a : Set}
    (values : OCamlSeq.t a) (guard : GeneralRecursionGuard)
    {struct guard} : t a :=
  match values tt with
  | OCamlSeq.Nil => []
  | OCamlSeq.Cons value values' =>
      value :: of_seq_guarded values' guard
  end.

Definition of_seq {a : Set} (values : OCamlSeq.t a) : t a :=
  of_seq_guarded values general_recursion_guard.
