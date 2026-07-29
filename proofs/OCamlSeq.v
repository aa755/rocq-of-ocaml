(** A total compatibility model for the finite fragment of [Stdlib.Seq].

    OCaml represents sequences as arbitrary thunks.  They can be infinite,
    effectful, or divergent when forced, so the complete interface cannot be
    represented by total Gallina functions.  This model deliberately uses an
    inductive sequence.  Every consumer is therefore structurally terminating.

    Translated projects must exclude unsupported infinite or effectful
    operations when copying [Stdlib.Seq]'s module signature.  [range] handles
    the common total fragment [Seq.take count (Seq.ints start)] without ever
    constructing an infinite sequence. *)

Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.Settings.

Import ListNotations.
Local Open Scope Z_scope.

Inductive t (A : Set) : Set :=
| Empty
| More (head : A) (tail : t A).

Arguments Empty {_}.
Arguments More {_}.

(** [node] is the one-step view exposed by OCaml's [seq ()] operation. *)
Inductive node (A : Set) : Set :=
| Nil
| Cons (head : A) (tail : t A).

Arguments Nil {_}.
Arguments Cons {_}.

Definition observe {A : Set} (values : t A) (_ : unit) : node A :=
  match values with
  | Empty => Nil
  | More head tail => Cons head tail
  end.

(** This coercion preserves the source-level observation syntax [seq ()]. *)
Coercion observe : t >-> Funclass.

Fixpoint of_list {A : Set} (values : list A) : t A :=
  match values with
  | [] => Empty
  | head :: tail => More head (of_list tail)
  end.

Fixpoint to_list {A : Set} (values : t A) : list A :=
  match values with
  | Empty => []
  | More head tail => head :: to_list tail
  end.

Definition empty {A : Set} : t A := Empty.

Definition _return {A : Set} (value : A) : t A := More value Empty.

Definition singleton {A : Set} (value : A) : t A := _return value.

Definition cons {A : Set} (value : A) (values : t A) : t A :=
  More value values.

Definition is_empty {A : Set} (values : t A) : bool :=
  match values with
  | Empty => true
  | More _ _ => false
  end.

Definition uncons {A : Set} (values : t A) : option (A * t A) :=
  match values with
  | Empty => None
  | More head tail => Some (head, tail)
  end.

Fixpoint length_nat {A : Set} (values : t A) : nat :=
  match values with
  | Empty => O
  | More _ tail => S (length_nat tail)
  end.

Definition length {A : Set} (values : t A) : int :=
  Z.of_nat (length_nat values).

Fixpoint append {A : Set} (left right : t A) : t A :=
  match left with
  | Empty => right
  | More head tail => More head (append tail right)
  end.

Fixpoint map {A B : Set} (function_value : A -> B) (values : t A) : t B :=
  match values with
  | Empty => Empty
  | More head tail => More (function_value head) (map function_value tail)
  end.

Fixpoint mapi_from {A B : Set}
    (index : int) (function_value : int -> A -> B) (values : t A) : t B :=
  match values with
  | Empty => Empty
  | More head tail =>
      More (function_value index head)
        (mapi_from (Z.add index 1) function_value tail)
  end.

Definition mapi {A B : Set}
    (function_value : int -> A -> B) (values : t A) : t B :=
  mapi_from 0 function_value values.

Fixpoint filter {A : Set}
    (predicate : A -> bool) (values : t A) : t A :=
  match values with
  | Empty => Empty
  | More head tail =>
      if predicate head
      then More head (filter predicate tail)
      else filter predicate tail
  end.

Fixpoint filteri_from {A : Set}
    (index : int) (predicate : int -> A -> bool) (values : t A) : t A :=
  match values with
  | Empty => Empty
  | More head tail =>
      let rest := filteri_from (Z.add index 1) predicate tail in
      if predicate index head then More head rest else rest
  end.

Definition filteri {A : Set}
    (predicate : int -> A -> bool) (values : t A) : t A :=
  filteri_from 0 predicate values.

Fixpoint filter_map {A B : Set}
    (function_value : A -> option B) (values : t A) : t B :=
  match values with
  | Empty => Empty
  | More head tail =>
      match function_value head with
      | None => filter_map function_value tail
      | Some value => More value (filter_map function_value tail)
      end
  end.

Fixpoint concat {A : Set} (values : t (t A)) : t A :=
  match values with
  | Empty => Empty
  | More head tail => append head (concat tail)
  end.

Fixpoint flat_map {A B : Set}
    (function_value : A -> t B) (values : t A) : t B :=
  match values with
  | Empty => Empty
  | More head tail =>
      append (function_value head) (flat_map function_value tail)
  end.

Definition concat_map {A B : Set} : (A -> t B) -> t A -> t B :=
  flat_map.

Fixpoint iter {A B : Set}
    (function_value : A -> B) (values : t A) : unit :=
  match values with
  | Empty => tt
  | More head tail =>
      let '_ := function_value head in
      iter function_value tail
  end.

Fixpoint iteri_from {A B : Set}
    (index : int) (function_value : int -> A -> B) (values : t A) : unit :=
  match values with
  | Empty => tt
  | More head tail =>
      let '_ := function_value index head in
      iteri_from (Z.add index 1) function_value tail
  end.

Definition iteri {A B : Set}
    (function_value : int -> A -> B) (values : t A) : unit :=
  iteri_from 0 function_value values.

Fixpoint fold_left {A B : Set}
    (function_value : A -> B -> A) (accumulator : A) (values : t B) : A :=
  match values with
  | Empty => accumulator
  | More head tail =>
      fold_left function_value (function_value accumulator head) tail
  end.

Fixpoint fold_lefti_from {A B : Set}
    (index : int) (function_value : A -> int -> B -> A)
    (accumulator : A) (values : t B) : A :=
  match values with
  | Empty => accumulator
  | More head tail =>
      fold_lefti_from (Z.add index 1) function_value
        (function_value accumulator index head) tail
  end.

Definition fold_lefti {A B : Set}
    (function_value : A -> int -> B -> A)
    (accumulator : A) (values : t B) : A :=
  fold_lefti_from 0 function_value accumulator values.

Fixpoint for_all {A : Set}
    (predicate : A -> bool) (values : t A) : bool :=
  match values with
  | Empty => true
  | More head tail => andb (predicate head) (for_all predicate tail)
  end.

Fixpoint _exists {A : Set}
    (predicate : A -> bool) (values : t A) : bool :=
  match values with
  | Empty => false
  | More head tail => orb (predicate head) (_exists predicate tail)
  end.

Fixpoint find {A : Set}
    (predicate : A -> bool) (values : t A) : option A :=
  match values with
  | Empty => None
  | More head tail =>
      if predicate head then Some head else find predicate tail
  end.

Fixpoint find_index_from {A : Set}
    (index : int) (predicate : A -> bool) (values : t A) : option int :=
  match values with
  | Empty => None
  | More head tail =>
      if predicate head
      then Some index
      else find_index_from (Z.add index 1) predicate tail
  end.

Definition find_index {A : Set}
    (predicate : A -> bool) (values : t A) : option int :=
  find_index_from 0 predicate values.

Fixpoint find_map {A B : Set}
    (function_value : A -> option B) (values : t A) : option B :=
  match values with
  | Empty => None
  | More head tail =>
      match function_value head with
      | Some value => Some value
      | None => find_map function_value tail
      end
  end.

Fixpoint find_mapi_from {A B : Set}
    (index : int) (function_value : int -> A -> option B)
    (values : t A) : option B :=
  match values with
  | Empty => None
  | More head tail =>
      match function_value index head with
      | Some value => Some value
      | None => find_mapi_from (Z.add index 1) function_value tail
      end
  end.

Definition find_mapi {A B : Set}
    (function_value : int -> A -> option B) (values : t A) : option B :=
  find_mapi_from 0 function_value values.

Fixpoint iter2 {A B C : Set}
    (function_value : A -> B -> C) (left : t A) (right : t B) : unit :=
  match left, right with
  | More left_head left_tail, More right_head right_tail =>
      let '_ := function_value left_head right_head in
      iter2 function_value left_tail right_tail
  | _, _ => tt
  end.

Fixpoint fold_left2 {A B C : Set}
    (function_value : A -> B -> C -> A) (accumulator : A)
    (left : t B) (right : t C) : A :=
  match left, right with
  | More left_head left_tail, More right_head right_tail =>
      fold_left2 function_value
        (function_value accumulator left_head right_head)
        left_tail right_tail
  | _, _ => accumulator
  end.

Fixpoint for_all2 {A B : Set}
    (predicate : A -> B -> bool) (left : t A) (right : t B) : bool :=
  match left, right with
  | More left_head left_tail, More right_head right_tail =>
      andb (predicate left_head right_head)
        (for_all2 predicate left_tail right_tail)
  | _, _ => true
  end.

Fixpoint _exists2 {A B : Set}
    (predicate : A -> B -> bool) (left : t A) (right : t B) : bool :=
  match left, right with
  | More left_head left_tail, More right_head right_tail =>
      orb (predicate left_head right_head)
        (_exists2 predicate left_tail right_tail)
  | _, _ => false
  end.

Fixpoint equal {A B : Set}
    (equal_value : A -> B -> bool) (left : t A) (right : t B) : bool :=
  match left, right with
  | Empty, Empty => true
  | More left_head left_tail, More right_head right_tail =>
      andb (equal_value left_head right_head)
        (equal equal_value left_tail right_tail)
  | _, _ => false
  end.

Fixpoint compare {A B : Set}
    (compare_value : A -> B -> int) (left : t A) (right : t B) : int :=
  match left, right with
  | Empty, Empty => 0
  | Empty, More _ _ => -1
  | More _ _, Empty => 1
  | More left_head left_tail, More right_head right_tail =>
      let comparison := compare_value left_head right_head in
      if nequiv_decb comparison 0
      then comparison
      else compare compare_value left_tail right_tail
  end.

Fixpoint init_nat {A : Set}
    (remaining : nat) (index : int) (function_value : int -> A) : t A :=
  match remaining with
  | O => Empty
  | S remaining =>
      More (function_value index)
        (init_nat remaining (Z.add index 1) function_value)
  end.

Definition init {A : Set} `{Unreachable (t A)}
    (count : int) (function_value : int -> A) : t A :=
  if RocqOfOCaml.Basics.Stdlib.lt count 0
  then RocqOfOCaml.Basics.Stdlib.invalid_arg "Seq.init"
  else init_nat (Z.to_nat count) 0 function_value.

Fixpoint scan_tail {A B : Set}
    (function_value : A -> B -> A) (state : A) (values : t B) : t A :=
  match values with
  | Empty => Empty
  | More head tail =>
      let state := function_value state head in
      More state (scan_tail function_value state tail)
  end.

Definition scan {A B : Set}
    (function_value : A -> B -> A) (state : A) (values : t B) : t A :=
  More state (scan_tail function_value state values).

Fixpoint take_nat {A : Set} (count : nat) (values : t A) : t A :=
  match count, values with
  | O, _ => Empty
  | S count, Empty => Empty
  | S count, More head tail => More head (take_nat count tail)
  end.

Definition take {A : Set} `{Unreachable (t A)}
    (count : int) (values : t A) : t A :=
  if RocqOfOCaml.Basics.Stdlib.lt count 0
  then RocqOfOCaml.Basics.Stdlib.invalid_arg "Seq.take"
  else take_nat (Z.to_nat count) values.

Fixpoint drop_nat {A : Set} (count : nat) (values : t A) : t A :=
  match count, values with
  | O, _ => values
  | S count, Empty => Empty
  | S count, More _ tail => drop_nat count tail
  end.

Definition drop {A : Set} `{Unreachable (t A)}
    (count : int) (values : t A) : t A :=
  if RocqOfOCaml.Basics.Stdlib.lt count 0
  then RocqOfOCaml.Basics.Stdlib.invalid_arg "Seq.drop"
  else drop_nat (Z.to_nat count) values.

Fixpoint take_while {A : Set}
    (predicate : A -> bool) (values : t A) : t A :=
  match values with
  | Empty => Empty
  | More head tail =>
      if predicate head
      then More head (take_while predicate tail)
      else Empty
  end.

Fixpoint drop_while {A : Set}
    (predicate : A -> bool) (values : t A) : t A :=
  match values with
  | Empty => Empty
  | More head tail =>
      if predicate head then drop_while predicate tail else values
  end.

Fixpoint zip {A B : Set} (left : t A) (right : t B) : t (A * B) :=
  match left, right with
  | More left_head left_tail, More right_head right_tail =>
      More (left_head, right_head) (zip left_tail right_tail)
  | _, _ => Empty
  end.

Fixpoint map2 {A B C : Set}
    (function_value : A -> B -> C) (left : t A) (right : t B) : t C :=
  match left, right with
  | More left_head left_tail, More right_head right_tail =>
      More (function_value left_head right_head)
        (map2 function_value left_tail right_tail)
  | _, _ => Empty
  end.

Fixpoint unzip {A B : Set} (values : t (A * B)) : t A * t B :=
  match values with
  | Empty => (Empty, Empty)
  | More (left_value, right_value) tail =>
      let '(left_tail, right_tail) := unzip tail in
      (More left_value left_tail, More right_value right_tail)
  end.

Definition split {A B : Set} : t (A * B) -> t A * t B := unzip.

Fixpoint partition_map {A B C : Set}
    (function_value : A -> sum B C) (values : t A) : t B * t C :=
  match values with
  | Empty => (Empty, Empty)
  | More head tail =>
      let '(left_tail, right_tail) := partition_map function_value tail in
      match function_value head with
      | inl left_value => (More left_value left_tail, right_tail)
      | inr right_value => (left_tail, More right_value right_tail)
      end
  end.

Definition partition {A : Set}
    (predicate : A -> bool) (values : t A) : t A * t A :=
  (filter predicate values, filter (fun value => negb (predicate value)) values).

Definition map_product {A B C : Set}
    (function_value : A -> B -> C) (left : t A) (right : t B) : t C :=
  flat_map
    (fun left_value => map (function_value left_value) right)
    left.

Definition product {A B : Set} (left : t A) (right : t B) : t (A * B) :=
  map_product (fun left_value right_value => (left_value, right_value))
    left right.

(** A finite replacement for [take count (ints start)]. *)
Definition range `{Unreachable (t int)} (count start : int) : t int :=
  init count (fun index => Z.add start index).
