From Stdlib Require Import ZArith List Bool.
Require Import RocqOfOCaml.Basics RocqOfOCaml.OCamlSeq.

Import ListNotations.
Local Open Scope Z_scope.

(** Executable model of OCaml 5.4's persistent [Stdlib.Map].

    Maps are sorted association lists.  Every constructor in [Make] preserves
    sortedness and key uniqueness when the supplied OCaml comparator defines
    an order.  This is an implementation choice hidden behind the translated
    [Map.S] signature; it is not exposed to translated source modules. *)

Module OrderedType.
  Record signature {t : Set} : Set := {
    t := t;
    compare : t -> t -> int;
  }.
End OrderedType.
Definition OrderedType := @OrderedType.signature.
Arguments OrderedType {_}.

Module S.
  Record signature {key : Set} {t : Set -> Set} : Set := {
    key := key;
    t := t;
    empty : forall {a : Set}, t a;
    add : forall {a : Set}, key -> a -> t a -> t a;
    add_to_list : forall {a : Set}, key -> a -> t (list a) -> t (list a);
    update :
      forall {a : Set}, key -> (option a -> option a) -> t a -> t a;
    singleton : forall {a : Set}, key -> a -> t a;
    remove : forall {a : Set}, key -> t a -> t a;
    merge :
      forall {a b c : Set},
        (key -> option a -> option b -> option c) -> t a -> t b -> t c;
    union :
      forall {a : Set},
        (key -> a -> a -> option a) -> t a -> t a -> t a;
    cardinal : forall {a : Set}, t a -> int;
    bindings : forall {a : Set}, t a -> list (key * a);
    min_binding : forall {a : Set}, t a -> key * a;
    min_binding_opt : forall {a : Set}, t a -> option (key * a);
    max_binding : forall {a : Set}, t a -> key * a;
    max_binding_opt : forall {a : Set}, t a -> option (key * a);
    choose : forall {a : Set}, t a -> key * a;
    choose_opt : forall {a : Set}, t a -> option (key * a);
    find : forall {a : Set}, key -> t a -> a;
    find_opt : forall {a : Set}, key -> t a -> option a;
    find_first : forall {a : Set}, (key -> bool) -> t a -> key * a;
    find_first_opt :
      forall {a : Set}, (key -> bool) -> t a -> option (key * a);
    find_last : forall {a : Set}, (key -> bool) -> t a -> key * a;
    find_last_opt :
      forall {a : Set}, (key -> bool) -> t a -> option (key * a);
    iter : forall {a : Set}, (key -> a -> unit) -> t a -> unit;
    fold :
      forall {a acc : Set}, (key -> a -> acc -> acc) -> t a -> acc -> acc;
    map : forall {a b : Set}, (a -> b) -> t a -> t b;
    mapi : forall {a b : Set}, (key -> a -> b) -> t a -> t b;
    filter : forall {a : Set}, (key -> a -> bool) -> t a -> t a;
    filter_map :
      forall {a b : Set}, (key -> a -> option b) -> t a -> t b;
    partition :
      forall {a : Set}, (key -> a -> bool) -> t a -> t a * t a;
    split : forall {a : Set}, key -> t a -> t a * option a * t a;
    is_empty : forall {a : Set}, t a -> bool;
    mem : forall {a : Set}, key -> t a -> bool;
    equal : forall {a : Set}, (a -> a -> bool) -> t a -> t a -> bool;
    compare : forall {a : Set}, (a -> a -> int) -> t a -> t a -> int;
    for_all : forall {a : Set}, (key -> a -> bool) -> t a -> bool;
    _exists : forall {a : Set}, (key -> a -> bool) -> t a -> bool;
    to_list : forall {a : Set}, t a -> list (key * a);
    of_list : forall {a : Set}, list (key * a) -> t a;
    to_seq : forall {a : Set}, t a -> OCamlSeq.t (key * a);
    to_rev_seq : forall {a : Set}, t a -> OCamlSeq.t (key * a);
    to_seq_from : forall {a : Set}, key -> t a -> OCamlSeq.t (key * a);
    add_seq :
      forall {a : Set}, OCamlSeq.t (key * a) -> t a -> t a;
    of_seq : forall {a : Set}, OCamlSeq.t (key * a) -> t a;
  }.
End S.
Definition S := @S.signature.
Arguments S {_ _}.

Module Make.
  Section WITH_ORDER.
    Context {key : Set} (Ord : OrderedType (t := key)).

    Definition t (a : Set) : Set := list (key * a).

    Definition key_compare (left right : key) : Z :=
      Ord.(OrderedType.compare) left right.

    Definition key_equal (left right : key) : bool :=
      Z.eqb (key_compare left right) 0.

    Definition key_before (left right : key) : bool :=
      Z.ltb (key_compare left right) 0.

    Fixpoint add {a : Set} (key_value : key) (value : a) (map : t a) : t a :=
      match map with
      | [] => [(key_value, value)]
      | (existing_key, existing_value) :: tail =>
          if key_before key_value existing_key then
            (key_value, value) :: map
          else if key_equal key_value existing_key then
            (key_value, value) :: tail
          else
            (existing_key, existing_value) :: add key_value value tail
      end.

    Fixpoint remove {a : Set} (key_value : key) (map : t a) : t a :=
      match map with
      | [] => []
      | (existing_key, existing_value) :: tail =>
          if key_before key_value existing_key then
            map
          else if key_equal key_value existing_key then
            tail
          else
            (existing_key, existing_value) :: remove key_value tail
      end.

    Fixpoint find_opt {a : Set} (key_value : key) (map : t a) : option a :=
      match map with
      | [] => None
      | (existing_key, value) :: tail =>
          if key_before key_value existing_key then
            None
          else if key_equal key_value existing_key then
            Some value
          else
            find_opt key_value tail
      end.

    Definition find {a : Set} (key_value : key) (map : t a) : a :=
      match find_opt key_value map with
      | Some value => value
      | None => Basics.axiom
      end.

    Definition update {a : Set}
        (key_value : key) (f : option a -> option a) (map : t a) : t a :=
      match f (find_opt key_value map) with
      | Some value => add key_value value map
      | None => remove key_value map
      end.

    Definition add_to_list {a : Set}
        (key_value : key) (value : a) (map : t (list a)) : t (list a) :=
      update key_value
        (fun previous =>
          match previous with
          | Some values => Some (value :: values)
          | None => Some [value]
          end)
        map.

    Definition singleton {a : Set} (key_value : key) (value : a) : t a :=
      [(key_value, value)].

    Fixpoint add_key (key_value : key) (keys : list key) : list key :=
      match keys with
      | [] => [key_value]
      | existing_key :: tail =>
          if key_before key_value existing_key then
            key_value :: keys
          else if key_equal key_value existing_key then
            keys
          else
            existing_key :: add_key key_value tail
      end.

    Fixpoint keys_of {a : Set} (map : t a) : list key :=
      match map with
      | [] => []
      | (key_value, _) :: tail => key_value :: keys_of tail
      end.

    Fixpoint add_keys (source destination : list key) : list key :=
      match source with
      | [] => destination
      | key_value :: tail => add_keys tail (add_key key_value destination)
      end.

    Fixpoint merge_keys {a b c : Set}
        (f : key -> option a -> option b -> option c)
        (keys : list key) (left : t a) (right : t b) : t c :=
      match keys with
      | [] => []
      | key_value :: tail =>
          let merged_tail := merge_keys f tail left right in
          match f key_value
              (find_opt key_value left) (find_opt key_value right) with
          | Some value => add key_value value merged_tail
          | None => merged_tail
          end
      end.

    Definition merge {a b c : Set}
        (f : key -> option a -> option b -> option c)
        (left : t a) (right : t b) : t c :=
      merge_keys f
        (add_keys (keys_of right) (keys_of left))
        left right.

    Definition union {a : Set}
        (f : key -> a -> a -> option a)
        (left right : t a) : t a :=
      merge
        (fun key_value left_value right_value =>
          match left_value, right_value with
          | Some left_value, Some right_value =>
              f key_value left_value right_value
          | Some value, None | None, Some value => Some value
          | None, None => None
          end)
        left right.

    Definition cardinal {a : Set} (map : t a) : int :=
      Z.of_nat (List.length map).

    Definition bindings {a : Set} (map : t a) : list (key * a) := map.

    Definition min_binding_opt {a : Set} (map : t a) : option (key * a) :=
      match map with
      | [] => None
      | binding :: _ => Some binding
      end.

    Fixpoint last_binding_opt {a : Set} (map : t a) : option (key * a) :=
      match map with
      | [] => None
      | [binding] => Some binding
      | _ :: tail => last_binding_opt tail
      end.

    Definition max_binding_opt {a : Set} (map : t a) : option (key * a) :=
      last_binding_opt map.

    Definition choose_opt {a : Set} (map : t a) : option (key * a) :=
      min_binding_opt map.

    Definition min_binding {a : Set} (map : t a) : key * a :=
      match min_binding_opt map with
      | Some binding => binding
      | None => Basics.axiom
      end.

    Definition max_binding {a : Set} (map : t a) : key * a :=
      match max_binding_opt map with
      | Some binding => binding
      | None => Basics.axiom
      end.

    Definition choose {a : Set} (map : t a) : key * a :=
      min_binding map.

    Fixpoint find_first_opt {a : Set}
        (predicate : key -> bool) (map : t a) : option (key * a) :=
      match map with
      | [] => None
      | (key_value, value) as binding :: tail =>
          if predicate key_value then Some binding
          else find_first_opt predicate tail
      end.

    Fixpoint find_last_acc {a : Set}
        (predicate : key -> bool) (map : t a)
        (candidate : option (key * a)) : option (key * a) :=
      match map with
      | [] => candidate
      | (key_value, value) as binding :: tail =>
          find_last_acc predicate tail
            (if predicate key_value then Some binding else candidate)
      end.

    Definition find_last_opt {a : Set}
        (predicate : key -> bool) (map : t a) : option (key * a) :=
      find_last_acc predicate map None.

    Definition find_first {a : Set}
        (predicate : key -> bool) (map : t a) : key * a :=
      match find_first_opt predicate map with
      | Some binding => binding
      | None => Basics.axiom
      end.

    Definition find_last {a : Set}
        (predicate : key -> bool) (map : t a) : key * a :=
      match find_last_opt predicate map with
      | Some binding => binding
      | None => Basics.axiom
      end.

    Fixpoint iter {a : Set}
        (f : key -> a -> unit) (map : t a) : unit :=
      match map with
      | [] => tt
      | (key_value, value) :: tail =>
          let '_ := f key_value value in
          iter f tail
      end.

    Fixpoint fold {a acc : Set}
        (f : key -> a -> acc -> acc) (map : t a) (initial : acc) : acc :=
      match map with
      | [] => initial
      | (key_value, value) :: tail =>
          fold f tail (f key_value value initial)
      end.

    Fixpoint map_values {a b : Set} (f : a -> b) (map : t a) : t b :=
      match map with
      | [] => []
      | (key_value, value) :: tail =>
          (key_value, f value) :: map_values f tail
      end.

    Fixpoint mapi {a b : Set}
        (f : key -> a -> b) (map : t a) : t b :=
      match map with
      | [] => []
      | (key_value, value) :: tail =>
          (key_value, f key_value value) :: mapi f tail
      end.

    Fixpoint filter {a : Set}
        (predicate : key -> a -> bool) (map : t a) : t a :=
      match map with
      | [] => []
      | (key_value, value) as binding :: tail =>
          if predicate key_value value then binding :: filter predicate tail
          else filter predicate tail
      end.

    Fixpoint filter_map {a b : Set}
        (f : key -> a -> option b) (map : t a) : t b :=
      match map with
      | [] => []
      | (key_value, value) :: tail =>
          match f key_value value with
          | Some result => (key_value, result) :: filter_map f tail
          | None => filter_map f tail
          end
      end.

    Fixpoint partition {a : Set}
        (predicate : key -> a -> bool) (map : t a) : t a * t a :=
      match map with
      | [] => ([], [])
      | (key_value, value) as binding :: tail =>
          let '(yes, no) := partition predicate tail in
          if predicate key_value value
          then (binding :: yes, no)
          else (yes, binding :: no)
      end.

    Fixpoint split {a : Set}
        (pivot : key) (map : t a) : t a * option a * t a :=
      match map with
      | [] => ([], None, [])
      | (key_value, value) as binding :: tail =>
          if key_before key_value pivot then
            let '(before, found, after) := split pivot tail in
            (binding :: before, found, after)
          else if key_equal key_value pivot then
            ([], Some value, tail)
          else
            ([], None, map)
      end.

    Definition is_empty {a : Set} (map : t a) : bool :=
      match map with [] => true | _ => false end.

    Definition mem {a : Set} (key_value : key) (map : t a) : bool :=
      match find_opt key_value map with
      | Some _ => true
      | None => false
      end.

    Fixpoint equal {a : Set}
        (value_equal : a -> a -> bool) (left right : t a) : bool :=
      match left, right with
      | [], [] => true
      | (left_key, left_value) :: left_tail,
        (right_key, right_value) :: right_tail =>
          key_equal left_key right_key
          && value_equal left_value right_value
          && equal value_equal left_tail right_tail
      | _, _ => false
      end.

    Fixpoint compare {a : Set}
        (value_compare : a -> a -> int) (left right : t a) : int :=
      match left, right with
      | [], [] => 0
      | [], _ => -1
      | _, [] => 1
      | (left_key, left_value) :: left_tail,
        (right_key, right_value) :: right_tail =>
          let key_result := key_compare left_key right_key in
          if Z.eqb key_result 0 then
            let value_result := value_compare left_value right_value in
            if Z.eqb value_result 0
            then compare value_compare left_tail right_tail
            else value_result
          else key_result
      end.

    Fixpoint for_all {a : Set}
        (predicate : key -> a -> bool) (map : t a) : bool :=
      match map with
      | [] => true
      | (key_value, value) :: tail =>
          predicate key_value value && for_all predicate tail
      end.

    Fixpoint _exists {a : Set}
        (predicate : key -> a -> bool) (map : t a) : bool :=
      match map with
      | [] => false
      | (key_value, value) :: tail =>
          predicate key_value value || _exists predicate tail
      end.

    Definition to_list {a : Set} (map : t a) : list (key * a) :=
      bindings map.

    Fixpoint of_list {a : Set} (bindings : list (key * a)) : t a :=
      match bindings with
      | [] => []
      | (key_value, value) :: tail =>
          add key_value value (of_list tail)
      end.

    Definition to_seq {a : Set} (map : t a) : OCamlSeq.t (key * a) :=
      OCamlSeq.of_list map.

    Definition to_rev_seq {a : Set} (map : t a) : OCamlSeq.t (key * a) :=
      OCamlSeq.of_list (List.rev map).

    Definition to_seq_from {a : Set}
        (lower_bound : key) (map : t a) : OCamlSeq.t (key * a) :=
      OCamlSeq.of_list
        (filter
          (fun key_value _ => negb (key_before key_value lower_bound))
          map).

    Definition add_seq {a : Set}
        (sequence : OCamlSeq.t (key * a)) (map : t a) : t a :=
      OCamlSeq.fold_left
        (fun map '(key_value, value) => add key_value value map)
        map sequence.

    Definition of_seq {a : Set}
        (sequence : OCamlSeq.t (key * a)) : t a :=
      add_seq sequence [].

    Definition module : S (key := key) (t := t) :=
      {| S.empty _ := [];
         S.add _ := add;
         S.add_to_list _ := add_to_list;
         S.update _ := update;
         S.singleton _ := singleton;
         S.remove _ := remove;
         S.merge _ _ _ := merge;
         S.union _ := union;
         S.cardinal _ := cardinal;
         S.bindings _ := bindings;
         S.min_binding _ := min_binding;
         S.min_binding_opt _ := min_binding_opt;
         S.max_binding _ := max_binding;
         S.max_binding_opt _ := max_binding_opt;
         S.choose _ := choose;
         S.choose_opt _ := choose_opt;
         S.find _ := find;
         S.find_opt _ := find_opt;
         S.find_first _ := find_first;
         S.find_first_opt _ := find_first_opt;
         S.find_last _ := find_last;
         S.find_last_opt _ := find_last_opt;
         S.iter _ := iter;
         S.fold _ _ := fold;
         S.map _ _ := map_values;
         S.mapi _ _ := mapi;
         S.filter _ := filter;
         S.filter_map _ _ := filter_map;
         S.partition _ := partition;
         S.split _ := split;
         S.is_empty _ := is_empty;
         S.mem _ := mem;
         S.equal _ := equal;
         S.compare _ := compare;
         S.for_all _ := for_all;
         S._exists _ := _exists;
         S.to_list _ := to_list;
         S.of_list _ := of_list;
         S.to_seq _ := to_seq;
         S.to_rev_seq _ := to_rev_seq;
         S.to_seq_from _ := to_seq_from;
         S.add_seq _ := add_seq;
         S.of_seq _ := of_seq |}.
  End WITH_ORDER.
End Make.

Definition Make {Ord_t : Set} (Ord : OrderedType (t := Ord_t))
    : S (key := Ord_t) (t := @Make.t Ord_t) :=
  Make.module Ord.
