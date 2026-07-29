From Stdlib Require Import ZArith List Bool.
Require Import
  RocqOfOCaml.Basics
  RocqOfOCaml.OCamlMap
  RocqOfOCaml.OCamlSeq.

Import ListNotations.
Local Open Scope Z_scope.

(** Executable sorted-list model of OCaml 5.4's [Stdlib.Set]. *)

Module OrderedType := OCamlMap.OrderedType.
Definition OrderedType := @OrderedType.signature.
Arguments OrderedType {_}.

Module S.
  Record signature {elt : Set} {t : Set} : Type := {
    elt := elt;
    t := t;
    empty : t;
    add : elt -> t -> t;
    singleton : elt -> t;
    remove : elt -> t -> t;
    union : t -> t -> t;
    inter : t -> t -> t;
    disjoint : t -> t -> bool;
    diff : t -> t -> t;
    cardinal : t -> int;
    elements : t -> list elt;
    min_elt : forall `{Unreachable elt}, t -> elt;
    min_elt_opt : t -> option elt;
    max_elt : forall `{Unreachable elt}, t -> elt;
    max_elt_opt : t -> option elt;
    choose : forall `{Unreachable elt}, t -> elt;
    choose_opt : t -> option elt;
    find : forall `{Unreachable elt}, elt -> t -> elt;
    find_opt : elt -> t -> option elt;
    find_first : forall `{Unreachable elt}, (elt -> bool) -> t -> elt;
    find_first_opt : (elt -> bool) -> t -> option elt;
    find_last : forall `{Unreachable elt}, (elt -> bool) -> t -> elt;
    find_last_opt : (elt -> bool) -> t -> option elt;
    iter : (elt -> unit) -> t -> unit;
    fold : forall {acc : Set}, (elt -> acc -> acc) -> t -> acc -> acc;
    map : (elt -> elt) -> t -> t;
    filter : (elt -> bool) -> t -> t;
    filter_map : (elt -> option elt) -> t -> t;
    partition : (elt -> bool) -> t -> t * t;
    split : elt -> t -> t * bool * t;
    is_empty : t -> bool;
    mem : elt -> t -> bool;
    equal : t -> t -> bool;
    compare : t -> t -> int;
    subset : t -> t -> bool;
    for_all : (elt -> bool) -> t -> bool;
    _exists : (elt -> bool) -> t -> bool;
    to_list : t -> list elt;
    of_list : list elt -> t;
    to_seq_from : elt -> t -> OCamlSeq.t elt;
    to_seq : t -> OCamlSeq.t elt;
    to_rev_seq : t -> OCamlSeq.t elt;
    add_seq : OCamlSeq.t elt -> t -> t;
    of_seq : OCamlSeq.t elt -> t;
  }.
End S.
Definition S := @S.signature.
Arguments S {_ _}.

Module Make.
  Section WITH_ORDER.
    Context {elt : Set} (Ord : OrderedType (t := elt)).

    Definition t : Set := list elt.

    Definition compare_elt (left right : elt) : Z :=
      Ord.(OCamlMap.OrderedType.compare) left right.

    Definition equal_elt (left right : elt) : bool :=
      Z.eqb (compare_elt left right) 0.

    Definition before (left right : elt) : bool :=
      Z.ltb (compare_elt left right) 0.

    Fixpoint add (value : elt) (set : t) : t :=
      match set with
      | [] => [value]
      | existing :: tail =>
          if before value existing then value :: set
          else if equal_elt value existing then set
          else existing :: add value tail
      end.

    Fixpoint remove (value : elt) (set : t) : t :=
      match set with
      | [] => []
      | existing :: tail =>
          if before value existing then set
          else if equal_elt value existing then tail
          else existing :: remove value tail
      end.

    Fixpoint find_opt (value : elt) (set : t) : option elt :=
      match set with
      | [] => None
      | existing :: tail =>
          if before value existing then None
          else if equal_elt value existing then Some existing
          else find_opt value tail
      end.

    Definition mem (value : elt) (set : t) : bool :=
      match find_opt value set with Some _ => true | None => false end.

    Definition find `{Unreachable elt} (value : elt) (set : t) : elt :=
      match find_opt value set with
      | Some existing => existing
      | None => unreachable
      end.

    Definition singleton (value : elt) : t := [value].

    Fixpoint union (left right : t) : t :=
      match left with
      | [] => right
      | value :: tail => union tail (add value right)
      end.

    Fixpoint inter (left right : t) : t :=
      match left with
      | [] => []
      | value :: tail =>
          if mem value right then value :: inter tail right
          else inter tail right
      end.

    Fixpoint disjoint (left right : t) : bool :=
      match left with
      | [] => true
      | value :: tail =>
          if mem value right then false else disjoint tail right
      end.

    Fixpoint diff (left right : t) : t :=
      match left with
      | [] => []
      | value :: tail =>
          if mem value right then diff tail right
          else value :: diff tail right
      end.

    Definition cardinal (set : t) : int := Z.of_nat (List.length set).
    Definition elements (set : t) : list elt := set.

    Definition min_elt_opt (set : t) : option elt :=
      match set with [] => None | value :: _ => Some value end.

    Fixpoint max_elt_opt (set : t) : option elt :=
      match set with
      | [] => None
      | [value] => Some value
      | _ :: tail => max_elt_opt tail
      end.

    Definition choose_opt (set : t) : option elt := min_elt_opt set.

    Definition min_elt `{Unreachable elt} (set : t) : elt :=
      match min_elt_opt set with
      | Some value => value
      | None => unreachable
      end.

    Definition max_elt `{Unreachable elt} (set : t) : elt :=
      match max_elt_opt set with
      | Some value => value
      | None => unreachable
      end.

    Definition choose `{Unreachable elt} (set : t) : elt := min_elt set.

    Fixpoint find_first_opt
        (predicate : elt -> bool) (set : t) : option elt :=
      match set with
      | [] => None
      | value :: tail =>
          if predicate value then Some value else find_first_opt predicate tail
      end.

    Fixpoint find_last_acc
        (predicate : elt -> bool) (set : t)
        (candidate : option elt) : option elt :=
      match set with
      | [] => candidate
      | value :: tail =>
          find_last_acc predicate tail
            (if predicate value then Some value else candidate)
      end.

    Definition find_last_opt
        (predicate : elt -> bool) (set : t) : option elt :=
      find_last_acc predicate set None.

    Definition find_first `{Unreachable elt}
        (predicate : elt -> bool) (set : t) : elt :=
      match find_first_opt predicate set with
      | Some value => value
      | None => unreachable
      end.

    Definition find_last `{Unreachable elt}
        (predicate : elt -> bool) (set : t) : elt :=
      match find_last_opt predicate set with
      | Some value => value
      | None => unreachable
      end.

    Fixpoint iter (f : elt -> unit) (set : t) : unit :=
      match set with
      | [] => tt
      | value :: tail =>
          let '_ := f value in
          iter f tail
      end.

    Fixpoint fold {acc : Set}
        (f : elt -> acc -> acc) (set : t) (initial : acc) : acc :=
      match set with
      | [] => initial
      | value :: tail => fold f tail (f value initial)
      end.

    Fixpoint map (f : elt -> elt) (set : t) : t :=
      match set with
      | [] => []
      | value :: tail => add (f value) (map f tail)
      end.

    Fixpoint filter (predicate : elt -> bool) (set : t) : t :=
      match set with
      | [] => []
      | value :: tail =>
          if predicate value then value :: filter predicate tail
          else filter predicate tail
      end.

    Fixpoint filter_map (f : elt -> option elt) (set : t) : t :=
      match set with
      | [] => []
      | value :: tail =>
          match f value with
          | Some result => add result (filter_map f tail)
          | None => filter_map f tail
          end
      end.

    Fixpoint partition (predicate : elt -> bool) (set : t) : t * t :=
      match set with
      | [] => ([], [])
      | value :: tail =>
          let '(yes, no) := partition predicate tail in
          if predicate value then (value :: yes, no) else (yes, value :: no)
      end.

    Fixpoint split (pivot : elt) (set : t) : t * bool * t :=
      match set with
      | [] => ([], false, [])
      | value :: tail =>
          if before value pivot then
            let '(lower, present, upper) := split pivot tail in
            (value :: lower, present, upper)
          else if equal_elt value pivot then
            ([], true, tail)
          else
            ([], false, set)
      end.

    Definition is_empty (set : t) : bool :=
      match set with [] => true | _ => false end.

    Fixpoint equal (left right : t) : bool :=
      match left, right with
      | [], [] => true
      | left_value :: left_tail, right_value :: right_tail =>
          equal_elt left_value right_value && equal left_tail right_tail
      | _, _ => false
      end.

    Fixpoint compare (left right : t) : int :=
      match left, right with
      | [], [] => 0
      | [], _ => -1
      | _, [] => 1
      | left_value :: left_tail, right_value :: right_tail =>
          let result := compare_elt left_value right_value in
          if Z.eqb result 0 then compare left_tail right_tail else result
      end.

    Fixpoint subset (left right : t) : bool :=
      match left with
      | [] => true
      | value :: tail => mem value right && subset tail right
      end.

    Fixpoint for_all (predicate : elt -> bool) (set : t) : bool :=
      match set with
      | [] => true
      | value :: tail => predicate value && for_all predicate tail
      end.

    Fixpoint _exists (predicate : elt -> bool) (set : t) : bool :=
      match set with
      | [] => false
      | value :: tail => predicate value || _exists predicate tail
      end.

    Definition to_list (set : t) : list elt := set.

    Fixpoint of_list (values : list elt) : t :=
      match values with
      | [] => []
      | value :: tail => add value (of_list tail)
      end.

    Definition to_seq (set : t) : OCamlSeq.t elt :=
      OCamlSeq.of_list set.

    Definition to_rev_seq (set : t) : OCamlSeq.t elt :=
      OCamlSeq.of_list (List.rev set).

    Definition to_seq_from (lower_bound : elt) (set : t) : OCamlSeq.t elt :=
      OCamlSeq.of_list
        (filter (fun value => negb (before value lower_bound)) set).

    Definition add_seq (sequence : OCamlSeq.t elt) (set : t) : t :=
      OCamlSeq.fold_left (fun set value => add value set) set sequence.

    Definition of_seq (sequence : OCamlSeq.t elt) : t :=
      add_seq sequence [].

    Definition module : S (elt := elt) (t := t) :=
      {| S.empty := [];
         S.add := add;
         S.singleton := singleton;
         S.remove := remove;
         S.union := union;
         S.inter := inter;
         S.disjoint := disjoint;
         S.diff := diff;
         S.cardinal := cardinal;
         S.elements := elements;
         S.min_elt _ := min_elt;
         S.min_elt_opt := min_elt_opt;
         S.max_elt _ := max_elt;
         S.max_elt_opt := max_elt_opt;
         S.choose _ := choose;
         S.choose_opt := choose_opt;
         S.find _ := find;
         S.find_opt := find_opt;
         S.find_first _ := find_first;
         S.find_first_opt := find_first_opt;
         S.find_last _ := find_last;
         S.find_last_opt := find_last_opt;
         S.iter := iter;
         S.fold _ := fold;
         S.map := map;
         S.filter := filter;
         S.filter_map := filter_map;
         S.partition := partition;
         S.split := split;
         S.is_empty := is_empty;
         S.mem := mem;
         S.equal := equal;
         S.compare := compare;
         S.subset := subset;
         S.for_all := for_all;
         S._exists := _exists;
         S.to_list := to_list;
         S.of_list := of_list;
         S.to_seq_from := to_seq_from;
         S.to_seq := to_seq;
         S.to_rev_seq := to_rev_seq;
         S.add_seq := add_seq;
         S.of_seq := of_seq |}.
  End WITH_ORDER.
End Make.

Definition Make {Ord_t : Set} (Ord : OrderedType (t := Ord_t))
    : S (elt := Ord_t) (t := @Make.t Ord_t) :=
  Make.module Ord.
