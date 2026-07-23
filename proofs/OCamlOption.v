From Stdlib Require Import ZArith List Bool.
Require Import RocqOfOCaml.Basics RocqOfOCaml.OCamlSeq.

Import ListNotations.
Local Open Scope Z_scope.

(** Executable model of OCaml 5.4's [Stdlib.Option] module.

    The ordinary operations reduce directly on Gallina's [option].  OCaml's
    [Option.get None] raises [Invalid_argument]; generated pure Gallina has no
    exception effect, so that exceptional branch uses the translator's
    existing partial-operation axiom. *)

Definition t (a : Set) : Set := option a.

Definition none {a : Set} : option a := None.

Definition some {a : Set} (value : a) : option a := Some value.

Definition value {a : Set} (o : option a) (default : a) : a :=
  match o with
  | Some value => value
  | None => default
  end.

Definition get {a : Set} (o : option a) : a :=
  match o with
  | Some value => value
  | None => Basics.axiom
  end.

Definition bind {a b : Set}
    (o : option a) (f : a -> option b) : option b :=
  match o with
  | Some value => f value
  | None => None
  end.

Definition join {a : Set} (o : option (option a)) : option a :=
  match o with
  | Some inner => inner
  | None => None
  end.

Definition map {a b : Set} (f : a -> b) (o : option a) : option b :=
  match o with
  | Some value => Some (f value)
  | None => None
  end.

Definition fold {a b : Set}
    (none : a) (some : b -> a) (o : option b) : a :=
  match o with
  | Some value => some value
  | None => none
  end.

Definition iter {a : Set} (f : a -> unit) (o : option a) : unit :=
  match o with
  | Some value => f value
  | None => tt
  end.

Definition is_none {a : Set} (o : option a) : bool :=
  match o with
  | None => true
  | Some _ => false
  end.

Definition is_some {a : Set} (o : option a) : bool :=
  match o with
  | Some _ => true
  | None => false
  end.

Definition equal {a : Set}
    (eq : a -> a -> bool) (left right : option a) : bool :=
  match left, right with
  | None, None => true
  | Some x, Some y => eq x y
  | _, _ => false
  end.

Definition compare {a : Set}
    (cmp : a -> a -> Z) (left right : option a) : Z :=
  match left, right with
  | None, None => 0
  | None, Some _ => -1
  | Some _, None => 1
  | Some x, Some y => cmp x y
  end.

Definition to_result {e a : Set}
    (none : e) (o : option a) : a + e :=
  match o with
  | Some value => inl value
  | None => inr none
  end.

Definition to_list {a : Set} (o : option a) : list a :=
  match o with
  | Some value => [value]
  | None => []
  end.

Definition to_seq {a : Set} (o : option a) : OCamlSeq.t a :=
  match o with
  | Some value => OCamlSeq.singleton value
  | None => OCamlSeq.empty
  end.
