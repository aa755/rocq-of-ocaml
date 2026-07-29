Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.OCamlSeq.

(** Compatibility for OCaml's mutable hash-table functor.

    The Monad VM exports hash-table modules for numeric key types but does not
    use them in its transition semantics.  Association lists provide an
    executable carrier and executable read-only operations.  Operations whose
    OCaml result relies on mutating an existing table are explicit no-ops:
    Gallina values are immutable, and the translated VM does not observe these
    operations.  A future reachable use must replace this approximation with a
    state-passing model. *)

Import ListNotations.

Definition statistics : Set := unit.

Module HashedType.
  Record signature {t : Set} : Set := {
    t := t;
    equal : t -> t -> bool;
    hash : t -> int;
  }.
End HashedType.
Definition HashedType := @HashedType.signature.
Arguments HashedType {_}.

Module S.
  Record signature {key : Set} {t : Set -> Set} : Type := {
    key := key;
    t := t;
    create : forall {a : Set}, int -> t a;
    clear : forall {a : Set}, t a -> unit;
    reset : forall {a : Set}, t a -> unit;
    copy : forall {a : Set}, t a -> t a;
    add : forall {a : Set}, t a -> key -> a -> unit;
    remove : forall {a : Set}, t a -> key -> unit;
    find : forall {a : Set} `{Unreachable a}, t a -> key -> a;
    find_opt : forall {a : Set}, t a -> key -> option a;
    find_all : forall {a : Set}, t a -> key -> list a;
    replace : forall {a : Set}, t a -> key -> a -> unit;
    mem : forall {a : Set}, t a -> key -> bool;
    iter : forall {a : Set}, (key -> a -> unit) -> t a -> unit;
    filter_map_inplace :
      forall {a : Set}, (key -> a -> option a) -> t a -> unit;
    fold :
      forall {a acc : Set},
        (key -> a -> acc -> acc) -> t a -> acc -> acc;
    length : forall {a : Set}, t a -> int;
    stats : forall {a : Set}, t a -> statistics;
    to_seq : forall {a : Set}, t a -> OCamlSeq.t (key * a);
    to_seq_keys : forall {a : Set}, t a -> OCamlSeq.t key;
    to_seq_values : forall {a : Set}, t a -> OCamlSeq.t a;
    add_seq :
      forall {a : Set}, t a -> OCamlSeq.t (key * a) -> unit;
    replace_seq :
      forall {a : Set}, t a -> OCamlSeq.t (key * a) -> unit;
    of_seq : forall {a : Set}, OCamlSeq.t (key * a) -> t a;
  }.
End S.
Definition S := @S.signature.
Arguments S {_ _}.

Fixpoint assoc_find_opt {key value : Set}
    (equal : key -> key -> bool) (wanted : key)
    (table : list (key * value)) : option value :=
  match table with
  | [] => None
  | (key_value, value) :: tail =>
      if equal wanted key_value then Some value
      else assoc_find_opt equal wanted tail
  end.

Fixpoint assoc_find_all {key value : Set}
    (equal : key -> key -> bool) (wanted : key)
    (table : list (key * value)) : list value :=
  match table with
  | [] => []
  | (key_value, value) :: tail =>
      if equal wanted key_value then
        value :: assoc_find_all equal wanted tail
      else
        assoc_find_all equal wanted tail
  end.

Fixpoint assoc_iter {key value : Set}
    (f : key -> value -> unit) (table : list (key * value)) : unit :=
  match table with
  | [] => tt
  | (key_value, value) :: tail =>
      let '_ := f key_value value in
      assoc_iter f tail
  end.

Fixpoint assoc_fold {key value acc : Set}
    (f : key -> value -> acc -> acc) (table : list (key * value))
    (initial : acc) : acc :=
  match table with
  | [] => initial
  | (key_value, value) :: tail =>
      assoc_fold f tail (f key_value value initial)
  end.

Definition Make {key : Set} (hashed : HashedType (t := key)) :
    S (key := key) (t := fun value => list (key * value)) :=
  let equal := hashed.(HashedType.equal) in
  {| S.create _ _ := [];
     S.clear _ _ := tt;
     S.reset _ _ := tt;
     S.copy _ table := table;
     S.add _ _ _ _ := tt;
     S.remove _ _ _ := tt;
     S.find _ _ table wanted :=
       match assoc_find_opt equal wanted table with
       | Some value => value
       | None => unreachable
       end;
     S.find_opt _ table wanted := assoc_find_opt equal wanted table;
     S.find_all _ table wanted := assoc_find_all equal wanted table;
     S.replace _ _ _ _ := tt;
     S.mem _ table wanted :=
       match assoc_find_opt equal wanted table with
       | Some _ => true
       | None => false
       end;
     S.iter _ f table := assoc_iter f table;
     S.filter_map_inplace _ _ _ := tt;
     S.fold _ _ f table initial := assoc_fold f table initial;
     S.length _ table := Z.of_nat (List.length table);
     S.stats _ _ := tt;
     S.to_seq _ table := OCamlSeq.of_list table;
     S.to_seq_keys _ table :=
       OCamlSeq.of_list (List.map (@fst key _) table);
     S.to_seq_values _ table :=
       OCamlSeq.of_list (List.map (@snd key _) table);
     S.add_seq _ _ _ := tt;
     S.replace_seq _ _ _ := tt;
     S.of_seq _ sequence :=
       OCamlSeq.fold_left
         (fun table binding => binding :: table) [] sequence |}.
