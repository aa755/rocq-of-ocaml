Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.

(** Type-level compatibility for OCaml's mutable hash-table functor.

    The latest Monad VM model exports hash-table modules for its numeric key
    types but never creates or accesses a table in the transition semantics.
    We retain the key/hash interface and choose association lists as the
    hidden table carrier.  Operations can be added here if the VM starts using
    this currently static API. *)

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
  Record signature {key : Set} {t : Set -> Set} : Set := {
    key := key;
    t := t;
  }.
End S.
Definition S := @S.signature.
Arguments S {_ _}.

Definition Make {key : Set} (_ : HashedType (t := key)) :
    S (key := key) (t := fun value => list (key * value)) :=
  @S.Build_signature key (fun value => list (key * value)).
