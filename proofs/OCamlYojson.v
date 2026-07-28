Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.

(** The concrete recursive shape of [Yojson.Safe.t].

    Keeping the constructors typed avoids the existential payload and
    logically inconsistent casts previously used for polymorphic variants.
    Parsing and rendering are still outside the executable VM semantics. *)
Inductive t : Set :=
| Null : t
| Bool : bool -> t
| Int : int -> t
| Float : float -> t
| String : string -> t
| Assoc : list (string * t) -> t
| List : list t -> t
| Intlit : string -> t
| Tuple : list t -> t
| Variant : string -> option t -> t.

Module Util.
  Parameter member : string -> t -> t.
  Parameter to_assoc : t -> list (string * t).
  Parameter to_string : t -> string.
End Util.

Parameter pretty_to_string : option bool -> t -> string.
