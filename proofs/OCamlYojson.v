Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.

(** [Yojson.Safe.t] is an OCaml polymorphic variant, represented by the same
    generic [Variant.t] carrier used by translated pattern matches.

    Parsing, field projection, and rendering belong to the fixture/serialization
    layer rather than the VM transition function, so those library operations
    remain explicit external services. *)

Definition t : Set := Variant.t.

Module Util.
  Parameter member : string -> t -> t.
  Parameter to_assoc : t -> list (string * t).
  Parameter to_string : t -> string.
End Util.

Parameter pretty_to_string : option bool -> t -> string.
