Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.Bigstring.

(** Typed boundary for the secp256k1 operations used by [Crypto.ecrecover].

    The opaque carriers retain the distinctions made by the OCaml API.  The
    operations remain parameters because their implementation is C code and
    is outside this pure Gallina translation. *)
Module External.
  Module Context.
    Parameter t : Set.

    Parameter create : option bool -> option bool -> unit -> t.
  End Context.

  Module Key.
    Parameter public : Set.
    Parameter t : Set -> Set.

    Parameter to_bytes :
      option bool -> Context.t -> forall {kind : Set}, t kind -> Bigstring.t.
  End Key.

  Module Sign.
    Parameter recoverable : Set.
    Parameter t : Set -> Set.

    Parameter recoverable_bytes : int.

    Parameter read_recoverable :
      Context.t -> Bigstring.t -> sum (t recoverable) string.

    Parameter recover :
      Context.t -> t recoverable -> Bigstring.t ->
      sum (Key.t Key.public) string.
  End Sign.
End External.
