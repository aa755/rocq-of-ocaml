Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.Bigstring.

(** Bigarrays are owned by external cryptographic libraries in the Monad VM.
    Their representation and allocation effects are outside the pure Gallina
    model.  The VM reads bytes from [Bigstring.t], so the FFI boundary has
    that concrete carrier and byte result rather than an arbitrary result
    type. *)
Module Array1.
  Parameter get : Bigstring.t -> int -> ascii.
End Array1.
