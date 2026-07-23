Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.

(** Bigarrays are owned by external cryptographic libraries in the Monad VM.
    Their representation and allocation effects are outside the pure Gallina
    model.  This polymorphic read is therefore an explicit FFI boundary. *)
Module Array1.
  Parameter get : forall {array element : Set}, array -> int -> element.
End Array1.
