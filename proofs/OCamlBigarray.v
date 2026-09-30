Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.Bigstring.
Require Import RocqOfOCaml.OCamlString.

(** Bigarrays are owned by external cryptographic libraries in the Monad VM.
    Their representation and allocation effects are outside the pure Gallina
    model.  The VM reads bytes from [Bigstring.t], represented here by a
    string.  An out-of-range read follows the existing typed [Unreachable]
    path, matching the native operation's exception boundary. The upper
    bound is checked before [OCamlString.get] so extraction need not build a
    Peano index for a huge invalid [Z]. *)
Module Array1.
  Definition get `{Unreachable ascii}
      (value : Bigstring.t) (index : int) : ascii :=
    if Z.leb (OCamlString.length value) index
    then unreachable
    else OCamlString.get value index.
End Array1.
