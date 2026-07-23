Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.

(** Compatibility surface for OCaml's typed, variadic [Format] API.

    The existing rocq-of-ocaml model erases the indices of OCaml's format
    GADT, so the result function cannot be reconstructed in Gallina from that
    erased syntax alone.  Formatting is consequently an explicit trusted
    runtime service.  The VM transition audit must separately account for
    formatted strings that influence execution rather than diagnostics. *)

Parameter sprintf :
  forall {a : Set}, CamlinternalFormatBasics.format6_gadt -> a.

Parameter printf :
  forall {a : Set}, CamlinternalFormatBasics.format6_gadt -> a.

Parameter eprintf :
  forall {a : Set}, CamlinternalFormatBasics.format6_gadt -> a.

Definition print_string (_ : string) : unit := tt.

Definition print_flush (_ : unit) : unit := tt.
