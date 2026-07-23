Require Export OCamlSeqGenerated.
From Stdlib Require Import List.

Import ListNotations.

Include RocqOfOCaml.OCamlSeqGenerated.

(** Compatibility extension over the generated OCaml 5.4 [Stdlib.Seq].

    [of_list] is not part of OCaml's [Seq] module.  The executable [Map] and
    [Set] compatibility models use it to expose their finite association-list
    representations as sequences. *)
Fixpoint of_list_node {A : Set} (values : list A) : node A :=
  match values with
  | [] => Nil
  | head :: tail => Cons head (fun _ => of_list_node tail)
  end.

Definition of_list {A : Set} (values : list A) : t A :=
  fun _ => of_list_node values.
