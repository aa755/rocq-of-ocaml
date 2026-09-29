From Stdlib Require Import ZArith List.
Require Import RocqOfOCaml.OCamlMap RocqOfOCaml.OCamlSeq.
Import ListNotations.
Local Open Scope Z_scope.

Definition int_order : OCamlMap.OrderedType (t := Z) :=
  {| OCamlMap.OrderedType.compare := fun left right => Z.sgn (left - right) |}.

Definition reference_add_seq
    (updates initial : list (Z * Z)) : list (Z * Z) :=
  List.fold_left
    (fun current '(key_value, value) =>
      @OCamlMap.Make.add Z int_order Z key_value value current)
    updates initial.

Definition bulk_add_seq
    (updates initial : list (Z * Z)) : list (Z * Z) :=
  @OCamlMap.Make.add_seq Z int_order Z
    (OCamlSeq.of_list updates) initial.

Example sorted_updates_merge_and_replace :
  bulk_add_seq [(0, 10); (3, 30); (4, 40); (6, 60)]
    (reference_add_seq [(1, 1); (3, 3); (5, 5)] []) =
  reference_add_seq [(0, 10); (3, 30); (4, 40); (6, 60)]
    (reference_add_seq [(1, 1); (3, 3); (5, 5)] []).
Proof. vm_compute. reflexivity. Qed.

Example sorted_updates_from_empty :
  bulk_add_seq [(-2, 1); (0, 2); (1, 3); (8, 4)] [] =
  reference_add_seq [(-2, 1); (0, 2); (1, 3); (8, 4)] [].
Proof. vm_compute. reflexivity. Qed.

Example duplicate_updates_use_reference_path :
  bulk_add_seq [(1, 10); (1, 11); (0, 12); (2, 13)]
    (reference_add_seq [(-1, 1); (1, 2)] []) =
  reference_add_seq [(1, 10); (1, 11); (0, 12); (2, 13)]
    (reference_add_seq [(-1, 1); (1, 2)] []).
Proof. vm_compute. reflexivity. Qed.

Example descending_updates_use_reference_path :
  bulk_add_seq [(3, 30); (2, 20); (-1, 10)]
    (reference_add_seq [(0, 0); (1, 1)] []) =
  reference_add_seq [(3, 30); (2, 20); (-1, 10)]
    (reference_add_seq [(0, 0); (1, 1)] []).
Proof. vm_compute. reflexivity. Qed.
