From Stdlib Require Import ZArith List Bool.
Require Import RocqOfOCaml.OCamlMap RocqOfOCaml.OCamlSeq.
Import ListNotations.
Local Open Scope Z_scope.

Definition int_order : OCamlMap.OrderedType (t := Z) :=
  {| OCamlMap.OrderedType.compare := fun left right => left - right |}.

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

Lemma collect_sequence_reverses_into_accumulator {A : Set}
    (values : list A) (accumulator : list A) :
  OCamlSeq.fold_left
    (fun reversed value => value :: reversed)
    accumulator (OCamlSeq.of_list values) =
  List.rev_append values accumulator.
Proof.
  revert accumulator.
  induction values as [|value tail IH]; intro accumulator; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma collect_sequence_restores_list {A : Set} (values : list A) :
  List.rev
    (OCamlSeq.fold_left
      (fun reversed value => value :: reversed)
      [] (OCamlSeq.of_list values)) = values.
Proof.
  rewrite collect_sequence_reverses_into_accumulator.
  rewrite List.rev_append_rev.
  rewrite List.app_nil_r.
  apply List.rev_involutive.
Qed.

Lemma unsorted_updates_use_original_fold
    (updates initial : list (Z * Z)) :
  @OCamlMap.Make.strictly_increasing Z int_order Z updates = false ->
  bulk_add_seq updates initial = reference_add_seq updates initial.
Proof.
  intro not_increasing.
  unfold bulk_add_seq, OCamlMap.Make.add_seq.
  rewrite collect_sequence_restores_list.
  rewrite not_increasing.
  reflexivity.
Qed.

Lemma fold_sorted_updates_into_empty
    (updates reversed : list (Z * Z)) :
  List.fold_left
    (@OCamlMap.Make.add_sorted_entry Z int_order Z)
    updates ([], reversed) =
  ([], List.rev_append updates reversed).
Proof.
  revert reversed.
  induction updates as [|binding tail IH]; intro reversed; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma merge_sorted_updates_into_empty (updates : list (Z * Z)) :
  @OCamlMap.Make.merge_sorted_updates Z int_order Z updates [] = updates.
Proof.
  unfold OCamlMap.Make.merge_sorted_updates.
  rewrite fold_sorted_updates_into_empty.
  simpl.
  rewrite !List.rev_append_rev.
  rewrite !List.app_nil_r.
  apply List.rev_involutive.
Qed.

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

Definition sample_bindings : list (Z * Z) :=
  [(-1, 11); (0, 0); (0, 99); (1, 1); (2, 2)].

Fixpoint lists_exact (count : nat) : list (list (Z * Z)) :=
  match count with
  | Datatypes.O => [[]]
  | Datatypes.S previous =>
      List.concat
        (List.map
          (fun binding =>
            List.map (fun values => binding :: values) (lists_exact previous))
          sample_bindings)
  end.

Definition initial_cases :=
  lists_exact 0 ++ lists_exact 1 ++ lists_exact 2.
Definition update_cases :=
  initial_cases ++ lists_exact 3.

Definition binding_eqb (left right : Z * Z) : bool :=
  Z.eqb (fst left) (fst right) && Z.eqb (snd left) (snd right).

Fixpoint bindings_eqb (left right : list (Z * Z)) : bool :=
  match left, right with
  | [], [] => true
  | left_binding :: left_tail, right_binding :: right_tail =>
      binding_eqb left_binding right_binding &&
        bindings_eqb left_tail right_tail
  | _, _ => false
  end.

Definition matches_reference
    (initial_updates updates : list (Z * Z)) : bool :=
  let initial := reference_add_seq initial_updates [] in
  bindings_eqb
    (bulk_add_seq updates initial)
    (reference_add_seq updates initial).

Definition finite_comparison : bool :=
  List.forallb
    (fun initial_updates =>
      List.forallb (matches_reference initial_updates) update_cases)
    initial_cases.

Example finite_comparison_holds : finite_comparison = true.
Proof. vm_compute. reflexivity. Qed.
