From Stdlib Require Import ZArith List Bool Lia.
Require Import RocqOfOCaml.OCamlMap RocqOfOCaml.OCamlSeq
  RocqOfOCaml.OCamlInt.
Import ListNotations.
Local Open Scope Z_scope.

Definition int_order : OCamlMap.OrderedType (t := Z) :=
  {| OCamlMap.OrderedType.compare := OCamlInt.compare |}.

Lemma int_key_before (left right : Z) :
  @OCamlMap.Make.key_before Z int_order left right = Z.ltb left right.
Proof.
  unfold OCamlMap.Make.key_before, OCamlMap.Make.key_compare,
    int_order, OCamlInt.compare.
  simpl.
  destruct (Z.compare left right) eqn:order; simpl.
  - apply Z.compare_eq_iff in order. subst.
    symmetry. apply Z.ltb_ge. lia.
  - apply Z.compare_lt_iff in order. symmetry.
    apply Z.ltb_lt. exact order.
  - apply Z.compare_gt_iff in order. symmetry.
    apply Z.ltb_ge. lia.
Qed.

Lemma int_key_equal (left right : Z) :
  @OCamlMap.Make.key_equal Z int_order left right = Z.eqb left right.
Proof.
  unfold OCamlMap.Make.key_equal, OCamlMap.Make.key_compare,
    int_order, OCamlInt.compare.
  simpl.
  destruct (Z.compare left right) eqn:order; simpl.
  - apply Z.compare_eq_iff in order. subst. rewrite Z.eqb_refl.
    reflexivity.
  - pose proof (proj1 (Z.compare_lt_iff left right) order) as less.
    assert (different : left <> right) by lia.
    apply Z.eqb_neq in different. rewrite different. reflexivity.
  - pose proof (proj1 (Z.compare_gt_iff left right) order) as greater.
    assert (different : left <> right) by lia.
    apply Z.eqb_neq in different. rewrite different. reflexivity.
Qed.

Definition add_int (key_value value : Z) (map : list (Z * Z)) :
    list (Z * Z) :=
  @OCamlMap.Make.add Z int_order Z key_value value map.

Lemma add_after_lower_prefix
    (key_value value : Z) (prefix remaining : list (Z * Z)) :
  Forall (fun binding => fst binding < key_value) prefix ->
  add_int key_value value (prefix ++ remaining) =
    prefix ++ add_int key_value value remaining.
Proof.
  induction prefix as [|[existing_key existing_value] tail IH];
    intro lower_prefix; simpl.
  - reflexivity.
  - inversion lower_prefix as [|? ? lower_head lower_tail]; subst.
    unfold add_int at 1.
    cbn [OCamlMap.Make.add].
    rewrite int_key_before, int_key_equal.
    assert (Z.ltb key_value existing_key = false) as not_before
      by (apply Z.ltb_ge; simpl in lower_head; lia).
    assert (Z.eqb key_value existing_key = false) as not_equal
      by (apply Z.eqb_neq; simpl in lower_head; lia).
    rewrite not_before, not_equal.
    f_equal. apply IH. exact lower_tail.
Qed.

Lemma sorted_entry_matches_add
    (key_value value : Z) (remaining reversed : list (Z * Z)) :
  Forall (fun binding => fst binding < key_value) reversed ->
  let '(next_remaining, next_reversed) :=
    @OCamlMap.Make.add_sorted_entry Z int_order Z
      (remaining, reversed) (key_value, value) in
  List.rev_append next_reversed next_remaining =
    add_int key_value value (List.rev_append reversed remaining).
Proof.
  revert reversed.
  induction remaining as [|[existing_key existing_value] tail IH];
    intros reversed lower_prefix.
  - cbn [OCamlMap.Make.add_sorted_entry OCamlMap.Make.collect_before].
    rewrite !List.rev_append_rev, !List.app_nil_r.
    simpl.
    assert (lower_reversed :
      Forall (fun binding => fst binding < key_value) (rev reversed))
      by (apply List.Forall_rev; exact lower_prefix).
    pose proof
      (add_after_lower_prefix key_value value (rev reversed) []
        lower_reversed) as add_end.
    rewrite List.app_nil_r in add_end.
    cbn [app add_int OCamlMap.Make.add] in add_end.
    symmetry. exact add_end.
  - cbn [OCamlMap.Make.add_sorted_entry OCamlMap.Make.collect_before].
    rewrite int_key_before.
    destruct (Z.ltb existing_key key_value) eqn:existing_before.
    + cbn [fst]. rewrite existing_before.
      apply IH.
      constructor.
      * cbn [fst]. apply Z.ltb_lt in existing_before.
        exact existing_before.
      * exact lower_prefix.
    + cbn [fst]. rewrite existing_before.
      rewrite int_key_equal.
      assert (lower_reversed :
        Forall (fun binding => fst binding < key_value) (rev reversed))
        by (apply List.Forall_rev; exact lower_prefix).
      rewrite !List.rev_append_rev.
      rewrite add_after_lower_prefix by exact lower_reversed.
      destruct (Z.eqb key_value existing_key) eqn:same_key.
      * apply Z.eqb_eq in same_key. subst existing_key.
        rewrite List.rev_append_rev.
        cbn [rev add_int OCamlMap.Make.add].
        rewrite int_key_before, int_key_equal.
        rewrite Z.ltb_irrefl, Z.eqb_refl.
        rewrite <- List.app_assoc. reflexivity.
      * apply Z.eqb_neq in same_key.
        apply Z.ltb_ge in existing_before.
        rewrite List.rev_append_rev.
        cbn [rev add_int OCamlMap.Make.add].
        rewrite int_key_before.
        assert (Z.ltb key_value existing_key = true) as key_before
          by (apply Z.ltb_lt; lia).
        rewrite key_before.
        rewrite <- List.app_assoc. reflexivity.
Qed.

Lemma sorted_entry_prefix_below_later
    (key_value value later : Z)
    (remaining reversed : list (Z * Z)) :
  key_value < later ->
  Forall (fun binding => fst binding < key_value) reversed ->
  let '(_, next_reversed) :=
    @OCamlMap.Make.add_sorted_entry Z int_order Z
      (remaining, reversed) (key_value, value) in
  Forall (fun binding => fst binding < later) next_reversed.
Proof.
  revert reversed.
  induction remaining as [|[existing_key existing_value] tail IH];
    intros reversed key_below_later lower_prefix.
  - cbn [OCamlMap.Make.add_sorted_entry OCamlMap.Make.collect_before].
    constructor.
    + cbn [fst]. exact key_below_later.
    + eapply List.Forall_impl; [|exact lower_prefix].
      intros [binding_key binding_value] lower_key.
      cbn [fst] in *. lia.
  - cbn [OCamlMap.Make.add_sorted_entry OCamlMap.Make.collect_before].
    rewrite int_key_before.
    destruct (Z.ltb existing_key key_value) eqn:existing_before.
    + cbn [fst]. rewrite existing_before.
      apply IH; [exact key_below_later|].
      constructor.
      * cbn [fst]. apply Z.ltb_lt in existing_before.
        exact existing_before.
      * exact lower_prefix.
    + cbn [fst]. rewrite existing_before.
      destruct (@OCamlMap.Make.key_equal Z int_order
        key_value existing_key); constructor.
      all: try (cbn [fst]; exact key_below_later).
      all: eapply List.Forall_impl; [|exact lower_prefix];
        intros [binding_key binding_value] lower_key;
        cbn [fst] in *; lia.
Qed.

Lemma fold_increasing_updates_matches_add
    (updates : list (Z * Z)) :
  forall (previous : Z) (remaining reversed : list (Z * Z)),
    @OCamlMap.Make.strictly_increasing_from Z int_order Z
      previous updates = true ->
    Forall (fun binding => fst binding <= previous) reversed ->
    @OCamlMap.Make.finish_sorted_update_state Z Z
      (List.fold_left
        (@OCamlMap.Make.add_sorted_entry Z int_order Z)
        updates (remaining, reversed)) =
      List.fold_left
        (fun current '(key_value, value) =>
          add_int key_value value current)
        updates (List.rev_append reversed remaining).
Proof.
  induction updates as [|[key_value value] tail IH];
    intros previous remaining reversed increasing bounded.
  - reflexivity.
  - simpl in increasing.
    apply Bool.andb_true_iff in increasing as [previous_before increasing_tail].
    rewrite int_key_before in previous_before.
    apply Z.ltb_lt in previous_before.
    assert (lower_prefix :
      Forall (fun binding => fst binding < key_value) reversed).
    { eapply List.Forall_impl; [|exact bounded].
      intros [binding_key binding_value] lower_key.
      cbn [fst] in *. lia. }
    remember (@OCamlMap.Make.add_sorted_entry Z int_order Z
      (remaining, reversed) (key_value, value)) as next_state
      eqn:next_state_eq.
    destruct next_state as [next_remaining next_reversed].
    pose proof (sorted_entry_matches_add key_value value remaining
      reversed lower_prefix) as step_correct.
    rewrite <- next_state_eq in step_correct.
    cbn in step_correct.
    pose proof (sorted_entry_prefix_below_later key_value value
      (key_value + 1) remaining reversed ltac:(lia) lower_prefix)
      as prefix_below_successor.
    rewrite <- next_state_eq in prefix_below_successor.
    cbn in prefix_below_successor.
    assert (next_bounded :
      Forall (fun binding => fst binding <= key_value) next_reversed).
    { eapply List.Forall_impl; [|exact prefix_below_successor].
      intros [binding_key binding_value] below_successor.
      cbn [fst] in *. lia. }
    specialize (IH key_value next_remaining next_reversed
      increasing_tail next_bounded).
    cbn [List.fold_left].
    rewrite <- next_state_eq.
    rewrite <- step_correct.
    exact IH.
Qed.

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

Theorem int_add_seq_matches_original_fold
    (updates initial : list (Z * Z)) :
  bulk_add_seq updates initial = reference_add_seq updates initial.
Proof.
  unfold bulk_add_seq, OCamlMap.Make.add_seq, reference_add_seq.
  rewrite collect_sequence_restores_list.
  destruct updates as [|[first_key first_value] tail].
  - reflexivity.
  - destruct (@OCamlMap.Make.strictly_increasing Z int_order Z
      ((first_key, first_value) :: tail)) eqn:ordered.
    + assert (from_predecessor :
        @OCamlMap.Make.strictly_increasing_from Z int_order Z
          (first_key - 1) ((first_key, first_value) :: tail) = true).
      { cbn [OCamlMap.Make.strictly_increasing_from].
        rewrite int_key_before.
        assert (Z.ltb (first_key - 1) first_key = true) as before_first
          by (apply Z.ltb_lt; lia).
        rewrite before_first.
        cbn [OCamlMap.Make.strictly_increasing] in ordered.
        exact ordered. }
      unfold OCamlMap.Make.merge_sorted_updates.
      eapply fold_increasing_updates_matches_add.
      * exact from_predecessor.
      * constructor.
    + reflexivity.
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
