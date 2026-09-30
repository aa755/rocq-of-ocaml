From Stdlib Require Import ZArith List Bool Lia String.
Require Import RocqOfOCaml.OCamlMap RocqOfOCaml.OCamlSeq
  RocqOfOCaml.OCamlMapBulkInt RocqOfOCaml.OCamlZ
  RocqOfOCaml.OCamlString RocqOfOCaml.Basics.
Import ListNotations.
Local Open Scope Z_scope.

(** [OrderedType] contains only a comparison function.  The fast path in
    [Make.add_seq] is correct when that function behaves as an order; those
    semantic requirements are explicit here rather than axioms of the
    runtime.  Equality may identify distinct key representations. *)
Section OrderedComparator.
  Context {K V : Set} (Ord : OCamlMap.OrderedType (t := K)).

  Definition before : K -> K -> bool :=
    @OCamlMap.Make.key_before K Ord.
  Definition same : K -> K -> bool :=
    @OCamlMap.Make.key_equal K Ord.
  Definition below_or_same (left right : K) : Prop :=
    before left right = true \/ same left right = true.

  Hypothesis before_transitive :
    forall x y z, before x y = true -> before y z = true ->
      before x z = true.
  Hypothesis before_asymmetric :
    forall x y, before x y = true -> before y x = false.
  Hypothesis before_excludes_reverse_same :
    forall x y, before x y = true -> same y x = false.
  Hypothesis same_excludes_before :
    forall x y, same x y = true -> before x y = false.
  Hypothesis reverse_when_distinct :
    forall x y, before x y = false -> same y x = false ->
      before y x = true.
  Hypothesis same_respects_before :
    forall x y z, same x y = true -> before x z = before y z.
  Hypothesis same_reflexive :
    forall x, same x x = true.

  Definition add_model (key_value : K) (value : V)
      (map : list (K * V)) : list (K * V) :=
    @OCamlMap.Make.add K Ord V key_value value map.

  Lemma add_after_lower_prefix
      (key_value : K) (value : V)
      (prefix remaining : list (K * V)) :
    Forall (fun binding => before (fst binding) key_value = true) prefix ->
    add_model key_value value (prefix ++ remaining) =
      prefix ++ add_model key_value value remaining.
  Proof.
    induction prefix as [|[existing_key existing_value] tail IH];
      intro lower_prefix; simpl.
    - reflexivity.
    - inversion lower_prefix as [|? ? lower_head lower_tail]; subst.
      cbn [fst] in lower_head.
      unfold add_model at 1.
      cbn [OCamlMap.Make.add].
      fold before same.
      rewrite (before_asymmetric existing_key key_value lower_head).
      rewrite (before_excludes_reverse_same existing_key key_value
        lower_head).
      f_equal. apply IH. exact lower_tail.
  Qed.

  Lemma sorted_entry_matches_add
      (key_value : K) (value : V)
      (remaining reversed : list (K * V)) :
    Forall (fun binding => before (fst binding) key_value = true) reversed ->
    let '(next_remaining, next_reversed) :=
      @OCamlMap.Make.add_sorted_entry K Ord V
        (remaining, reversed) (key_value, value) in
    List.rev_append next_reversed next_remaining =
      add_model key_value value (List.rev_append reversed remaining).
  Proof.
    revert reversed.
    induction remaining as [|[existing_key existing_value] tail IH];
      intros reversed lower_prefix.
    - cbn [OCamlMap.Make.add_sorted_entry OCamlMap.Make.collect_before].
      rewrite !List.rev_append_rev, !List.app_nil_r.
      simpl.
      assert (lower_reversed :
        Forall (fun binding => before (fst binding) key_value = true)
          (rev reversed))
        by (apply List.Forall_rev; exact lower_prefix).
      pose proof
        (add_after_lower_prefix key_value value (rev reversed) []
          lower_reversed) as add_end.
      rewrite List.app_nil_r in add_end.
      cbn [app add_model OCamlMap.Make.add] in add_end.
      symmetry. exact add_end.
    - cbn [OCamlMap.Make.add_sorted_entry OCamlMap.Make.collect_before].
      fold before same.
      destruct (before existing_key key_value) eqn:existing_before.
      + cbn [fst]. rewrite existing_before.
        apply IH.
        constructor; [exact existing_before|exact lower_prefix].
      + cbn [fst]. rewrite existing_before.
        assert (lower_reversed :
          Forall (fun binding => before (fst binding) key_value = true)
            (rev reversed))
          by (apply List.Forall_rev; exact lower_prefix).
        rewrite !List.rev_append_rev.
        rewrite add_after_lower_prefix by exact lower_reversed.
        destruct (same key_value existing_key) eqn:same_key.
        * rewrite List.rev_append_rev.
          cbn [rev add_model OCamlMap.Make.add].
          fold before same.
          rewrite (same_excludes_before key_value existing_key same_key).
          rewrite same_key.
          rewrite <- List.app_assoc. reflexivity.
        * rewrite List.rev_append_rev.
          cbn [rev add_model OCamlMap.Make.add].
          fold before same.
          rewrite (reverse_when_distinct existing_key key_value
            existing_before same_key).
          rewrite <- List.app_assoc. reflexivity.
  Qed.

  Lemma sorted_entry_prefix_bounded
      (key_value : K) (value : V)
      (remaining reversed : list (K * V)) :
    Forall (fun binding => before (fst binding) key_value = true) reversed ->
    let '(_, next_reversed) :=
      @OCamlMap.Make.add_sorted_entry K Ord V
        (remaining, reversed) (key_value, value) in
    Forall (fun binding => below_or_same (fst binding) key_value)
      next_reversed.
  Proof.
    revert reversed.
    induction remaining as [|[existing_key existing_value] tail IH];
      intros reversed lower_prefix.
    - cbn [OCamlMap.Make.add_sorted_entry OCamlMap.Make.collect_before].
      constructor.
      + right. apply same_reflexive.
      + eapply List.Forall_impl; [|exact lower_prefix].
        intros [binding_key binding_value] lower_key.
        left. exact lower_key.
    - cbn [OCamlMap.Make.add_sorted_entry OCamlMap.Make.collect_before].
      fold before same.
      destruct (before existing_key key_value) eqn:existing_before.
      + cbn [fst]. rewrite existing_before.
        apply IH.
        constructor; [exact existing_before|exact lower_prefix].
      + cbn [fst]. rewrite existing_before.
        destruct (same key_value existing_key).
        * constructor.
          -- right. apply same_reflexive.
          -- eapply List.Forall_impl; [|exact lower_prefix].
             intros [binding_key binding_value] lower_key.
             left. exact lower_key.
        * constructor.
          -- right. apply same_reflexive.
          -- eapply List.Forall_impl; [|exact lower_prefix].
             intros [binding_key binding_value] lower_key.
             left. exact lower_key.
  Qed.

  Lemma fold_increasing_updates_matches_add
      (updates : list (K * V)) :
    forall (previous : K)
      (remaining reversed : list (K * V)),
      @OCamlMap.Make.strictly_increasing_from K Ord V
        previous updates = true ->
      Forall (fun binding => below_or_same (fst binding) previous)
        reversed ->
      @OCamlMap.Make.finish_sorted_update_state K V
        (List.fold_left
          (@OCamlMap.Make.add_sorted_entry K Ord V)
          updates (remaining, reversed)) =
      List.fold_left
        (fun current '(key_value, value) =>
          add_model key_value value current)
        updates (List.rev_append reversed remaining).
  Proof.
    induction updates as [|[key_value value] tail IH];
      intros previous remaining reversed increasing bounded.
    - reflexivity.
    - simpl in increasing.
      apply Bool.andb_true_iff in increasing as
        [previous_before increasing_tail].
      assert (lower_prefix :
        Forall (fun binding => before (fst binding) key_value = true)
          reversed).
      { eapply List.Forall_impl; [|exact bounded].
        intros [binding_key binding_value] lower_key.
        destruct lower_key as [lower_key|same_key].
        - eapply before_transitive; eauto.
        - cbn [fst] in same_key |- *.
          rewrite (same_respects_before binding_key previous key_value
            same_key).
          exact previous_before. }
      remember (@OCamlMap.Make.add_sorted_entry K Ord V
        (remaining, reversed) (key_value, value)) as next_state
        eqn:next_state_eq.
      destruct next_state as [next_remaining next_reversed].
      pose proof (sorted_entry_matches_add key_value value remaining
        reversed lower_prefix) as step_correct.
      rewrite <- next_state_eq in step_correct.
      cbn in step_correct.
      pose proof (sorted_entry_prefix_bounded key_value value
        remaining reversed lower_prefix) as next_bounded.
      rewrite <- next_state_eq in next_bounded.
      cbn in next_bounded.
      specialize (IH key_value next_remaining next_reversed
        increasing_tail next_bounded).
      cbn [List.fold_left].
      rewrite <- next_state_eq.
      rewrite <- step_correct.
      exact IH.
  Qed.

  Definition reference_add_seq
      (updates initial : list (K * V)) : list (K * V) :=
    List.fold_left
      (fun current '(key_value, value) =>
        add_model key_value value current)
      updates initial.

  Definition bulk_add_seq
      (updates initial : list (K * V)) : list (K * V) :=
    @OCamlMap.Make.add_seq K Ord V (OCamlSeq.of_list updates) initial.

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
    List.rev_append
      (OCamlSeq.fold_left
        (fun reversed value => value :: reversed)
        [] (OCamlSeq.of_list values)) [] = values.
  Proof.
    rewrite collect_sequence_reverses_into_accumulator.
    rewrite !List.rev_append_rev.
    rewrite !List.app_nil_r.
    apply List.rev_involutive.
  Qed.

  Theorem ordered_add_seq_matches_original_fold
      (updates initial : list (K * V)) :
    bulk_add_seq updates initial = reference_add_seq updates initial.
  Proof.
    unfold bulk_add_seq, OCamlMap.Make.add_seq, reference_add_seq.
    rewrite collect_sequence_restores_list.
    destruct updates as [|[first_key first_value] tail].
    - reflexivity.
    - destruct (@OCamlMap.Make.strictly_increasing K Ord V
        ((first_key, first_value) :: tail)) eqn:ordered.
      + cbn [OCamlMap.Make.strictly_increasing] in ordered.
        unfold OCamlMap.Make.merge_sorted_updates.
        cbn [List.fold_left].
        destruct (@OCamlMap.Make.add_sorted_entry K Ord V
          (initial, []) (first_key, first_value))
          as [next_remaining next_reversed] eqn:first_state_eq.
        pose proof (sorted_entry_matches_add first_key first_value
          initial [] (Forall_nil _)) as first_correct.
        rewrite first_state_eq in first_correct.
        cbn in first_correct.
        pose proof (sorted_entry_prefix_bounded first_key first_value
          initial [] (Forall_nil _)) as first_bounded.
        rewrite first_state_eq in first_bounded.
        cbn in first_bounded.
        pose proof
          (f_equal
            (fun state =>
              @OCamlMap.Make.finish_sorted_update_state K V
                (List.fold_left
                  (@OCamlMap.Make.add_sorted_entry K Ord V) tail state))
            first_state_eq) as state_transport.
        pose proof
          (fold_increasing_updates_matches_add tail first_key
            next_remaining next_reversed ordered first_bounded)
          as tail_correct.
        etransitivity; [exact state_transport|].
        etransitivity; [exact tail_correct|].
        apply f_equal. exact first_correct.
      + reflexivity.
  Qed.
End OrderedComparator.

(** The VM-memory comparator discharges the generic order obligations. *)
Section IntegerComparator.
  Lemma integer_before (left right : Z) :
    before int_order left right = Z.ltb left right.
  Proof. unfold before. apply int_key_before. Qed.

  Lemma integer_same (left right : Z) :
    same int_order left right = Z.eqb left right.
  Proof. unfold same. apply int_key_equal. Qed.

  Lemma integer_before_transitive :
    forall x y z : Z,
      before int_order x y = true ->
      before int_order y z = true ->
      before int_order x z = true.
  Proof.
    intros x y z xy yz.
    rewrite integer_before in *.
    apply Z.ltb_lt in xy. apply Z.ltb_lt in yz.
    apply Z.ltb_lt. lia.
  Qed.

  Lemma integer_before_asymmetric :
    forall x y : Z,
      before int_order x y = true ->
      before int_order y x = false.
  Proof.
    intros x y xy.
    rewrite integer_before in *.
    apply Z.ltb_lt in xy.
    apply Z.ltb_ge. lia.
  Qed.

  Lemma integer_before_excludes_reverse_same :
    forall x y : Z,
      before int_order x y = true ->
      same int_order y x = false.
  Proof.
    intros x y xy.
    rewrite integer_before in xy.
    rewrite integer_same.
    apply Z.ltb_lt in xy.
    apply Z.eqb_neq. lia.
  Qed.

  Lemma integer_same_excludes_before :
    forall x y : Z,
      same int_order x y = true ->
      before int_order x y = false.
  Proof.
    intros x y equal.
    rewrite integer_same in equal.
    apply Z.eqb_eq in equal. subst.
    rewrite integer_before.
    apply Z.ltb_ge. lia.
  Qed.

  Lemma integer_reverse_when_distinct :
    forall x y : Z,
      before int_order x y = false ->
      same int_order y x = false ->
      before int_order y x = true.
  Proof.
    intros x y not_before not_same.
    rewrite integer_before in *.
    rewrite integer_same in not_same.
    apply Z.ltb_ge in not_before.
    apply Z.eqb_neq in not_same.
    apply Z.ltb_lt. lia.
  Qed.

  Lemma integer_same_respects_before :
    forall x y z : Z,
      same int_order x y = true ->
      before int_order x z = before int_order y z.
  Proof.
    intros x y z equal.
    rewrite integer_same in equal.
    apply Z.eqb_eq in equal. subst. reflexivity.
  Qed.

  Lemma integer_same_reflexive :
    forall x : Z, same int_order x x = true.
  Proof.
    intro x. rewrite integer_same. apply Z.eqb_refl.
  Qed.

  Corollary int_add_seq_from_generic_law {A : Set}
      (updates initial : list (Z * A)) :
    @bulk_add_seq Z A int_order updates initial =
    @reference_add_seq Z A int_order updates initial.
  Proof.
    apply ordered_add_seq_matches_original_fold.
    - exact integer_before_transitive.
    - exact integer_before_asymmetric.
    - exact integer_before_excludes_reverse_same.
    - exact integer_same_excludes_before.
    - exact integer_reverse_when_distinct.
    - exact integer_same_respects_before.
    - exact integer_same_reflexive.
  Qed.
End IntegerComparator.

(** [OCamlZ.compare] and [OCamlInt.compare] have the same Gallina body.
    The generic bulk law therefore applies to the numeric maps as well. *)
Definition z_order : OCamlMap.OrderedType (t := Z) :=
  {| OCamlMap.OrderedType.compare := OCamlZ.compare |}.

Lemma z_order_is_int_order : z_order = int_order.
Proof. reflexivity. Qed.

Corollary z_add_seq_from_generic_law {A : Set}
    (updates initial : list (Z * A)) :
  @bulk_add_seq Z A z_order updates initial =
  @reference_add_seq Z A z_order updates initial.
Proof.
  rewrite z_order_is_int_order.
  apply int_add_seq_from_generic_law.
Qed.

(** Numeric's ordered key maps compare [to_z] images of abstract values.
    The generic theorem permits distinct representations with the same
    numeric image, so no injectivity premise is needed. *)
Definition z_pullback_order {K : Set} (to_z : K -> Z) :
    OCamlMap.OrderedType (t := K) :=
  {| OCamlMap.OrderedType.compare :=
       fun left right => OCamlZ.compare (to_z left) (to_z right) |}.

Corollary z_pullback_add_seq_from_generic_law {K A : Set}
    (to_z : K -> Z) (updates initial : list (K * A)) :
  @bulk_add_seq K A (z_pullback_order to_z) updates initial =
  @reference_add_seq K A (z_pullback_order to_z) updates initial.
Proof.
  apply ordered_add_seq_matches_original_fold.
  - intros x y z xy yz.
    exact (integer_before_transitive (to_z x) (to_z y) (to_z z) xy yz).
  - intros x y xy.
    exact (integer_before_asymmetric (to_z x) (to_z y) xy).
  - intros x y xy.
    exact (integer_before_excludes_reverse_same (to_z x) (to_z y) xy).
  - intros x y equal.
    exact (integer_same_excludes_before (to_z x) (to_z y) equal).
  - intros x y not_before not_same.
    exact (integer_reverse_when_distinct (to_z x) (to_z y)
      not_before not_same).
  - intros x y z equal.
    exact (integer_same_respects_before (to_z x) (to_z y) (to_z z)
      equal).
  - intro x. exact (integer_same_reflexive (to_z x)).
Qed.

Definition string_order : OCamlMap.OrderedType (t := string) :=
  {| OCamlMap.OrderedType.compare := OCamlString.compare |}.

Lemma string_ltb_irreflexive (value : string) :
  Basics.String.ltb value value = false.
Proof.
  destruct (Basics.String.ltb_spec value value) as [less|not_less].
  - exfalso. exact (@Basics.String.Lt.irreflexivity value less).
  - reflexivity.
Qed.

Lemma string_key_before (left right : string) :
  before string_order left right = Basics.String.ltb left right.
Proof.
  unfold before, OCamlMap.Make.key_before, OCamlMap.Make.key_compare,
    string_order.
  cbn [OCamlMap.OrderedType.compare].
  rewrite OCamlString.compare_matches_structural.
  unfold OCamlString.compare_structural.
  simpl.
  destruct (Strings.String.eqb left right) eqn:equal.
  - apply Strings.String.eqb_eq in equal. subst.
    rewrite string_ltb_irreflexive. reflexivity.
  - destruct (Basics.String.ltb left right); reflexivity.
Qed.

Lemma string_key_same (left right : string) :
  same string_order left right = Strings.String.eqb left right.
Proof.
  unfold same, OCamlMap.Make.key_equal, OCamlMap.Make.key_compare,
    string_order.
  cbn [OCamlMap.OrderedType.compare].
  rewrite OCamlString.compare_matches_structural.
  unfold OCamlString.compare_structural.
  simpl.
  destruct (Strings.String.eqb left right); simpl; [reflexivity|].
  destruct (Basics.String.ltb left right); reflexivity.
Qed.

Lemma string_ltb_true_lt (left right : string) :
  Basics.String.ltb left right = true -> Basics.String.Lt.t left right.
Proof.
  intro ordered.
  destruct (Basics.String.ltb_spec left right) as [less|not_less].
  - exact less.
  - discriminate.
Qed.

Lemma string_lt_ltb_true (left right : string) :
  Basics.String.Lt.t left right -> Basics.String.ltb left right = true.
Proof.
  intro less.
  destruct (Basics.String.ltb_spec left right) as [ordered|not_ordered].
  - reflexivity.
  - contradiction.
Qed.

Lemma string_before_transitive :
  forall x y z : string,
    before string_order x y = true ->
    before string_order y z = true ->
    before string_order x z = true.
Proof.
  intros x y z xy yz.
  rewrite string_key_before in *.
  apply string_lt_ltb_true.
  eapply Basics.String.Lt.transitivity.
  - apply string_ltb_true_lt. exact xy.
  - apply string_ltb_true_lt. exact yz.
Qed.

Lemma string_before_asymmetric :
  forall x y : string,
    before string_order x y = true ->
    before string_order y x = false.
Proof.
  intros x y xy.
  rewrite string_key_before in *.
  destruct (Basics.String.ltb y x) eqn:yx; [|reflexivity].
  exfalso.
  apply (@Basics.String.Lt.irreflexivity x).
  eapply Basics.String.Lt.transitivity.
  - apply string_ltb_true_lt. exact xy.
  - apply string_ltb_true_lt. exact yx.
Qed.

Lemma string_before_excludes_reverse_same :
  forall x y : string,
    before string_order x y = true ->
    same string_order y x = false.
Proof.
  intros x y xy.
  rewrite string_key_before in xy.
  rewrite string_key_same.
  destruct (Strings.String.eqb y x) eqn:equal; [|reflexivity].
  apply Strings.String.eqb_eq in equal. subst.
  rewrite string_ltb_irreflexive in xy. discriminate.
Qed.

Lemma string_same_excludes_before :
  forall x y : string,
    same string_order x y = true ->
    before string_order x y = false.
Proof.
  intros x y equal.
  rewrite string_key_same in equal.
  apply Strings.String.eqb_eq in equal. subst.
  rewrite string_key_before. apply string_ltb_irreflexive.
Qed.

Lemma string_reverse_when_distinct :
  forall x y : string,
    before string_order x y = false ->
    same string_order y x = false ->
    before string_order y x = true.
Proof.
  intros x y not_before not_same.
  rewrite string_key_before in *.
  rewrite string_key_same in not_same.
  assert (different : Strings.String.eqb x y = false).
  { destruct (Strings.String.eqb x y) eqn:equal; [|reflexivity].
    apply Strings.String.eqb_eq in equal. subst.
    rewrite Strings.String.eqb_refl in not_same. discriminate. }
  exact (Basics.String.ltb_or_eqb_or_gtb x y not_before different).
Qed.

Lemma string_same_respects_before :
  forall x y z : string,
    same string_order x y = true ->
    before string_order x z = before string_order y z.
Proof.
  intros x y z equal.
  rewrite string_key_same in equal.
  apply Strings.String.eqb_eq in equal. subst. reflexivity.
Qed.

Lemma string_same_reflexive :
  forall x : string, same string_order x x = true.
Proof.
  intro x. rewrite string_key_same. apply Strings.String.eqb_refl.
Qed.

Corollary string_add_seq_from_generic_law {A : Set}
    (updates initial : list (string * A)) :
  @bulk_add_seq string A string_order updates initial =
  @reference_add_seq string A string_order updates initial.
Proof.
  apply ordered_add_seq_matches_original_fold.
  - exact string_before_transitive.
  - exact string_before_asymmetric.
  - exact string_before_excludes_reverse_same.
  - exact string_same_excludes_before.
  - exact string_reverse_when_distinct.
  - exact string_same_respects_before.
  - exact string_same_reflexive.
Qed.

(** The raw [OrderedType] record cannot support an unconditional theorem:
    this comparison incorrectly puts either distinct key before the other. *)
Definition symmetric_before : OCamlMap.OrderedType (t := Z) :=
  {| OCamlMap.OrderedType.compare :=
       fun left right => if Z.eqb left right then 0 else -1 |}.

Example unqualified_add_seq_law_is_false :
  @bulk_add_seq Z Z symmetric_before [(1, 10); (2, 20)] [] <>
  @reference_add_seq Z Z symmetric_before [(1, 10); (2, 20)] [].
Proof. vm_compute. discriminate. Qed.
