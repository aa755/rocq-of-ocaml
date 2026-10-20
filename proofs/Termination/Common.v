(** Reusable facts for ranking recursion by a nonnegative integer
    expression. *)

From Stdlib Require Import ZArith Lia Arith.Wf_nat.

Local Open Scope Z_scope.

(** Negative values are clamped to zero.  A caller proves nonnegativity on
    every recursive edge before using [z_rank_strict]. *)
Definition z_rank (value : Z) : nat := Z.to_nat value.

Lemma z_rank_strict (next current : Z) :
  0 <= next ->
  next < current ->
  (z_rank next < z_rank current)%nat.
Proof.
  intros Hnext Hlt.
  unfold z_rank.
  assert (Hcurrent : 0 <= current) by lia.
  exact ((proj1 (Z2Nat.inj_lt next current Hnext Hcurrent)) Hlt).
Qed.

(** Well-founded recursion on the states satisfying an invariant. Each
    recursive call must prove both preservation and strict decrease. The
    public entry also requires a proof: this helper does not manufacture an
    inhabitant, discard failed obligations, or decide an invalid-input policy. *)
Polymorphic Definition invariant_fix {State Result : Type}
    (valid : State -> Prop) (measure : State -> nat)
    (body : forall state, valid state ->
      (forall next, valid next /\ (measure next < measure state)%nat -> Result) ->
      Result)
    (state : State) (Hvalid : valid state) : Result :=
  @Fix { state : State | valid state }
    (ltof _ (fun state => measure (proj1_sig state)))
    (well_founded_ltof _ (fun state => measure (proj1_sig state)))
    (fun _ => Result)
    (fun state recurse =>
      body (proj1_sig state) (proj2_sig state)
        (fun next certificate =>
          recurse (exist _ next (proj1 certificate)) (proj2 certificate)))
    (exist _ state Hvalid).

Polymorphic Lemma invariant_fix_eq {State Result : Type}
    (valid : State -> Prop) (measure : State -> nat)
    (body : forall state, valid state ->
      (forall next, valid next /\ (measure next < measure state)%nat -> Result) ->
      Result)
    (body_ext : forall state Hvalid recurse1 recurse2,
      (forall next certificate, recurse1 next certificate = recurse2 next certificate) ->
      body state Hvalid recurse1 = body state Hvalid recurse2)
    state Hvalid :
  invariant_fix valid measure body state Hvalid =
  body state Hvalid
    (fun next certificate =>
      invariant_fix valid measure body next (proj1 certificate)).
Proof.
  unfold invariant_fix.
  rewrite Fix_eq.
  - reflexivity.
  - intros. apply body_ext. intros. apply H.
Qed.

(** A clamped next rank may be negative.  It still decreases whenever the
    current integer rank is positive. *)
Lemma z_rank_strict_from_positive (next current : Z) :
  0 < current ->
  next < current ->
  (z_rank next < z_rank current)%nat.
Proof.
  intros Hcurrent Hlt.
  destruct (Z_lt_ge_dec next 0) as [Hnegative | Hnonnegative].
  - assert (Hnext_rank : Z.to_nat next = 0%nat).
    { destruct next; simpl in *; lia. }
    unfold z_rank.
    rewrite Hnext_rank.
    change (Z.to_nat 0 < Z.to_nat current)%nat.
    exact ((proj1 (Z2Nat.inj_lt 0 current ltac:(lia) ltac:(lia))) Hcurrent).
  - apply z_rank_strict; lia.
Qed.
