(** In-bounds string slices are independent of exceptional fallback values. *)

From Stdlib Require Import String ZArith Lia.
Require Import RocqOfOCaml.OCamlString.

Local Open Scope Z_scope.

Lemma substring_length_in_bounds (bytes : string) (start count : nat) :
  (start + count <= Strings.String.length bytes)%nat ->
  Strings.String.length (substring start count bytes) = count.
Proof.
  revert start count.
  induction bytes as [|char bytes IH];
    intros [|start] [|count] Hbound; cbn in *; try lia.
  all: rewrite IH by lia; reflexivity.
Qed.

Lemma sub_in_bounds `{RocqOfOCaml.Basics.Unreachable string}
    (bytes : string) (start count : Z) :
  0 <= start -> 0 <= count -> start + count <= OCamlString.length bytes ->
  OCamlString.sub bytes start count =
    substring (Z.to_nat start) (Z.to_nat count) bytes.
Proof.
  intros Hstart Hcount Hbound.
  unfold OCamlString.sub.
  assert (Hvalid : andb (Z.leb 0 start)
    (andb (Z.leb 0 count)
      (Z.leb (start + count) (OCamlString.length bytes))) = true).
  { repeat rewrite Bool.andb_true_iff.
    repeat split; apply Z.leb_le; lia. }
  rewrite Hvalid; reflexivity.
Qed.

Lemma sub_length_in_bounds `{RocqOfOCaml.Basics.Unreachable string}
    (bytes : string) (start count : Z) :
  0 <= start -> 0 <= count -> start + count <= OCamlString.length bytes ->
  OCamlString.length (OCamlString.sub bytes start count) = count.
Proof.
  intros Hstart Hcount Hbound.
  rewrite sub_in_bounds by assumption.
  unfold OCamlString.length in *.
  rewrite substring_length_in_bounds by lia.
  lia.
Qed.

Lemma sub_fallback_irrelevant
    (left right : RocqOfOCaml.Basics.Unreachable string)
    (bytes : string) (start count : Z) :
  0 <= start -> 0 <= count -> start + count <= OCamlString.length bytes ->
  @OCamlString.sub left bytes start count =
    @OCamlString.sub right bytes start count.
Proof.
  intros Hstart Hcount Hbound.
  rewrite !sub_in_bounds by assumption.
  reflexivity.
Qed.
