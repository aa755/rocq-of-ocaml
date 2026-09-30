From Stdlib Require Import Ascii String ZArith Lia.
Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.Bigstring.
Require Import RocqOfOCaml.OCamlBigarray.
Require Import RocqOfOCaml.Libsecp256k1.

(** The upper-bound guard prevents the default extraction from converting a
    huge invalid [Z] index into a Peano [nat]. It preserves the result and
    exceptional branch of [OCamlString.get] for every index. *)
Lemma string_get_out_of_bounds (value : string) (index : nat) :
  (Strings.String.length value <= index)%nat ->
  Strings.String.get index value = None.
Proof.
  revert index.
  induction value as [|character rest IH]; intros [|index] bounded;
    cbn in *; try reflexivity; try lia.
  apply IH. lia.
Qed.

Lemma bigarray_get_is_string_get `{Unreachable ascii}
    (value : Bigstring.t) (index : int) :
  OCamlBigarray.Array1.get value index = OCamlString.get value index.
Proof.
  unfold OCamlBigarray.Array1.get.
  destruct (Z.leb (OCamlString.length value) index) eqn:too_large;
    [|reflexivity].
  apply Z.leb_le in too_large.
  unfold OCamlString.get.
  assert (index <? 0 = false)%Z as nonnegative.
  { apply Z.ltb_ge. unfold OCamlString.length in too_large. lia. }
  rewrite nonnegative.
  rewrite string_get_out_of_bounds.
  - reflexivity.
  - unfold OCamlString.length in too_large. lia.
Qed.

Print Assumptions bigarray_get_is_string_get.

Lemma in_bounds_string_get_exists (value : string) (index : nat) :
  (index < Strings.String.length value)%nat ->
  exists character, Strings.String.get index value = Some character.
Proof.
  revert index.
  induction value as [|character rest IH]; intros [|index] bounded;
    cbn in *; try lia.
  - eexists. reflexivity.
  - apply IH. lia.
Qed.

Lemma bigarray_get_in_bounds_fallback_irrelevant
    (left right : Unreachable ascii)
    (value : Bigstring.t) (index : int) :
  (0 <= index < OCamlString.length value)%Z ->
  @OCamlBigarray.Array1.get left value index =
    @OCamlBigarray.Array1.get right value index.
Proof.
  intro bounded.
  unfold OCamlBigarray.Array1.get.
  assert (OCamlString.length value <=? index = false)%Z as in_bounds.
  { apply Z.leb_gt. lia. }
  rewrite in_bounds.
  unfold OCamlString.get.
  assert (index <? 0 = false)%Z as nonnegative.
  { apply Z.ltb_ge. lia. }
  rewrite nonnegative.
  destruct (Strings.String.get (Z.to_nat index) value)
    as [character|] eqn:chosen; [reflexivity|].
  destruct (in_bounds_string_get_exists value (Z.to_nat index))
    as [character exists_at_index].
  { unfold OCamlString.length in bounded. lia. }
  rewrite chosen in exists_at_index. discriminate.
Qed.

Print Assumptions bigarray_get_in_bounds_fallback_irrelevant.

Lemma uncompressed_public_key_read_fallback_irrelevant
    (left right : Unreachable ascii)
    (context : Libsecp256k1.External.Context.t)
    (key : Libsecp256k1.External.Key.t
      Libsecp256k1.External.Key.public)
    (index : int) :
  (0 <= index < 64)%Z ->
  @OCamlBigarray.Array1.get left
    (Libsecp256k1.External.Key.to_bytes (Some false) context key)
    (index + 1)%Z =
  @OCamlBigarray.Array1.get right
    (Libsecp256k1.External.Key.to_bytes (Some false) context key)
    (index + 1)%Z.
Proof.
  intro bounded.
  apply bigarray_get_in_bounds_fallback_irrelevant.
  pose proof
    (Libsecp256k1.External.Key.to_bytes_uncompressed_length context key)
    as key_length.
  lia.
Qed.

Print Assumptions uncompressed_public_key_read_fallback_irrelevant.

Lemma init_nat_ext (count : nat) (start : int)
    (left right : int -> ascii) :
  (forall offset, (0 <= offset < Z.of_nat count)%Z ->
    left (start + offset)%Z = right (start + offset)%Z) ->
  OCamlString.init_nat count start left =
    OCamlString.init_nat count start right.
Proof.
  revert start.
  induction count as [|count IH]; intros start equal_at; cbn;
    [reflexivity|].
  f_equal.
  - replace start with (start + 0)%Z at 1 by lia.
    replace start with (start + 0)%Z at 2 by lia.
    apply equal_at. lia.
  - apply IH. intros offset bounded.
    replace (start + 1 + offset)%Z with (start + (offset + 1))%Z
      by lia.
    apply equal_at. lia.
Qed.

(** This is the 64-byte [Bytes.init] expression inside generated ecrecover.
    It isolates the new Bigarray read site; other uses of the shared
    [Unreachable ascii] binder in ecrecover require separate analysis. *)
Lemma ecrecover_public_key_bytes_fallback_irrelevant
    (left right : Unreachable ascii)
    (string_fallback : Unreachable string)
    (context : Libsecp256k1.External.Context.t)
    (key : Libsecp256k1.External.Key.t
      Libsecp256k1.External.Key.public) :
  @OCamlString.init string_fallback 64%Z
    (fun index => @OCamlBigarray.Array1.get left
      (Libsecp256k1.External.Key.to_bytes (Some false) context key)
      (index + 1)%Z) =
  @OCamlString.init string_fallback 64%Z
    (fun index => @OCamlBigarray.Array1.get right
      (Libsecp256k1.External.Key.to_bytes (Some false) context key)
      (index + 1)%Z).
Proof.
  rewrite !OCamlString.init_matches_structural.
  cbn.
  apply init_nat_ext.
  intros offset bounded.
  apply uncompressed_public_key_read_fallback_irrelevant.
  lia.
Qed.

Print Assumptions ecrecover_public_key_bytes_fallback_irrelevant.
