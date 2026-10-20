From Stdlib Require Import ZArith String Lia.
Require Import RocqOfOCaml.OCamlZ.

Local Open Scope Z_scope.

(** The canonical encoder is the significant-byte prefix of native Zarith
    serialization. These statements quantify over every Gallina integer;
    they do not assume an allocation limit or use a native extraction shim. *)
Lemma to_bits_bytes_length count value :
  String.length (to_bits_bytes count value) = count.
Proof. revert value. induction count; intros; cbn; congruence. Qed.

Lemma to_bits_bytes_prefix small large value :
  (small <= large)%nat ->
  String.substring 0 small (to_bits_bytes large value) =
    to_bits_bytes small value.
Proof.
  revert large value. induction small; intros [|large] value Hle;
    cbn; try reflexivity; try lia.
  f_equal. apply IHsmall. lia.
Qed.

Lemma significant_byte_count_fits value :
  (Z.to_nat ((numbits value + 7) / 8) <= 8 * limb_count value)%nat.
Proof.
  assert (Hbits : 0 <= numbits value).
  { unfold numbits. destruct (Z.eqb value 0); [lia|].
    pose proof (Z.log2_nonneg (Z.abs value)). lia. }
  pose proof (Z.div_mod (numbits value + 7) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (numbits value + 7) 8 ltac:(lia)).
  pose proof (Z.div_mod (numbits value + 63) 64 ltac:(lia)).
  pose proof (Z.mod_pos_bound (numbits value + 63) 64 ltac:(lia)).
  unfold limb_count. apply Nat2Z.inj_le.
  rewrite Nat2Z.inj_mul, !Z2Nat.id by (apply Z.div_pos; lia).
  change ((numbits value + 7) / 8 <= 8 * ((numbits value + 63) / 64)). lia.
Qed.

Lemma numbits_abs value : numbits (Z.abs value) = numbits value.
Proof. destruct value; reflexivity. Qed.

Theorem minimal_is_native_prefix value :
  String.substring 0 (String.length (to_bits_minimal value)) (to_bits value) =
    to_bits_minimal value.
Proof.
  unfold to_bits_minimal, to_bits.
  rewrite to_bits_bytes_length, numbits_abs.
  apply to_bits_bytes_prefix, significant_byte_count_fits.
Qed.

Theorem native_byte_length value :
  String.length (to_bits value) = (8 * limb_count value)%nat.
Proof. apply to_bits_bytes_length. Qed.

Print Assumptions minimal_is_native_prefix.
