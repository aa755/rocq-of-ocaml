Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.OCamlMachineInt.

(** OCaml [int] on a 64-bit platform, represented by signed [Z] values. *)
Module Width <: OCamlMachineInt.Width.
  Definition bits := 63%Z.
End Width.
Include OCamlMachineInt.Make Width.

From Stdlib Require Import Lia.
Local Open Scope Z_scope.

(** These lemmas let client proofs recover ordinary arithmetic when no wrap
    occurs, without incorrectly replacing all native arithmetic by [Z.add]. *)
Lemma repr_range value : min_int <= repr value <= max_int.
Proof.
  unfold repr, OCamlZ.signed_repr, min_int, max_int, sign_bit, size, Width.bits.
  change (-4611686018427387904 <=
    (let u := value mod 9223372036854775808 in
     if 4611686018427387904 <=? u then u - 9223372036854775808 else u)
    <= 4611686018427387903).
  pose proof (Z.mod_pos_bound value 9223372036854775808 ltac:(lia)).
  cbn zeta.
  destruct (Z.leb_spec 4611686018427387904 (value mod 9223372036854775808)); lia.
Qed.

Lemma repr_small value : min_int <= value <= max_int -> repr value = value.
Proof.
  unfold repr, OCamlZ.signed_repr, min_int, max_int, sign_bit, size, Width.bits.
  change (-4611686018427387904 <= value <= 4611686018427387903 ->
    (let u := value mod 9223372036854775808 in
     if 4611686018427387904 <=? u then u - 9223372036854775808 else u) = value).
  intros Hrange.
  cbn zeta.
  destruct (Z_lt_ge_dec value 0) as [Hnegative | Hnonnegative].
  - assert (Hmod : value mod 9223372036854775808 = value + 9223372036854775808).
    { symmetry. apply Z.mod_unique with (q := -1); lia. }
    rewrite Hmod. destruct (Z.leb_spec 4611686018427387904
      (value + 9223372036854775808)); lia.
  - rewrite Z.mod_small by lia.
    destruct (Z.leb_spec 4611686018427387904 value); lia.
Qed.

Lemma add_no_overflow left right :
  min_int <= left + right <= max_int -> add left right = left + right.
Proof. apply repr_small. Qed.
