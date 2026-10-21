From Stdlib Require Import List ZArith Strings.Ascii.
Require Import Tests.byte_literals.
Require Import RocqOfOCaml.OCamlChar.

Example every_literal_preserves_its_byte :
  List.map OCamlChar.code all_bytes = List.map Z.of_nat (List.seq 0 256).
Proof. vm_compute. reflexivity. Qed.

Example high_byte_patterns :
  classify "128"%char = 1%Z /\ classify "255"%char = 2%Z /\
  classify "127"%char = 0%Z.
Proof. vm_compute. repeat split. Qed.

Print Assumptions every_literal_preserves_its_byte.
