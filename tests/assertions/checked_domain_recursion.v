Require Import Tests.checked_domain_recursion.
From Stdlib Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Example length_in_domain : checked_domain_recursion.length [1; 2] = 2.
Proof. vm_compute. reflexivity. Qed.

Example length_outside_domain : checked_domain_recursion.length [1; 2; 3] = 99.
Proof. vm_compute. reflexivity. Qed.

Example local_length_in_domain : local_length [1; 2] = 2.
Proof. vm_compute. reflexivity. Qed.

Example local_length_outside_domain : local_length [1; 2; 3] = 99.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions checked_domain_recursion.length.
Print Assumptions local_length.
