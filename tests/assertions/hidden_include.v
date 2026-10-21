Require Import Tests.hidden_include.
From Stdlib Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Example hidden_body_is_executable : generated_result = 42.
Proof. vm_compute. reflexivity. Qed.

Example earlier_shadowed_reference : previous = 1.
Proof. reflexivity. Qed.

Example final_shadowed_reference : shadowed = 2.
Proof. reflexivity. Qed.

Example constrained_hidden_body : constrained_result = 42.
Proof. vm_compute. reflexivity. Qed.

Example recursive_hidden_equal :
  equal (Node [Leaf 1; Node [Leaf 2]]) (Node [Leaf 1; Node [Leaf 2]]) = true.
Proof. vm_compute. reflexivity. Qed.

Example recursive_hidden_unequal :
  equal (Node [Leaf 1; Node [Leaf 2]]) (Node [Leaf 1; Node [Leaf 3]]) = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions generated.
Print Assumptions equal.
