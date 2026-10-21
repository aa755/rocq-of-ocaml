Require Import RocqOfOCaml.RocqOfOCaml Provider LawSupport Consumer Client.

Definition concrete_result : int := result_value.
Example concrete_result_is_zero : concrete_result = 0%Z.
Proof. vm_compute. reflexivity. Qed.

Definition inline_result : int := Client.inline 12%Z.
Example inline_result_is_zero : inline_result = 0%Z.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions inline_result.

Fail Definition unjustified_loop : Run.FArgs :=
  Run.Build_FArgs Provider.Identity.
Fail Definition fabricated_law : Law False := ltac:(typeclasses eauto).

Print Assumptions Run.run.
Print Assumptions concrete_result.
Definition cross_file_result : int := Client.run 12%Z.
Example cross_file_result_is_zero : cross_file_result = 0%Z.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions cross_file_result.

Example direct_result_is_zero : Client.direct 12%Z = 0%Z.
Proof. vm_compute. reflexivity. Qed.
Example local_direct_result_is_zero : Client.local_direct 12%Z = 0%Z.
Proof. vm_compute. reflexivity. Qed.

Example inline_state_result_is_zero : Client.inline_state 12%Z = 0%Z.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions Client.inline_state.
