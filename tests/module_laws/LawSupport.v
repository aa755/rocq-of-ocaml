From Stdlib Require Import Lia ZArith.
Require Import RocqOfOCaml.RocqOfOCaml Provider.

Definition decreases (s : Provider.STEP) : Prop :=
  forall n, (0 < n)%Z ->
    (Z.to_nat (Provider.STEP.step s n) < Z.to_nat n)%nat.

Definition step_decreases (step : Z -> Z) : Prop :=
  forall n, (0 < n)%Z -> (Z.to_nat (step n) < Z.to_nat n)%nat.

Definition state_resets {State : Type}
    (step : State -> State) (gas : State -> Z) : Prop :=
  forall s, gas (step s) = 0%Z.

#[global] Instance reset_state_law :
    Law (state_resets (Provider.STEP.step Provider.Reset) (fun n => n)).
Proof. constructor. unfold state_resets. intros s. reflexivity. Qed.

#[global] Instance reset_law : Law (decreases Provider.Reset).
Proof.
  constructor. intros n Hn. cbn.
  change (Z.to_nat 0 < Z.to_nat n)%nat. apply Z2Nat.inj_lt; lia.
Qed.

#[global] Instance reset_step_law :
    Law (step_decreases (Provider.STEP.step Provider.Reset)).
Proof. exact reset_law. Qed.

Lemma identity_is_not_decreasing : ~ decreases Provider.Identity.
Proof.
  intros H. specialize (H 1%Z). cbn in H. lia.
Qed.

Ltac solve_decrease :=
  repeat match goal with x := _ |- _ => subst x end;
  unfold ltof; cbn beta iota zeta;
  match goal with
  | |- (Z.to_nat (Provider.STEP.step ?s ?n) < Z.to_nat ?n)%nat =>
      let instance := constr:(_ : Law (decreases s)) in
      apply (@law _ instance);
      match goal with H : Z.gtb _ _ = true |- _ =>
        apply Z.gtb_lt in H; exact H
      end
  end.

Ltac solve_step_decrease :=
  repeat match goal with x := _ |- _ => subst x end;
  unfold ltof; cbn beta iota zeta;
  match goal with
  | |- (Z.to_nat (?step ?n) < Z.to_nat ?n)%nat =>
      let instance := constr:(_ : Law (step_decreases step)) in
      apply (@law _ instance);
      match goal with H : Z.gtb _ _ = true |- _ =>
        apply Z.gtb_lt in H; exact H
      end
  end.
