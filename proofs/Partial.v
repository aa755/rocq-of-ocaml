(** Coinductive semantics for OCaml computations that may diverge.

    [Delay] models a pure partial computation. [Resumption] additionally
    records actions from an abstract source monad [M], preserving the order in
    which OCaml code invokes [M.bind]. Neither type provides an unconditional
    projection to a result. The [run] functions require a computational
    convergence witness. *)

Set Implicit Arguments.

Module Delay.
  CoInductive t (A : Set) : Set :=
  | Done : A -> t A
  | Tau : (unit -> t A) -> t A.

  Arguments Done {A}.
  Arguments Tau {A}.

  CoFixpoint bind {A B : Set}
      (computation : t A) (continuation : A -> t B) : t B :=
    match computation with
    | Done value => continuation value
    | Tau next => Tau (fun _ => bind (next tt) continuation)
    end.

  Definition map {A B : Set} (f : A -> B) (computation : t A) : t B :=
    bind computation (fun value => Done (f value)).

  Inductive converges {A : Set} : t A -> Set :=
  | ConvergesDone : forall value, converges (Done value)
  | ConvergesTau : forall next,
      converges (next tt) ->
      converges (Tau next).

  Fixpoint run {A : Set} (computation : t A)
      (proof : converges computation) {struct proof} : A :=
    match proof with
    | ConvergesDone value => value
    | ConvergesTau next proof => @run A (next tt) proof
    end.

  Lemma unfold_eq {A : Set} (computation : t A) :
    computation =
    match computation with
    | Done value => Done value
    | Tau next => Tau next
    end.
  Proof. destruct computation; reflexivity. Qed.

  Lemma bind_unfold {A B : Set}
      (computation : t A) (continuation : A -> t B) :
    bind computation continuation =
    match computation with
    | Done value => continuation value
    | Tau next => Tau (fun _ => bind (next tt) continuation)
    end.
  Proof.
    destruct computation as [value | next].
    - rewrite (unfold_eq (bind (Done value) continuation)).
      cbn. destruct (continuation value); reflexivity.
    - rewrite (unfold_eq (bind (Tau next) continuation)). reflexivity.
  Qed.

  (** A caller needs convergence only for the continuation reached by the
      first computation, not for every possible value of its result type. *)
  Definition bind_converges {A B : Set}
      (computation : t A) (continuation : A -> t B)
      (proof : converges computation) :
    converges (continuation (@run A computation proof)) ->
    converges (bind computation continuation).
  Proof.
    induction proof as [value | next proof IH]; intro H;
      rewrite bind_unfold.
    - exact H.
    - apply ConvergesTau. apply IH. exact H.
  Defined.

  Lemma run_transport {A : Set} (left right : t A)
      (equation : left = right) (proof : converges left) :
    @run A right (eq_rect left converges proof right equation) =
    @run A left proof.
  Proof. destruct equation. reflexivity. Qed.

  (** Sequencing suspended computations preserves their returned value.
      No proof irrelevance or total projection from [t] is required. *)
  Lemma run_bind {A B : Set}
      (computation : t A) (continuation : A -> t B)
      (proof : converges computation)
      (next_proof : converges (continuation (@run A computation proof))) :
    @run B (bind computation continuation)
      (@bind_converges A B computation continuation proof next_proof) =
    @run B (continuation (@run A computation proof)) next_proof.
  Proof.
    revert next_proof.
    induction proof as [value | next proof IH]; intro next_proof.
    - unfold bind_converges. cbn.
      unfold eq_rec_r, eq_rec. apply run_transport.
    - unfold bind_converges. cbn.
      unfold eq_rec_r, eq_rec. rewrite run_transport. cbn. apply IH.
  Qed.
End Delay.

Module Resumption.
  (** [Bind] hides the result type of an arbitrary [M] action.  Under
      predicative [Set], that existential package belongs in [Type]. *)
  CoInductive t (M : Set -> Set) (A : Set) : Type :=
  | Done : A -> t M A
  | Tau : (unit -> t M A) -> t M A
  | Bind : forall X : Set, M X -> (X -> t M A) -> t M A
  | Compose : forall X : Set, t M X -> (X -> t M A) -> t M A.

  Arguments Done {M A}.
  Arguments Tau {M A}.
  Arguments Bind {M A X}.
  Arguments Compose {M A X}.

  (** A pure partial computation can suspend inside a monadic computation
      without inventing an [M] action or requiring convergence up front. *)
  CoFixpoint of_delay {M : Set -> Set} {A : Set}
      (computation : Delay.t A) : t M A :=
    match computation with
    | Delay.Done value => Done value
    | Delay.Tau next => Tau (fun _ => of_delay (next tt))
    end.

  Lemma unfold_eq {M : Set -> Set} {A : Set} (computation : t M A) :
    computation =
    match computation with
    | Done value => Done value
    | Tau next => Tau next
    | Bind action next => Bind action next
    | Compose computation next => Compose computation next
    end.
  Proof. destruct computation; reflexivity. Qed.

  Lemma of_delay_unfold {M : Set -> Set} {A : Set}
      (computation : Delay.t A) :
    @of_delay M A computation =
    match computation with
    | Delay.Done value => Done value
    | Delay.Tau next => Tau (fun _ => of_delay (next tt))
    end.
  Proof.
    destruct computation as [value | next];
      rewrite (unfold_eq (of_delay _)); reflexivity.
  Qed.

  CoFixpoint bind {M : Set -> Set} {A B : Set}
      (computation : t M A) (continuation : A -> t M B) : t M B :=
    match computation with
    | Done value => continuation value
    | Tau next => Tau (fun _ => bind (next tt) continuation)
    | Bind action next =>
        Bind action (fun value => bind (next value) continuation)
    | Compose computation next =>
        Compose computation
          (fun value => bind (next value) continuation)
    end.

  Definition map {M : Set -> Set} {A B : Set}
      (f : A -> B) (computation : t M A) : t M B :=
    bind computation (fun value => Done (f value)).

  (** Consume a possibly infinite sequence while allowing each element
      computation to suspend. The sequence representation is abstract:
      callers supply its observation and construction operations. *)
  CoFixpoint traverse {M : Set -> Set} {S A B T : Set}
      (uncons : S -> option (A * S)) (empty : T) (cons : B -> T -> T)
      (f : A -> t M B) (sequence : S) : t M T :=
    Tau
      (fun _ =>
        match uncons sequence with
        | None => Done empty
        | Some (value, rest) =>
            Compose (f value)
              (fun mapped =>
                Compose (traverse uncons empty cons f rest)
                  (fun mapped_rest => Done (cons mapped mapped_rest)))
        end).

  Inductive converges {M : Set -> Set} {A : Set} : t M A -> Type :=
  | ConvergesDone : forall value, converges (Done value)
  | ConvergesTau : forall next,
      converges (next tt) ->
      converges (Tau next)
  | ConvergesBind : forall X (action : M X) next,
      (forall value, converges (next value)) ->
      converges (Bind action next)
  | ConvergesCompose : forall X (computation : t M X) next,
      converges computation ->
      (forall value, converges (next value)) ->
      converges (Compose computation next).

  Fixpoint run {M : Set -> Set}
      (return_ : forall {A : Set}, A -> M A)
      (bind_ : forall {A B : Set}, M A -> (A -> M B) -> M B)
      {A : Set} (computation : t M A) (proof : converges computation)
      {struct proof} : M A :=
    match proof with
    | ConvergesDone value => return_ value
    | ConvergesTau next proof =>
        @run M (@return_) (@bind_) A (next tt) proof
    | ConvergesBind action next proof =>
        bind_ action
          (fun value =>
            @run M (@return_) (@bind_) A (next value) (proof value))
    | @ConvergesCompose _ _ _ computation next
        computation_proof next_proof =>
        bind_
          (@run M (@return_) (@bind_) _ computation computation_proof)
          (fun value =>
            @run M (@return_) (@bind_) A (next value) (next_proof value))
    end.

  Definition run_explicit {M : Set -> Set}
      (return_ : forall {A : Set}, A -> M A)
      (bind_ : forall {A B : Set}, M A -> (A -> M B) -> M B)
      {A : Set} (computation : t M A) (proof : converges computation) : M A :=
    @run M (@return_) (@bind_) A computation proof.

  Arguments run_explicit {M} return_ bind_ {A} computation proof.

  Definition of_delay_converges {M : Set -> Set} {A : Set}
      (computation : Delay.t A) (proof : Delay.converges computation) :
    converges (@of_delay M A computation).
  Proof.
    induction proof as [value | next proof IH]; rewrite of_delay_unfold.
    - apply ConvergesDone.
    - apply ConvergesTau. exact IH.
  Defined.

  (** The embedding cannot make a divergent pure computation converge. *)
  Lemma of_delay_converges_inv {M : Set -> Set} {A : Set}
      (computation : Delay.t A) :
    converges (@of_delay M A computation) -> Delay.converges computation.
  Proof.
    intro proof.
    remember (@of_delay M A computation) as resumed eqn:Heq.
    revert computation Heq.
    induction proof as
      [A value | A next proof IH | A X action next proof IH |
       A X source next source_proof source_IH next_proof next_IH];
      intros computation Heq; destruct computation as [value' | next'];
      rewrite of_delay_unfold in Heq; try discriminate.
    - apply Delay.ConvergesDone.
    - apply Delay.ConvergesTau. apply IH.
      injection Heq as Hnext.
      exact (f_equal (fun continuation => continuation tt) Hnext).
  Qed.

  Lemma run_transport {M : Set -> Set}
      (return_ : forall {A : Set}, A -> M A)
      (bind_ : forall {A B : Set}, M A -> (A -> M B) -> M B)
      {A : Set} (left right : t M A) (equation : left = right)
      (proof : converges left) :
    @run M (@return_) (@bind_) A right
      (eq_rect left converges proof right equation) =
    @run M (@return_) (@bind_) A left proof.
  Proof. destruct equation. reflexivity. Qed.

  (** Embedding a convergent pure computation introduces no monadic action:
      observing it returns exactly its original result. *)
  Lemma run_of_delay {M : Set -> Set}
      (return_ : forall {A : Set}, A -> M A)
      (bind_ : forall {A B : Set}, M A -> (A -> M B) -> M B)
      {A : Set} (computation : Delay.t A)
      (proof : Delay.converges computation) :
    @run M (@return_) (@bind_) A (of_delay computation)
      (@of_delay_converges M A computation proof) =
    return_ (@Delay.run A computation proof).
  Proof.
    induction proof as [value | next proof IH].
    - unfold of_delay_converges. cbn. unfold eq_rect_r.
      rewrite run_transport. reflexivity.
    - unfold of_delay_converges. cbn. unfold eq_rect_r.
      rewrite run_transport. cbn. exact IH.
  Qed.
End Resumption.
