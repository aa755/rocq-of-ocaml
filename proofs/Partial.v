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
  (** Map every source action through [lift], preserving suspension and
      composition. The observation theorem below states the laws needed for
      this operation to commute with a source monad interpreter. *)
  CoFixpoint hoist {M N : Set -> Set}
      (lift : forall {X : Set}, M X -> N X) {A : Set}
      (computation : t M A) : t N A :=
    match computation with
    | Done value => Done value
    | Tau next => Tau (fun _ => hoist (@lift) (next tt))
    | Bind action next =>
        Bind (lift action) (fun value => hoist (@lift) (next value))
    | Compose source next =>
        Compose (hoist (@lift) source)
          (fun value => hoist (@lift) (next value))
    end.

  Lemma hoist_unfold {M N : Set -> Set}
      (lift : forall {X : Set}, M X -> N X) {A : Set}
      (computation : t M A) :
    hoist (@lift) computation =
    match computation with
    | Done value => Done value
    | Tau next => Tau (fun _ => hoist (@lift) (next tt))
    | Bind action next =>
        Bind (lift action) (fun value => hoist (@lift) (next value))
    | Compose source next =>
        Compose (hoist (@lift) source)
          (fun value => hoist (@lift) (next value))
    end.
  Proof. destruct computation; rewrite (unfold_eq (hoist _ _)); reflexivity. Qed.

  Definition hoist_converges {M N : Set -> Set}
      (lift : forall {X : Set}, M X -> N X) {A : Set}
      (computation : t M A) (proof : converges computation) :
    converges (hoist (@lift) computation).
  Proof.
    induction proof as
      [A value | A next proof IH | A X action next proof IH |
       A X source next source_proof source_IH next_proof next_IH];
      rewrite hoist_unfold.
    - apply ConvergesDone.
    - apply ConvergesTau. exact IH.
    - apply ConvergesBind. exact IH.
    - apply ConvergesCompose; assumption.
  Defined.

  (** Observe related target actions instead of requiring equality of
      functions. State models can instantiate [equiv] with pointwise equality,
      without assuming functional extensionality or proof irrelevance. *)
  Lemma run_hoist {M N : Set -> Set}
      (lift : forall {X : Set}, M X -> N X)
      (returnM : forall {X : Set}, X -> M X)
      (bindM : forall {X Y : Set}, M X -> (X -> M Y) -> M Y)
      (returnN : forall {X : Set}, X -> N X)
      (bindN : forall {X Y : Set}, N X -> (X -> N Y) -> N Y)
      (equiv : forall {X : Set}, N X -> N X -> Prop)
      (equiv_refl : forall (X : Set) (value : N X), equiv value value)
      (equiv_trans : forall (X : Set) (left middle right : N X),
        equiv left middle -> equiv middle right -> equiv left right)
      (bind_respects : forall (X Y : Set) (left right : N X)
        (next_left next_right : X -> N Y),
        equiv left right ->
        (forall value, equiv (next_left value) (next_right value)) ->
        equiv (bindN left next_left) (bindN right next_right))
      (lift_return : forall (X : Set) (value : X),
        equiv (returnN value) (lift (returnM value)))
      (lift_bind : forall (X Y : Set) (action : M X) (next : X -> M Y),
        equiv (bindN (lift action) (fun value => lift (next value)))
          (lift (bindM action next)))
      {A : Set} (computation : t M A) (proof : converges computation) :
    equiv
      (@run N (@returnN) (@bindN) A (hoist (@lift) computation)
        (@hoist_converges M N (@lift) A computation proof))
      (lift (@run M (@returnM) (@bindM) A computation proof)).
  Proof.
    induction proof as
      [A value | A next proof IH | A X action next proof IH |
       A X source next source_proof source_IH next_proof next_IH].
    - unfold hoist_converges. cbn. unfold eq_rect_r.
      rewrite run_transport. cbn. apply lift_return.
    - unfold hoist_converges. cbn. unfold eq_rect_r.
      rewrite run_transport. cbn. exact IH.
    - unfold hoist_converges. cbn. unfold eq_rect_r.
      rewrite run_transport. cbn.
      eapply equiv_trans.
      + apply bind_respects. apply equiv_refl. exact IH.
      + apply lift_bind.
    - unfold hoist_converges. cbn. unfold eq_rect_r.
      rewrite run_transport. cbn.
      eapply equiv_trans.
      + apply bind_respects. exact source_IH. exact next_IH.
      + apply lift_bind.
  Qed.

  Lemma bind_unfold {M : Set -> Set} {A B : Set}
      (computation : t M A) (continuation : A -> t M B) :
    bind computation continuation =
    match computation with
    | Done value => continuation value
    | Tau next => Tau (fun _ => bind (next tt) continuation)
    | Bind action next =>
        Bind action (fun value => bind (next value) continuation)
    | Compose source next =>
        Compose source (fun value => bind (next value) continuation)
    end.
  Proof.
    destruct computation as [value | next | X action next | X source next];
      rewrite (unfold_eq (bind _ _)); cbn;
      try reflexivity.
    destruct (continuation value); reflexivity.
  Qed.
End Resumption.

Module ResultState.
  Definition t (S E A : Set) := S -> sum A E * S.

  Definition return_ {S E A : Set} (value : A) : t S E A :=
    fun state => (inl value, state).

  Definition bind_ {S E A B : Set} (action : t S E A)
      (next : A -> t S E B) : t S E B :=
    fun state =>
      let '(result, state) := action state in
      match result with
      | inl value => next value state
      | inr error => (inr error, state)
      end.

  (** Observe state actions without requiring a convergence witness. A
      source error retains its updated state and skips every continuation.
      Flattening [Compose] beneath [Tau] keeps this evaluator productive. *)
  CoFixpoint observe {S E A : Set}
      (computation : Resumption.t (t S E) A) (state : S) :
      Delay.t (sum A E * S) :=
    match computation with
    | Resumption.Done value => Delay.Done (inl value, state)
    | Resumption.Tau next =>
        Delay.Tau (fun _ => observe (next tt) state)
    | Resumption.Bind action next =>
        Delay.Tau (fun _ =>
          let '(result, state) := action state in
          match result with
          | inl value => observe (next value) state
          | inr error => Delay.Done (inr error, state)
          end)
    | Resumption.Compose source next =>
        Delay.Tau (fun _ => observe (Resumption.bind source next) state)
    end.

  Lemma observe_unfold {S E A : Set}
      (computation : Resumption.t (t S E) A) (state : S) :
    observe computation state =
    match computation with
    | Resumption.Done value => Delay.Done (inl value, state)
    | Resumption.Tau next =>
        Delay.Tau (fun _ => observe (next tt) state)
    | Resumption.Bind action next =>
        Delay.Tau (fun _ =>
          let '(result, state) := action state in
          match result with
          | inl value => observe (next value) state
          | inr error => Delay.Done (inr error, state)
          end)
    | Resumption.Compose source next =>
        Delay.Tau (fun _ => observe (Resumption.bind source next) state)
    end.
  Proof.
    destruct computation; rewrite (Delay.unfold_eq (observe _ _)); reflexivity.
  Qed.

  Definition returns {A : Set} (computation : Delay.t A) (value : A) : Type :=
    { proof : Delay.converges computation &
      @Delay.run A computation proof = value }.

  Lemma returns_done {A : Set} (value : A) :
    returns (Delay.Done value) value.
  Proof. exists (Delay.ConvergesDone value). reflexivity. Defined.

  Lemma returns_tau {A : Set} (next : unit -> Delay.t A) (value : A) :
    returns (next tt) value -> returns (Delay.Tau next) value.
  Proof.
    intros [proof equation]. exists (Delay.ConvergesTau next proof). exact equation.
  Defined.

  Definition run {S E A : Set} (computation : Resumption.t (t S E) A)
      (proof : Resumption.converges computation) : t S E A :=
    @Resumption.run (t S E) (@return_ S E) (@bind_ S E) A computation proof.

  Lemma bind_assoc {S E A B C : Set} (action : t S E A)
      (next : A -> t S E B) (last : B -> t S E C) (state : S) :
    bind_ (bind_ action next) last state =
    bind_ action (fun value => bind_ (next value) last) state.
  Proof.
    unfold bind_. destruct (action state) as [[value | error] next_state];
      reflexivity.
  Qed.

  (** Prove observation and observation after binding together: flattening
      a composed resumption needs the induction hypothesis for its source and
      the continuation selected by that source. *)
  Definition observe_spec {S E A : Set}
      (computation : Resumption.t (t S E) A)
      (proof : Resumption.converges computation) :
    ((forall state, returns (observe computation state)
        (@run S E A computation proof state)) *
     (forall (B : Set) (next : A -> Resumption.t (t S E) B)
        (next_run : A -> t S E B),
        (forall value state, returns (observe (next value) state)
          (next_run value state)) ->
        forall state, returns (observe (Resumption.bind computation next) state)
          (bind_ (@run S E A computation proof) next_run state)))%type.
  Proof.
    induction proof as
      [A value | A next proof IH | A X action next proof IH |
       A X source next source_proof source_IH next_proof next_IH].
    - split.
      + intro state. rewrite observe_unfold. apply returns_done.
      + intros B next next_run Hnext state.
        rewrite Resumption.bind_unfold. apply Hnext.
    - destruct IH as [IHobserve IHbind]. split.
      + intro state. rewrite observe_unfold. apply returns_tau. apply IHobserve.
      + intros B continuation next_run Hnext state.
        rewrite Resumption.bind_unfold, observe_unfold.
        apply returns_tau. apply IHbind. exact Hnext.
    - split.
      + intro state. rewrite observe_unfold. apply returns_tau.
        cbn [run Resumption.run]. unfold bind_.
        destruct (action state) as [[value | error] next_state].
        * apply (fst (IH value)).
        * apply returns_done.
      + intros B continuation next_run Hnext state.
        rewrite Resumption.bind_unfold, observe_unfold. apply returns_tau.
        cbn [run Resumption.run]. unfold bind_.
        destruct (action state) as [[value | error] next_state].
        * apply (snd (IH value)). exact Hnext.
        * apply returns_done.
    - destruct source_IH as [source_observe source_bind]. split.
      + intro state. rewrite observe_unfold. apply returns_tau.
        apply source_bind. intros value next_state. apply (fst (next_IH value)).
      + intros B continuation next_run Hnext state.
        rewrite Resumption.bind_unfold, observe_unfold. apply returns_tau.
        cbn [run Resumption.run]. rewrite bind_assoc.
        apply source_bind. intros value next_state.
        apply (snd (next_IH value)). exact Hnext.
  Defined.

  (** The abstract resumption witness is sufficient, but not necessary:
      state observation can terminate when an error skips a divergent branch. *)
  Definition observe_converges {S E A : Set}
      (computation : Resumption.t (t S E) A)
      (proof : Resumption.converges computation) (state : S) :
    Delay.converges (observe computation state) :=
    projT1 (fst (@observe_spec S E A computation proof) state).

  Lemma run_observe {S E A : Set}
      (computation : Resumption.t (t S E) A)
      (proof : Resumption.converges computation) (state : S) :
    @Delay.run (sum A E * S) (observe computation state)
      (@observe_converges S E A computation proof state) =
    @run S E A computation proof state.
  Proof.
    exact (projT2 (fst (@observe_spec S E A computation proof) state)).
  Qed.

  (** An error keeps the action's updated state and requires no termination
      fact about the continuation, which may diverge. *)
  Definition observe_bind_error {S E A X : Set}
      (action : t S E X) (next : X -> Resumption.t (t S E) A)
      (state : S) (error : E) (next_state : S)
      (equation : action state = (inr error, next_state)) :
    returns (observe (Resumption.Bind action next) state) (inr error, next_state).
  Proof.
    rewrite observe_unfold. apply returns_tau.
    rewrite equation. apply returns_done.
  Defined.
End ResultState.
