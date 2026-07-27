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
End Delay.

Module Resumption.
  CoInductive t (M : Set -> Set) (A : Set) : Set :=
  | Done : A -> t M A
  | Tau : (unit -> t M A) -> t M A
  | Bind : forall X : Set, M X -> (X -> t M A) -> t M A
  | Compose : forall X : Set, t M X -> (X -> t M A) -> t M A.

  Arguments Done {M A}.
  Arguments Tau {M A}.
  Arguments Bind {M A X}.
  Arguments Compose {M A X}.

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

  Inductive converges {M : Set -> Set} {A : Set} : t M A -> Set :=
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
End Resumption.
