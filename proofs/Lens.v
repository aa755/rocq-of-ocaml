(** Executable model of the external [lens] package used by the VM. *)

Module t.
  Record signature (Source Focus : Set) : Set := {
    get : Source -> Focus;
    set : Focus -> Source -> Source;
  }.
End t.

Definition t := t.signature.
Arguments t.get {_ _}.
Arguments t.set {_ _}.

Definition get {Source Focus : Set}
    (lens : t Source Focus) (source : Source) : Focus :=
  lens.(t.get) source.

Definition set {Source Focus : Set}
    (lens : t Source Focus) (focus : Focus) (source : Source) : Source :=
  lens.(t.set) focus source.

Definition modify {Source Focus : Set}
    (lens : t Source Focus) (f : Focus -> Focus) (source : Source) : Source :=
  set lens (f (get lens source)) source.

Module Infix.
  (** Lens composition, matching the package's [( |-- )] operator. *)
  Definition op_pipeminusminus {Outer Middle Inner : Set}
      (outer : t Outer Middle) (inner : t Middle Inner) : t Outer Inner :=
    {| t.get := fun source => inner.(t.get) (outer.(t.get) source);
       t.set :=
         fun value source =>
           outer.(t.set)
             (inner.(t.set) value (outer.(t.get) source))
             source |}.
End Infix.
