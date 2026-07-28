Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.

Import ListNotations.
Local Open Scope string_scope.

(** The concrete recursive shape of [Yojson.Safe.t].

    Keeping the constructors typed avoids existential payloads and casts.
    The translated execution roots only render JSON for diagnostic output,
    which the pure model erases along with other printing effects. *)
Inductive t : Set :=
| Null : t
| Bool : bool -> t
| Int : int -> t
| Float : float -> t
| String : string -> t
| Assoc : list (string * t) -> t
| List : list t -> t
| Intlit : string -> t
| Tuple : list t -> t
| Variant : string -> option t -> t.

Fixpoint lookup_member (name : string) (fields : list (string * t)) : t :=
  match fields with
  | [] => Null
  | (candidate, value) :: fields =>
      if Strings.String.eqb name candidate then value
      else lookup_member name fields
  end.

Module Util.
  Definition member (name : string) (value : t) : t :=
    match value with
    | Assoc fields => lookup_member name fields
    | _ => Null
    end.

  Definition to_assoc (value : t) : list (string * t) :=
    match value with
    | Assoc fields => fields
    | _ => []
    end.

  Definition to_string (_ : t) : string := "".
End Util.

Definition pretty_to_string (_ : option bool) (_ : t) : string := "".
