Require Import RocqOfOCaml.Libraries.

(** The result type and bind operation emitted by [ppx_deriving_yojson].
    Constructors [Ok] and [Error] are translated to [inl] and [inr]. *)
Definition error_or (A : Set) : Set := sum A string.

Definition op_gtgteq {A B : Set}
    (result : error_or A) (next : A -> error_or B) : error_or B :=
  match result with
  | inl value => next value
  | inr error => inr error
  end.
