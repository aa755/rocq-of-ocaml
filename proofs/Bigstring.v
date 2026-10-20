Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.

(** [Bigstring.t] is a mutable C-backed bigarray in OCaml.  The translated VM
    only constructs values for cryptographic FFI calls and reads returned
    values through [OCamlBigarray.Array1.get], which is modeled separately.
    A string carrier preserves the byte-oriented interface without claiming
    to model allocation, mutation, or aliasing. *)
Definition t : Set := string.

(** The pure byte contents agree with [Bigarray.Array1.init]. Allocation and
    callback effects are outside this immutable compatibility model. *)
Fixpoint init_bytes (remaining : nat) (index : int)
    (element : int -> ascii) : string :=
  match remaining with
  | O => EmptyString
  | S remaining => String (element index)
      (init_bytes remaining (Z.succ index) element)
  end.

Definition init `{Unreachable t} (count : int) (element : int -> ascii) : t :=
  if Z.ltb count 0%Z then unreachable
  else init_bytes (Z.to_nat count) 0%Z element.

Lemma init_bytes_length (remaining : nat) (index : int)
    (element : int -> ascii) :
  Strings.String.length (init_bytes remaining index element) = remaining.
Proof. revert index; induction remaining; intros; cbn; auto. Qed.

Definition of_string (value : string) : t := value.
