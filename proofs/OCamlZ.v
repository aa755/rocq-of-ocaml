From Stdlib Require Import Numbers.DecimalString.
Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.

Local Open Scope Z_scope.

(** Executable compatibility model for the Zarith operations that do not
    have a definition with the same interface in Rocq's [Z] library. *)

Definition of_int (value : int) : Z := value.

Definition op_tildedollar : int -> Z := of_int.

Definition signed_min (width : Z) : Z := Z.opp (Z.pow 2 (Z.pred width)).

Definition signed_max (width : Z) : Z := Z.pred (Z.pow 2 (Z.pred width)).

Definition fits_signed (width value : Z) : bool :=
  andb (Z.leb (signed_min width) value) (Z.leb value (signed_max width)).

Definition checked_signed (width value : Z) : Z :=
  if fits_signed width value then value else axiom.

Definition signed_repr (width value : Z) : Z :=
  let modulus := Z.pow 2 width in
  let sign_bit := Z.pow 2 (Z.pred width) in
  let value := Z.modulo value modulus in
  if Z.leb sign_bit value then Z.sub value modulus else value.

Definition of_int32 (value : int32) : Z := value.

Definition of_int64 (value : int64) : Z := value.

Definition of_int32_unsigned (value : int32) : Z :=
  if Z.ltb value 0 then Z.add value (Z.pow 2 32) else value.

Definition of_int64_unsigned (value : int64) : Z :=
  if Z.ltb value 0 then Z.add value (Z.pow 2 64) else value.

Definition to_int (value : Z) : int := checked_signed 63 value.

Definition to_int32 (value : Z) : int32 := checked_signed 32 value.

Definition to_int64 (value : Z) : int64 := checked_signed 64 value.

Definition to_int32_unsigned (value : Z) : int32 :=
  if andb (Z.leb 0 value) (Z.ltb value (Z.pow 2 32)) then
    signed_repr 32 value
  else
    axiom.

Definition to_int64_unsigned (value : Z) : int64 :=
  if andb (Z.leb 0 value) (Z.ltb value (Z.pow 2 64)) then
    signed_repr 64 value
  else
    axiom.

Definition fits_int (value : Z) : bool := fits_signed 63 value.

Definition compare (left right : Z) : int :=
  match Z.compare left right with
  | Lt => -1
  | Eq => 0
  | Gt => 1
  end.

Definition numbits (value : Z) : int :=
  if Z.eqb value 0 then 0 else Z.succ (Z.log2 (Z.abs value)).

Definition extract (value offset length : Z) : Z :=
  if orb (Z.ltb offset 0) (Z.leb length 0) then
    axiom
  else
    Z.land (Z.shiftr value offset) (Z.pred (Z.shiftl 1 length)).

Definition signed_extract (value offset length : Z) : Z :=
  let extracted := extract value offset length in
  if Z.testbit extracted (Z.pred length) then
    Z.sub extracted (Z.shiftl 1 length)
  else
    extracted.

Fixpoint to_bits_bytes (count : nat) (value : Z) : string :=
  match count with
  | O => EmptyString
  | S count =>
      String
        (ascii_of_N (Z.to_N (Z.modulo value 256)))
        (to_bits_bytes count (Z.div value 256))
  end.

Definition to_bits (value : Z) : string :=
  let value := Z.abs value in
  let byte_count := Z.div (Z.add (numbits value) 7) 8 in
  to_bits_bytes (Z.to_nat byte_count) value.

Fixpoint of_bits (value : string) : Z :=
  match value with
  | EmptyString => 0
  | String byte rest =>
      Z.add (Z.of_N (N_of_ascii byte)) (Z.mul 256 (of_bits rest))
  end.

Fixpoint powm_positive (base : Z) (exponent : positive) (modulus : Z) : Z :=
  match exponent with
  | xH => Z.modulo base modulus
  | xO exponent =>
      let half := powm_positive base exponent modulus in
      Z.modulo (Z.mul half half) modulus
  | xI exponent =>
      let half := powm_positive base exponent modulus in
      Z.modulo (Z.mul base (Z.mul half half)) modulus
  end.

Definition powm (base exponent modulus : Z) : Z :=
  match exponent with
  | Z0 => Z.modulo 1 modulus
  | Zpos exponent => powm_positive base exponent modulus
  | Zneg _ =>
      (* Negative exponents require a modular inverse.  Monad VM's EVM
         arithmetic only calls [powm] with unsigned exponents. *)
      axiom
  end.

(** Zarith delegates this operation to OCaml's representation-sensitive
    generic hash. *)
Parameter hash : Z -> int.

Definition to_string (value : Z) : string :=
  NilZero.string_of_int (Z.to_int value).

Definition of_string_opt (value : string) : option Z :=
  match NilZero.int_of_string value with
  | Some parsed => Some (Z.of_int parsed)
  | None => None
  end.

Definition of_string (value : string) : Z :=
  match of_string_opt value with
  | Some parsed => parsed
  | None => axiom
  end.

(** Zarith supports a printf-like formatting language.  Numeric formatting is
    currently used for JSON/debug rendering, not VM state transitions. *)
Parameter format : string -> Z -> string.

Example numbits_zero : numbits 0 = 0 := eq_refl.

Example numbits_256 : numbits 256 = 9 := eq_refl.

Example extract_1234 : extract 4660 4 8 = 35 := eq_refl.

Example signed_extract_ff : signed_extract 255 0 8 = -1 := eq_refl.

Example bits_round_trip : of_bits (to_bits 4660) = 4660 := eq_refl.

Example powm_example : powm 2 10 1000 = 24 := eq_refl.
