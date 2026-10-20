From Stdlib Require Import Numbers.DecimalString Lia.
From Stdlib Require ZArith.Znumtheory.
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

Definition checked_signed `{Unreachable Z} (width value : Z) : Z :=
  if fits_signed width value then value else unreachable.

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

Definition to_int `{Unreachable int} (value : Z) : int :=
  checked_signed 63 value.

Definition to_int32 `{Unreachable int32} (value : Z) : int32 :=
  checked_signed 32 value.

Definition to_int64 `{Unreachable int64} (value : Z) : int64 :=
  checked_signed 64 value.

Definition to_int32_unsigned `{Unreachable int32} (value : Z) : int32 :=
  if andb (Z.leb 0 value) (Z.ltb value (Z.pow 2 32)) then
    signed_repr 32 value
  else
    unreachable.

Definition to_int64_unsigned `{Unreachable int64} (value : Z) : int64 :=
  if andb (Z.leb 0 value) (Z.ltb value (Z.pow 2 64)) then
    signed_repr 64 value
  else
    unreachable.

Definition fits_int (value : Z) : bool := fits_signed 63 value.

Definition compare (left right : Z) : int :=
  match Z.compare left right with
  | Lt => -1
  | Eq => 0
  | Gt => 1
  end.

Definition numbits (value : Z) : int :=
  if Z.eqb value 0 then 0 else Z.succ (Z.log2 (Z.abs value)).

Definition extract `{Unreachable Z} (value offset length : Z) : Z :=
  if orb (Z.ltb offset 0) (Z.leb length 0) then
    unreachable
  else
    Z.land (Z.shiftr value offset) (Z.pred (Z.shiftl 1 length)).

Definition signed_extract `{Unreachable Z} (value offset length : Z) : Z :=
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

(** Zarith's Euclidean remainder is nonnegative even for a negative divisor.
    Exceptional inputs retain the existing typed fallback convention. *)
Definition erem `{Unreachable Z} (value modulus : Z) : Z :=
  if Z.eqb modulus 0 then unreachable
  else Z.modulo value (Z.abs modulus).

Definition powm `{Unreachable Z} (base exponent modulus : Z) : Z :=
  let modulus := Z.abs modulus in
  if Z.eqb modulus 0 then unreachable else
  match exponent with
  | Z0 => Z.modulo 1 modulus
  | Zpos exponent => powm_positive base exponent modulus
  | Zneg exponent =>
      let '(coefficient, _, gcd) := Znumtheory.extgcd base modulus in
      if Z.eqb gcd 1 then powm_positive coefficient exponent modulus
      else unreachable
  end.

(** [extgcd] computes Bezout coefficients. Sealing the executable model
    keeps its reduction out of generated clients while retaining checked
    specification lemmas. On noninvertible inputs this is only a total
    Gallina fallback: Zarith raises [Division_by_zero] there. *)
Module Type Invert_model_signature.
  Parameter invert : Z -> Z -> Z.
  Parameter invert_range : forall base modulus,
    0 < modulus -> 0 <= invert base modulus < modulus.
  Parameter invert_modular_inverse : forall base modulus,
    1 < modulus -> Z.gcd base modulus = 1 ->
    (base * invert base modulus) mod modulus = 1.
End Invert_model_signature.

Module Invert_model : Invert_model_signature.
  Definition invert (base modulus : Z) : Z :=
    let '(coefficient, _, _) := Znumtheory.extgcd base modulus in
    coefficient mod modulus.

  Lemma invert_range (base modulus : Z) :
    0 < modulus -> 0 <= invert base modulus < modulus.
  Proof.
    intros Hmodulus.
    unfold invert.
    destruct (Znumtheory.extgcd base modulus) as [[u v] d].
    apply Z.mod_pos_bound. exact Hmodulus.
  Qed.

  Lemma invert_modular_inverse (base modulus : Z) :
    1 < modulus -> Z.gcd base modulus = 1 ->
    (base * invert base modulus) mod modulus = 1.
  Proof.
    intros Hmodulus Hcoprime.
    unfold invert.
    destruct (Znumtheory.extgcd base modulus) as [[u v] d] eqn:Hext.
    pose proof (Znumtheory.extgcd_correct base modulus Hext)
      as [Hbezout Hgcd].
    rewrite Hcoprime in Hgcd. subst d.
    rewrite Z.mul_mod_idemp_r by lia.
    replace (base * u) with (u * base) by ring.
    symmetry.
    apply Z.mod_unique_pos with (q := -v); [lia | nia].
  Qed.
End Invert_model.

Definition invert : Z -> Z -> Z := Invert_model.invert.

Lemma invert_range (base modulus : Z) :
  0 < modulus -> 0 <= invert base modulus < modulus.
Proof. exact (Invert_model.invert_range base modulus). Qed.

Lemma invert_modular_inverse (base modulus : Z) :
  1 < modulus -> Z.gcd base modulus = 1 ->
  (base * invert base modulus) mod modulus = 1.
Proof. exact (Invert_model.invert_modular_inverse base modulus). Qed.

Lemma invert_prime_modular_inverse (base modulus : Z) :
  Znumtheory.prime modulus -> 0 < base < modulus ->
  (base * invert base modulus) mod modulus = 1.
Proof.
  intros Hprime Hbase.
  apply invert_modular_inverse.
  - destruct Hprime as [Hmodulus _]. exact Hmodulus.
  - apply (proj2 (Znumtheory.Zgcd_1_rel_prime base modulus)).
    apply Znumtheory.rel_prime_le_prime; [exact Hprime | lia].
Qed.

(** The Legendre symbol still depends on GMP's implementation. *)

Parameter legendre : Z -> Z -> int.

(** Zarith delegates this operation to OCaml's representation-sensitive
    generic hash. *)
Parameter hash : Z -> int.

Definition to_string (value : Z) : string :=
  NilZero.string_of_int (Z.to_int value).

(** [Z.of_string] accepts signed decimal and base-prefixed literals. A leading
    underscore is invalid, while separators after a digit are ignored. Even an
    empty digit sequence denotes zero, including the empty string and a bare
    sign. These cases follow the native Zarith parser. *)
Definition digit_value (character : ascii) : option Z :=
  let code := Z.of_N (N_of_ascii character) in
  if andb (Z.leb 48 code) (Z.leb code 57) then Some (code - 48)
  else if andb (Z.leb 65 code) (Z.leb code 70) then Some (code - 55)
  else if andb (Z.leb 97 code) (Z.leb code 102) then Some (code - 87)
  else None.

Fixpoint parse_digits (base : Z) (digits : string) (accumulator : Z)
    (seen_digit : bool) : option Z :=
  match digits with
  | EmptyString => Some accumulator
  | String character rest =>
      if Ascii.eqb character "_"%char then
        if seen_digit then parse_digits base rest accumulator seen_digit
        else None
      else
        match digit_value character with
        | Some digit =>
            if Z.ltb digit base then
              parse_digits base rest (base * accumulator + digit) true
            else None
        | None => None
        end
  end.

Definition base_and_digits (value : string) : Z * string :=
  match value with
  | String zero (String prefix digits) =>
      if Ascii.eqb zero "0"%char then
        if orb (Ascii.eqb prefix "x"%char) (Ascii.eqb prefix "X"%char) then
          (16, digits)
        else if orb (Ascii.eqb prefix "o"%char) (Ascii.eqb prefix "O"%char) then
          (8, digits)
        else if orb (Ascii.eqb prefix "b"%char) (Ascii.eqb prefix "B"%char) then
          (2, digits)
        else (10, value)
      else (10, value)
  | _ => (10, value)
  end.

Definition sign_and_digits (value : string) : Z * string :=
  match value with
  | String sign rest =>
      if Ascii.eqb sign "-"%char then
        match rest with
        | String plus digits =>
            if Ascii.eqb plus "+"%char then (-1, digits) else (-1, rest)
        | EmptyString => (-1, rest)
        end
      else if Ascii.eqb sign "+"%char then (1, rest)
      else (1, value)
  | EmptyString => (1, value)
  end.

Definition of_string_opt (value : string) : option Z :=
  let '(sign, unsigned) := sign_and_digits value in
  let '(base, digits) := base_and_digits unsigned in
  match parse_digits base digits 0 false with
  | Some parsed => Some (sign * parsed)
  | None => None
  end.

Example of_string_opt_native_forms :
  of_string_opt "" = Some 0 /\
  of_string_opt "+" = Some 0 /\
  of_string_opt "-0X" = Some 0 /\
  of_string_opt "-+0xF" = Some (-15) /\
  of_string_opt "0xF__F" = Some 255 /\
  of_string_opt "0o7_7" = Some 63 /\
  of_string_opt "0b1_0" = Some 2 /\
  of_string_opt "-1__" = Some (-1) /\
  of_string_opt "_1" = None /\
  of_string_opt "0x_F" = None /\
  of_string_opt "0o8" = None.
Proof. repeat split; reflexivity. Qed.

Definition of_string `{Unreachable Z} (value : string) : Z :=
  match of_string_opt value with
  | Some parsed => parsed
  | None => unreachable
  end.

(** Zarith supports a printf-like formatting language.  Numeric formatting is
    currently used for JSON/debug rendering, not VM state transitions. *)
Parameter format : string -> Z -> string.

Example numbits_zero : numbits 0 = 0 := eq_refl.

Example numbits_256 : numbits 256 = 9 := eq_refl.

Example extract_1234 `{Unreachable Z} : extract 4660 4 8 = 35 := eq_refl.

Example signed_extract_ff `{Unreachable Z} :
  signed_extract 255 0 8 = -1 := eq_refl.

Example bits_round_trip : of_bits (to_bits 4660) = 4660 := eq_refl.

Example powm_example `{Unreachable Z} : powm 2 10 1000 = 24 := eq_refl.
