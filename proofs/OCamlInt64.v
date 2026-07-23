Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.OCamlZ.

Local Open Scope Z_scope.

(** Executable two's-complement model of OCaml [Int64]. *)

Definition t : Set := int64.

Definition modulus : Z := 2 ^ 64.
Definition sign_bit : Z := 2 ^ 63.

Definition unsigned (value : t) : Z := value mod modulus.

Definition repr (value : Z) : t :=
  let value := value mod modulus in
  if Z.leb sign_bit value then value - modulus else value.

Definition zero : t := 0.
Definition one : t := 1.
Definition minus_one : t := -1.
Definition max_int : t := sign_bit - 1.
Definition min_int : t := -sign_bit.

Definition neg (value : t) : t := repr (-value).
Definition add (left right : t) : t := repr (left + right).
Definition sub (left right : t) : t := repr (left - right).
Definition mul (left right : t) : t := repr (left * right).
Definition div (left right : t) : t := repr (Z.quot left right).
Definition rem (left right : t) : t := repr (Z.rem left right).

Definition unsigned_div (left right : t) : t :=
  repr (Z.div (unsigned left) (unsigned right)).

Definition unsigned_rem (left right : t) : t :=
  repr (Z.modulo (unsigned left) (unsigned right)).

Definition succ (value : t) : t := add value 1.
Definition pred (value : t) : t := sub value 1.
Definition abs (value : t) : t := if Z.ltb value 0 then neg value else value.

Definition logand (left right : t) : t := repr (Z.land left right).
Definition logor (left right : t) : t := repr (Z.lor left right).
Definition logxor (left right : t) : t := repr (Z.lxor left right).
Definition lognot (value : t) : t := repr (Z.lnot value).

Definition shift_left (value : t) (count : int) : t :=
  repr (Z.shiftl value count).

Definition shift_right (value : t) (count : int) : t :=
  repr (Z.shiftr value count).

Definition shift_right_logical (value : t) (count : int) : t :=
  repr (Z.shiftr (unsigned value) count).

Definition of_int : int -> t := repr.
Definition to_int (value : t) : int := value.

Definition unsigned_to_int (value : t) : option int :=
  let value := unsigned value in
  if Z.leb value (2 ^ 62 - 1) then Some value else None.

Definition of_float : float -> t := repr.
Definition to_float (value : t) : float := value.
Definition of_int32 : int32 -> t := repr.
Definition to_int32 (value : t) : int32 :=
  let value := value mod 2 ^ 32 in
  if Z.leb (2 ^ 31) value then value - 2 ^ 32 else value.
Definition of_nativeint : nativeint -> t := repr.
Definition to_nativeint (value : t) : nativeint := value.

Definition of_string_opt (value : string) : option t :=
  match OCamlZ.of_string_opt value with
  | Some parsed => Some (repr parsed)
  | None => None
  end.

Definition of_string (value : string) : t :=
  match of_string_opt value with
  | Some parsed => parsed
  | None => axiom
  end.

Definition to_string (value : t) : string := OCamlZ.to_string value.

(** The compatibility [float] carrier is not an IEEE-754 bit pattern. *)
Parameter bits_of_float : float -> t.
Parameter float_of_bits : t -> float.

Definition compare (left right : t) : int :=
  match Z.compare left right with
  | Lt => -1
  | Eq => 0
  | Gt => 1
  end.

Definition unsigned_compare (left right : t) : int :=
  compare (unsigned left) (unsigned right).

Definition equal (left right : t) : bool := Z.eqb left right.

Definition hash (value : t) : int := value.

Definition seeded_hash (seed : int) (value : t) : int :=
  Z.lxor seed value.
