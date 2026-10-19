Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.OCamlZ.

Local Open Scope Z_scope.

(** Machine integers retain the [Z] carrier. Native values are represented by
    their signed, canonical representatives; clients supplying arbitrary [Z]
    arguments must establish that range invariant. Each arithmetic result is
    reduced modulo [2^bits] and interpreted as two's complement, not merely
    reduced to an unsigned [Z]. No such reduction applies to Zarith or [N].

    The supported platform is 64-bit OCaml: [int] has 63 bits, [nativeint] 64.
    Shift equivalence is claimed only for counts specified by OCaml. Division
    by zero and invalid [of_string] use the existing typed [Unreachable]
    boundary; this is not a model of exception propagation. *)
Module Type Width.
  Parameter bits : Z.
End Width.

Module Make (W : Width).
  Definition t : Set := Z.
  Definition size : int := W.bits.
  Definition modulus : Z := 2 ^ size.
  Definition sign_bit : Z := 2 ^ (size - 1).
  Definition unsigned (value : t) : Z := value mod modulus.
  Definition repr : Z -> t := OCamlZ.signed_repr size.

  Definition zero : t := 0.
  Definition one : t := 1.
  Definition minus_one : t := -1.
  Definition max_int : t := sign_bit - 1.
  Definition min_int : t := -sign_bit.

  Definition neg (value : t) : t := repr (-value).
  Definition add (left right : t) : t := repr (left + right).
  Definition sub (left right : t) : t := repr (left - right).
  Definition mul (left right : t) : t := repr (left * right).
  Definition succ (value : t) : t := add value 1.
  Definition pred (value : t) : t := sub value 1.
  Definition abs (value : t) : t := if Z.ltb value 0 then neg value else value.

  (** OCaml division truncates towards zero. In particular [min_int / -1]
      wraps to [min_int]; the corresponding remainder is zero. *)
  Definition div `{Unreachable t} (left right : t) : t :=
    if Z.eqb right 0 then unreachable else repr (Z.quot left right).
  Definition rem `{Unreachable t} (left right : t) : t :=
    if Z.eqb right 0 then unreachable else repr (Z.rem left right).
  Definition unsigned_div `{Unreachable t} (left right : t) : t :=
    if Z.eqb right 0 then unreachable
    else repr (Z.div (unsigned left) (unsigned right)).
  Definition unsigned_rem `{Unreachable t} (left right : t) : t :=
    if Z.eqb right 0 then unreachable
    else repr (Z.modulo (unsigned left) (unsigned right)).

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

  Definition equal : t -> t -> bool := Z.eqb.
  Definition compare (left right : t) : int :=
    match Z.compare left right with Lt => -1 | Eq => 0 | Gt => 1 end.
  Definition unsigned_compare (left right : t) : int :=
    compare (unsigned left) (unsigned right).
  Definition min : t -> t -> t := Z.min.
  Definition max : t -> t -> t := Z.max.

  (** Unlike Zarith, the native parser requires an initial digit and rejects
      overflow. Decimal input uses the signed range. Base prefixes, including
      [0u], accept an unsigned bit pattern before applying the optional sign.
      See OCaml 5.4 [runtime/ints.c], [parse_intnat]/[caml_int64_of_string]. *)
  Definition sign_and_digits (value : string) : bool * string :=
    match value with
    | String "-"%char rest => (true, rest)
    | String "+"%char rest => (false, rest)
    | _ => (false, value)
    end.

  Definition base_and_digits (value : string) : bool * Z * string :=
    match value with
    | String "0"%char (String prefix digits) =>
        if orb (Ascii.eqb prefix "x"%char) (Ascii.eqb prefix "X"%char) then
          (false, 16, digits)
        else if orb (Ascii.eqb prefix "o"%char) (Ascii.eqb prefix "O"%char) then
          (false, 8, digits)
        else if orb (Ascii.eqb prefix "b"%char) (Ascii.eqb prefix "B"%char) then
          (false, 2, digits)
        else if orb (Ascii.eqb prefix "u"%char) (Ascii.eqb prefix "U"%char) then
          (false, 10, digits)
        else (true, 10, value)
    | _ => (true, 10, value)
    end.

  Definition of_string_opt (value : string) : option t :=
    let '(negative, digits) := sign_and_digits value in
    let '(signed, base, digits) := base_and_digits digits in
    match digits with
    | EmptyString => None
    | String first rest =>
        match OCamlZ.digit_value first with
        | None => None
        | Some first_digit =>
            if Z.ltb first_digit base then
              match OCamlZ.parse_digits base rest first_digit true with
              | None => None
              | Some magnitude =>
                  let bound := if signed then
                    (if negative then sign_bit else max_int)
                    else modulus - 1 in
                  if Z.leb magnitude bound then
                    Some (repr (if negative then -magnitude else magnitude))
                  else None
              end
            else None
        end
    end.

  Definition of_string `{Unreachable t} (value : string) : t :=
    match of_string_opt value with
    | Some parsed => parsed
    | None => unreachable
    end.
  Definition to_string : t -> string := OCamlZ.to_string.
End Make.
