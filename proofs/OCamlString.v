Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.
Require Import RocqOfOCaml.OCamlSeq.
Require Import RocqOfOCaml.OCamlUchar.

Import ListNotations.
Local Open Scope Z_scope.

(** Executable compatibility model for OCaml 5.4 [Stdlib.String].

    OCaml strings are represented by Gallina [string] values, and OCaml
    integer indices by [Z].  Pure operations used by the Monad VM are
    executable.  Mutation, runtime hashing, and UTF decoder internals have no
    faithful counterpart in this pure embedding and are explicit parameters
    rather than silently fabricated implementations. *)

Definition t : Set := string.

Definition empty : string := EmptyString.

Definition length (value : string) : int :=
  Z.of_nat (Strings.String.length value).

Definition get (value : string) (index : int) : ascii :=
  match Strings.String.get (Z.to_nat index) value with
  | Some character => character
  | None => axiom
  end.

Fixpoint make_nat (count : nat) (character : ascii) : string :=
  match count with
  | O => EmptyString
  | S count' => String character (make_nat count' character)
  end.

Definition make (count : int) (character : ascii) : string :=
  make_nat (Z.to_nat count) character.

Fixpoint init_nat
    (remaining : nat) (index : int) (element : int -> ascii) : string :=
  match remaining with
  | O => EmptyString
  | S remaining' =>
      String (element index) (init_nat remaining' (index + 1) element)
  end.

Definition init (count : int) (element : int -> ascii) : string :=
  init_nat (Z.to_nat count) 0 element.

Definition of_bytes (value : bytes) : string := value.

Definition to_bytes (value : string) : bytes := value.

(** OCaml [bytes] values are mutable.  The pure embedding has no store in
    which to represent the effect of these operations. *)
Parameter blit : string -> int -> bytes -> int -> int -> unit.

Fixpoint concat (separator : string) (values : list string) : string :=
  match values with
  | [] => EmptyString
  | [value] => value
  | value :: values' =>
      Strings.String.append value
        (Strings.String.append separator (concat separator values'))
  end.

Definition cat : string -> string -> string := Strings.String.append.

Fixpoint starts_with_chars (prefix value : string) : bool :=
  match prefix, value with
  | EmptyString, _ => true
  | String _ _, EmptyString => false
  | String prefix_head prefix_tail, String value_head value_tail =>
      andb (Ascii.eqb prefix_head value_head)
        (starts_with_chars prefix_tail value_tail)
  end.

Definition starts_with (prefix value : string) : bool :=
  starts_with_chars prefix value.

Definition ends_with (suffix value : string) : bool :=
  let suffix_length := Strings.String.length suffix in
  let value_length := Strings.String.length value in
  if Nat.leb suffix_length value_length then
    Strings.String.eqb suffix
      (substring (value_length - suffix_length) suffix_length value)
  else
    false.

Fixpoint skip_string (count : nat) (value : string) : string :=
  match count, value with
  | O, _ => value
  | S count', EmptyString => skip_string count' EmptyString
  | S count', String _ value' => skip_string count' value'
  end.

Fixpoint contains_char (character : ascii) (value : string) : bool :=
  match value with
  | EmptyString => false
  | String head tail =>
      orb (Ascii.eqb character head) (contains_char character tail)
  end.

Definition contains_from
    (value : string) (start : int) (character : ascii) : bool :=
  contains_char character (skip_string (Z.to_nat start) value).

Definition rcontains_from
    (value : string) (start : int) (character : ascii) : bool :=
  if Z.ltb start 0 then
    false
  else
    contains_char character
      (substring 0 (S (Z.to_nat start)) value).

Definition contains (value : string) (character : ascii) : bool :=
  contains_char character value.

Definition sub (value : string) (start count : int) : string :=
  substring (Z.to_nat start) (Z.to_nat count) value.

Fixpoint split_on_char_acc
    (separator : ascii) (value current : string) : list string :=
  match value with
  | EmptyString => [current]
  | String head tail =>
      if Ascii.eqb separator head then
        current :: split_on_char_acc separator tail EmptyString
      else
        split_on_char_acc separator tail
          (Strings.String.append current (String head EmptyString))
  end.

Definition split_on_char (separator : ascii) (value : string) : list string :=
  split_on_char_acc separator value EmptyString.

Fixpoint map (function_value : ascii -> ascii) (value : string) : string :=
  match value with
  | EmptyString => EmptyString
  | String head tail =>
      String (function_value head) (map function_value tail)
  end.

Fixpoint mapi_from
    (function_value : int -> ascii -> ascii)
    (index : int) (value : string) : string :=
  match value with
  | EmptyString => EmptyString
  | String head tail =>
      String (function_value index head)
        (mapi_from function_value (index + 1) tail)
  end.

Definition mapi
    (function_value : int -> ascii -> ascii) (value : string) : string :=
  mapi_from function_value 0 value.

Fixpoint fold_left {acc : Set}
    (function_value : acc -> ascii -> acc)
    (state : acc) (value : string) : acc :=
  match value with
  | EmptyString => state
  | String head tail =>
      fold_left function_value (function_value state head) tail
  end.

Fixpoint fold_right {acc : Set}
    (function_value : ascii -> acc -> acc)
    (value : string) (state : acc) : acc :=
  match value with
  | EmptyString => state
  | String head tail =>
      function_value head (fold_right function_value tail state)
  end.

Fixpoint for_all
    (predicate : ascii -> bool) (value : string) : bool :=
  match value with
  | EmptyString => true
  | String head tail => andb (predicate head) (for_all predicate tail)
  end.

Fixpoint _exists
    (predicate : ascii -> bool) (value : string) : bool :=
  match value with
  | EmptyString => false
  | String head tail => orb (predicate head) (_exists predicate tail)
  end.

Definition is_space (character : ascii) : bool :=
  let code := Z.of_N (N_of_ascii character) in
  orb (Z.eqb code 9)
    (orb (Z.eqb code 10)
      (orb (Z.eqb code 11)
        (orb (Z.eqb code 12)
          (orb (Z.eqb code 13) (Z.eqb code 32))))).

Fixpoint trim_left (value : string) : string :=
  match value with
  | EmptyString => EmptyString
  | String head tail =>
      if is_space head then trim_left tail else value
  end.

Fixpoint reverse_append (value accumulator : string) : string :=
  match value with
  | EmptyString => accumulator
  | String head tail =>
      reverse_append tail (String head accumulator)
  end.

Definition reverse (value : string) : string :=
  reverse_append value EmptyString.

Definition trim (value : string) : string :=
  reverse (trim_left (reverse (trim_left value))).

(** OCaml's exact escaping format is presentation-only and is not used by the
    VM transition system. *)
Parameter escaped : string -> string.

Definition code (character : ascii) : Z :=
  Z.of_N (N_of_ascii character).

Definition character_of_code (value : Z) : ascii :=
  ascii_of_N (Z.to_N (value mod 256)).

Definition lowercase_character (character : ascii) : ascii :=
  let value := code character in
  if andb (Z.leb 65 value) (Z.leb value 90) then
    character_of_code (value + 32)
  else
    character.

Definition uppercase_character (character : ascii) : ascii :=
  let value := code character in
  if andb (Z.leb 97 value) (Z.leb value 122) then
    character_of_code (value - 32)
  else
    character.

Definition uppercase_ascii (value : string) : string :=
  map uppercase_character value.

Definition lowercase_ascii (value : string) : string :=
  map lowercase_character value.

Definition capitalize_ascii (value : string) : string :=
  match value with
  | EmptyString => EmptyString
  | String head tail => String (uppercase_character head) tail
  end.

Definition uncapitalize_ascii (value : string) : string :=
  match value with
  | EmptyString => EmptyString
  | String head tail => String (lowercase_character head) tail
  end.

Fixpoint iter (function_value : ascii -> unit) (value : string) : unit :=
  match value with
  | EmptyString => tt
  | String head tail =>
      let '_ := function_value head in
      iter function_value tail
  end.

Fixpoint iteri_from
    (function_value : int -> ascii -> unit)
    (index : int) (value : string) : unit :=
  match value with
  | EmptyString => tt
  | String head tail =>
      let '_ := function_value index head in
      iteri_from function_value (index + 1) tail
  end.

Definition iteri
    (function_value : int -> ascii -> unit) (value : string) : unit :=
  iteri_from function_value 0 value.

Fixpoint index_from_nat
    (value : string) (index : int) (character : ascii) : option int :=
  match value with
  | EmptyString => None
  | String head tail =>
      if Ascii.eqb character head then
        Some index
      else
        index_from_nat tail (index + 1) character
  end.

Definition index_from_opt
    (value : string) (start : int) (character : ascii) : option int :=
  index_from_nat (skip_string (Z.to_nat start) value) start character.

Definition index_from
    (value : string) (start : int) (character : ascii) : int :=
  match index_from_opt value start character with
  | Some index => index
  | None => axiom
  end.

Fixpoint rindex_to_nat
    (value : string) (index limit : nat) (character : ascii)
    (last : option int) : option int :=
  match value with
  | EmptyString => last
  | String head tail =>
      if Nat.ltb limit index then
        last
      else
        rindex_to_nat tail (S index) limit character
          (if Ascii.eqb character head
           then Some (Z.of_nat index)
           else last)
  end.

Definition rindex_from_opt
    (value : string) (start : int) (character : ascii) : option int :=
  if Z.ltb start 0 then
    None
  else
    rindex_to_nat value O (Z.to_nat start) character None.

Definition rindex_from
    (value : string) (start : int) (character : ascii) : int :=
  match rindex_from_opt value start character with
  | Some index => index
  | None => axiom
  end.

Definition index_opt (value : string) (character : ascii) : option int :=
  index_from_opt value 0 character.

Definition index (value : string) (character : ascii) : int :=
  index_from value 0 character.

Definition rindex_opt (value : string) (character : ascii) : option int :=
  rindex_from_opt value (length value - 1) character.

Definition rindex (value : string) (character : ascii) : int :=
  rindex_from value (length value - 1) character.

Fixpoint to_seq_node (value : string) : OCamlSeq.node ascii :=
  match value with
  | EmptyString => OCamlSeq.Nil
  | String head tail =>
      OCamlSeq.Cons head (fun _ => to_seq_node tail)
  end.

Definition to_seq (value : t) : OCamlSeq.t ascii :=
  fun _ => to_seq_node value.

Fixpoint to_seqi_node
    (index : int) (value : string) : OCamlSeq.node (int * ascii) :=
  match value with
  | EmptyString => OCamlSeq.Nil
  | String head tail =>
      OCamlSeq.Cons (index, head)
        (fun _ => to_seqi_node (index + 1) tail)
  end.

Definition to_seqi (value : t) : OCamlSeq.t (int * ascii) :=
  fun _ => to_seqi_node 0 value.

#[bypass_check(guard)]
Fixpoint of_seq_guarded
    (value : OCamlSeq.t ascii) (guard : GeneralRecursionGuard)
    {struct guard} : t :=
  match value tt with
  | OCamlSeq.Nil => EmptyString
  | OCamlSeq.Cons head tail => String head (of_seq_guarded tail guard)
  end.

Definition of_seq (value : OCamlSeq.t ascii) : t :=
  of_seq_guarded value general_recursion_guard.

(** UTF decoding uses OCaml's private [Uchar.utf_decode] representation and is
    outside the executable subset needed by the VM. *)
Parameter get_utf_8_uchar : t -> int -> OCamlUchar.utf_decode.
Parameter is_valid_utf_8 : t -> bool.
Parameter get_utf_16be_uchar : t -> int -> OCamlUchar.utf_decode.
Parameter is_valid_utf_16be : t -> bool.
Parameter get_utf_16le_uchar : t -> int -> OCamlUchar.utf_decode.
Parameter is_valid_utf_16le : t -> bool.

Parameter edit_distance : option int -> t -> t -> int.

Parameter spellcheck :
  option (string -> int) -> ((string -> unit) -> unit) ->
  string -> list string.

Definition get_uint8 (value : string) (index : int) : int :=
  code (get value index).

Definition signed_value (bits value : Z) : Z :=
  if Z.leb (2 ^ (bits - 1)) value then value - 2 ^ bits else value.

Definition get_int8 (value : string) (index : int) : int :=
  signed_value 8 (get_uint8 value index).

Definition get_uint16_be (value : string) (index : int) : int :=
  256 * get_uint8 value index + get_uint8 value (index + 1).

Definition get_uint16_le (value : string) (index : int) : int :=
  get_uint8 value index + 256 * get_uint8 value (index + 1).

(** The translation target is the little-endian x86-64 production platform. *)
Definition get_uint16_ne : string -> int -> int := get_uint16_le.

Definition get_int16_be (value : string) (index : int) : int :=
  signed_value 16 (get_uint16_be value index).

Definition get_int16_le (value : string) (index : int) : int :=
  signed_value 16 (get_uint16_le value index).

Definition get_int16_ne : string -> int -> int := get_int16_le.

Definition get_uint32_be (value : string) (index : int) : Z :=
  2 ^ 24 * get_uint8 value index +
  2 ^ 16 * get_uint8 value (index + 1) +
  2 ^ 8 * get_uint8 value (index + 2) +
  get_uint8 value (index + 3).

Definition get_uint32_le (value : string) (index : int) : Z :=
  get_uint8 value index +
  2 ^ 8 * get_uint8 value (index + 1) +
  2 ^ 16 * get_uint8 value (index + 2) +
  2 ^ 24 * get_uint8 value (index + 3).

Definition get_int32_be (value : string) (index : int) : int32 :=
  signed_value 32 (get_uint32_be value index).

Definition get_int32_le (value : string) (index : int) : int32 :=
  signed_value 32 (get_uint32_le value index).

Definition get_int32_ne : string -> int -> int32 := get_int32_le.

Fixpoint read_unsigned_be_nat
    (remaining : nat) (value : string) (index : int) : Z :=
  match remaining with
  | O => 0
  | S remaining' =>
      256 ^ Z.of_nat remaining' * get_uint8 value index +
      read_unsigned_be_nat remaining' value (index + 1)
  end.

Fixpoint read_unsigned_le_nat
    (remaining : nat) (value : string) (index : int) : Z :=
  match remaining with
  | O => 0
  | S remaining' =>
      get_uint8 value index +
      256 * read_unsigned_le_nat remaining' value (index + 1)
  end.

Definition get_int64_be (value : string) (index : int) : int64 :=
  signed_value 64 (read_unsigned_be_nat 8 value index).

Definition get_int64_le (value : string) (index : int) : int64 :=
  signed_value 64 (read_unsigned_le_nat 8 value index).

Definition get_int64_ne : string -> int -> int64 := get_int64_le.

(** OCaml's seeded hash is tied to its runtime implementation. *)
Parameter hash : t -> int.
Parameter seeded_hash : int -> t -> int.

Definition unsafe_get : string -> int -> ascii := get.

Parameter unsafe_blit : string -> int -> bytes -> int -> int -> unit.

Definition equal : t -> t -> bool := Strings.String.eqb.

Definition compare (left right : t) : int :=
  if Strings.String.eqb left right then
    0
  else if RocqOfOCaml.Basics.String.ltb left right then
    -1
  else
    1.
