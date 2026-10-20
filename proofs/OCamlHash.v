Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.

Local Open Scope Z_scope.

(** OCaml 5.4's 32-bit MurmurHash mixing, expressed with modular [Z]
    arithmetic. This models the integer paths in [runtime/hash.c], not
    generic traversal of OCaml heap values. The supported host is 64-bit.
    Source: https://github.com/ocaml/ocaml/blob/5.4.0/runtime/hash.c *)
Definition uint32 (value : Z) : Z := value mod 4294967296.

Definition rotate_left (value count : Z) : Z :=
  Z.lor (uint32 (Z.shiftl (uint32 value) count))
    (Z.shiftr (uint32 value) (32 - count)).

Definition mix (hash data : Z) : Z :=
  let data := uint32 (uint32 data * 3432918353) in
  let data := uint32 (rotate_left data 15 * 461845907) in
  uint32 (rotate_left (Z.lxor (uint32 hash) data) 13 * 5 + 3864292196).

Definition finish (hash : Z) : int :=
  let hash := uint32 hash in
  let hash := uint32 (Z.lxor hash (Z.shiftr hash 16) * 2246822507) in
  let hash := uint32 (Z.lxor hash (Z.shiftr hash 13) * 3266489909) in
  Z.land (Z.lxor hash (Z.shiftr hash 16)) 1073741823.

Definition mix_intnat (seed value : Z) : Z :=
  mix seed (Z.lxor (Z.lxor (Z.shiftr value 32) (Z.shiftr value 63)) value).

(** Generic hashing sees the tagged representation of an immediate [int].
    The caller supplies a canonical signed 63-bit value. *)
Definition seeded_int (seed value : Z) : int :=
  finish (mix_intnat seed (2 * value + 1)).

(** [runtime/ints.c:int64_hash] first XORs the two halves. It does not
    call [caml_hash_mix_int64], which would mix the halves separately. *)
Definition seeded_int64 (seed value : Z) : int :=
  finish (mix seed (Z.lxor (uint32 value) (uint32 (Z.shiftr value 32)))).

Example int64_42 : seeded_int64 0 42 = 1043574520 := eq_refl.
