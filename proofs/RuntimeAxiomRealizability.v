From Stdlib Require Import Ascii String ZArith.
Require Import RocqOfOCaml.Libraries RocqOfOCaml.Basics
  RocqOfOCaml.Bigstring RocqOfOCaml.Digestif
  RocqOfOCaml.Libsecp256k1 RocqOfOCaml.OCamlBigarray
  RocqOfOCaml.OCamlString RocqOfOCaml.OCamlZ.

Local Open Scope Z_scope.

(** The signatures used by the project theorem census can be instantiated
    simultaneously by closed Gallina terms. This establishes logical
    realisability, not the behaviour of the native cryptographic, hashing,
    formatting, or physical-equality implementations. The actual bundle
    below checks these signatures against the translator's declarations.
    The current 696-theorem census uses 19 axiom names; this bundle also
    includes [Context.t], needed by the dependent secp256k1 signatures. *)
Record axiom_bundle : Type := {
  model_physical_equal : forall {A : Set}, A -> A -> bool;
  model_polymorphic_compare : forall {A : Set}, A -> A -> int;
  model_bigstring_init : int -> (int -> ascii) -> Bigstring.t;
  model_keccak_256 : Digestif.S;
  model_rmd160 : Digestif.S;
  model_sha256 : Digestif.S;
  model_context_type : Set;
  model_context_create :
    option bool -> option bool -> unit -> model_context_type;
  model_key_public : Set;
  model_key_type : Set -> Set;
  model_key_to_bytes :
    option bool -> model_context_type ->
    forall {kind : Set}, model_key_type kind -> Bigstring.t;
  model_key_to_bytes_uncompressed_length :
    forall (context : model_context_type)
      (key : model_key_type model_key_public),
      OCamlString.length
        (model_key_to_bytes (Some false) context key) = 65;
  model_sign_recoverable : Set;
  model_sign_type : Set -> Set;
  model_recoverable_bytes : int;
  model_read_recoverable :
    model_context_type -> Bigstring.t ->
    sum (model_sign_type model_sign_recoverable) string;
  model_recover :
    model_context_type -> model_sign_type model_sign_recoverable ->
    Bigstring.t -> sum (model_key_type model_key_public) string;
  model_z_legendre : Z -> Z -> int;
  model_z_hash : Z -> int;
  model_z_format : string -> Z -> string;
}.

Definition actual_bundle : axiom_bundle :=
  {|
    model_physical_equal := @Basics.Stdlib.physical_equal;
    model_polymorphic_compare := @Basics.Stdlib.polymorphic_compare;
    model_bigstring_init := Bigstring.init;
    model_keccak_256 := Digestif.KECCAK_256;
    model_rmd160 := Digestif.RMD160;
    model_sha256 := Digestif.SHA256;
    model_context_type := Libsecp256k1.External.Context.t;
    model_context_create := Libsecp256k1.External.Context.create;
    model_key_public := Libsecp256k1.External.Key.public;
    model_key_type := Libsecp256k1.External.Key.t;
    model_key_to_bytes := @Libsecp256k1.External.Key.to_bytes;
    model_key_to_bytes_uncompressed_length :=
      Libsecp256k1.External.Key.to_bytes_uncompressed_length;
    model_sign_recoverable := Libsecp256k1.External.Sign.recoverable;
    model_sign_type := Libsecp256k1.External.Sign.t;
    model_recoverable_bytes := Libsecp256k1.External.Sign.recoverable_bytes;
    model_read_recoverable := Libsecp256k1.External.Sign.read_recoverable;
    model_recover := Libsecp256k1.External.Sign.recover;
    model_z_legendre := OCamlZ.legendre;
    model_z_hash := OCamlZ.hash;
    model_z_format := OCamlZ.format;
  |}.

Definition digest_witness : Digestif.S :=
  {|
    Digestif.S.digest_string := fun _ _ value => value;
    Digestif.S.to_raw_string := fun value => value;
  |}.

Fixpoint uncompressed_key_witness (n : nat) : string :=
  match n with
  | Datatypes.O => EmptyString
  | Datatypes.S remaining => String (Ascii.ascii_of_nat 0)
      (uncompressed_key_witness remaining)
  end.

Lemma uncompressed_key_witness_length :
  OCamlString.length (uncompressed_key_witness 65%nat) = 65.
Proof. vm_compute. reflexivity. Qed.

Definition closed_bundle : axiom_bundle :=
  {|
    model_physical_equal := fun _ _ _ => false;
    model_polymorphic_compare := fun _ _ _ => 0;
    model_bigstring_init := fun _ _ => EmptyString;
    model_keccak_256 := digest_witness;
    model_rmd160 := digest_witness;
    model_sha256 := digest_witness;
    model_context_type := unit;
    model_context_create := fun _ _ _ => tt;
    model_key_public := unit;
    model_key_type := fun _ => unit;
    model_key_to_bytes := fun _ _ _ _ => uncompressed_key_witness 65%nat;
    model_key_to_bytes_uncompressed_length :=
      fun _ _ => uncompressed_key_witness_length;
    model_sign_recoverable := unit;
    model_sign_type := fun _ => unit;
    model_recoverable_bytes := 0;
    model_read_recoverable := fun _ _ => inr EmptyString;
    model_recover := fun _ _ _ => inr EmptyString;
    model_z_legendre := fun _ _ => 0;
    model_z_hash := fun _ => 0;
    model_z_format := fun format _ => format;
  |}.

Print Assumptions closed_bundle.
