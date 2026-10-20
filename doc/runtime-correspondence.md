# Runtime Correspondence Checks

The runtime replaces selected OCaml libraries with Gallina definitions. A
successful Rocq build checks those definitions and their proofs, not their
equivalence to the native libraries. The differential suites test that separate
claim by executing native OCaml and checking the translated wrappers with
`vm_compute`.

## Corrected Operations

- `Map.of_list` inserts left to right, so the last duplicate key wins.
- `Z.erem` returns the nonnegative representative for either sign of divisor.
- `Z.powm` uses the absolute modulus and computes an inverse for negative
  exponents when one exists. Zero modulus and noninvertible negative powers
  follow the existing typed `Unreachable` convention.
- `Bigstring.init` constructs the requested bytes. It is no longer an axiom.
  This is a pure byte-content model, not a model of allocation, aliasing,
  mutation, or effectful callbacks. Invalid lengths use a typed fallback.
- Integer guards in list/sequence helpers use actual integer comparisons.
  The translator specializes scalar integer, character, and string comparisons
  where their source types are known; genuinely polymorphic comparisons remain
  an explicit boundary.
- Library fallback requirements retain public result types instead of exposing
  expanded representation types, such as a Bigstring's backing bigarray.
- `Z.to_bits` includes whole 64-bit-limb padding, as native Zarith does.
  `OCamlZ.to_bits_minimal` is an explicitly separate canonical encoder.
  `OCamlZBits.minimal_is_native_prefix` proves their significant-byte-prefix
  relationship for every integer; `native_byte_length` proves the padded size.
- `Int64.hash` and `Int64.seeded_hash` use the native custom-block hash and
  OCaml's 32-bit mixing/finalization, not identity or XOR approximations.
- `Z.hash` and `Z.seeded_hash` are executable, not axioms. They distinguish
  tagged immediate integers from boxed Zarith values, including sign and
  zero high halves of limbs. Negative and large seeds are reduced to 32 bits.

Machine overflow and conversion corrections are documented separately in
[machine-integers.md](machine-integers.md). Arbitrary-precision integers remain
unbounded. Project-owned unsigned parsers should compose `OCamlZ.of_string_opt`
with their nonnegativity check instead of duplicating the parser.

## Reproduction

After building the translator and runtime in the pinned toolchain:

```sh
ruby tests/runtime/differential.rb
ruby tests/machine_integers/differential.rb
ruby test.rb
```

The full test command, used by CI, includes both differential suites. The
runtime suite requires Zarith and Bigstring, declared as test dependencies.
Its artifacts are retained in `_build/runtime-differential`: native wrappers,
oracle, generated Gallina, and checked comparison statements. Set `RUNTIME`
to another built runtime's `proofs` directory and `PREDICATIVE=1` to check
against a predicative runtime without `-impredicative-set`.

The runtime suite checks duplicate maps, sorting, bounded sequence consumers,
byte initialization, scalar comparisons, Zarith parsing, signed modular
arithmetic, byte serialization and seeded/unseeded integer hashing. Byte and
hash cases cover zero, both signs, byte/limb/immediate-integer boundaries,
and seeded random values through 512 bits. Expected results come from the
installed native libraries, not a second hashing model in the test runner.
On exceptional native inputs it checks the explicitly chosen
fallback, not exception-handler semantics or exception avoidance. No tests
assume an arbitrary inhabitant or bypass kernel checks.

## Native Versions and Client Migration

The byte and hash implementations follow 64-bit OCaml 5.4 and Zarith 1.14:
[OCaml hash mixing](https://github.com/ocaml/ocaml/blob/5.4.0/runtime/hash.c),
[the Int64 custom hash](https://github.com/ocaml/ocaml/blob/5.4.0/runtime/ints.c),
and [Zarith serialization/custom hashing](https://github.com/ocaml/Zarith/blob/release-1.14/caml_z.c).
These observable results are version/platform-sensitive; the native
differential gate must be rerun when those dependencies change. This is an
executable model with checked local lemmas and differential evidence, not a
mechanized proof about the C implementations.

Generated calls to native `Z.to_bits` continue to use that name. A handwritten
replacement needing minimal bytes must explicitly use `to_bits_minimal` or
`to_bits_bytes` with its significant byte count. Do not rename all source
calls to the minimal helper: native callers can observe the padded length.
The companion project change makes `UintN.to_bytes_be` explicitly canonical,
preserving its RLP round-trip and length proofs.

## Remaining Foreign Contracts

`Z.format` and `Z.legendre` remain foreign primitives under the existing FFI
policy. `format` means Zarith's exact string result, including its formatting
flags and prefixes; it is not just any human-readable rendering. `legendre`
means GMP's symbol on the documented domain. A bare parameter does not prove
either correspondence. The same applies to the retained cryptographic FFI
and native string-hash declarations. They remain explicit trust boundaries,
not fabricated executable answers. The realizability witness proves only
logical consistency of the remaining signatures.

## Remaining Boundaries

These changes do not settle general polymorphic hashing, physical equality,
floating-point models, the remaining FFI contracts,
or general effectful/infinite OCaml sequences. They neither prove whole-program
translation correctness nor replace the project's assumption census and kernel
checks. Downstream proof builds must be rerun after changing the runtime;
particularly, machine-arithmetic proofs must account for overflow.
