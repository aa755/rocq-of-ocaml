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
byte initialization, scalar comparisons, Zarith parsing, and signed modular
arithmetic. On exceptional native inputs it checks the explicitly chosen
fallback, not exception-handler semantics or exception avoidance. No tests
assume an arbitrary inhabitant or bypass kernel checks.

## Remaining Boundaries

These changes do not settle raw `Z.to_bits` padding, representation-sensitive
hashing, physical equality, floating-point models, cryptographic FFI contracts,
or general effectful/infinite OCaml sequences. They neither prove whole-program
translation correctness nor replace the project's assumption census and kernel
checks. Downstream proof builds must be rerun after changing the runtime;
particularly, machine-arithmetic proofs must account for overflow.
