# Machine Integer Semantics

The compatibility runtime models **64-bit OCaml**. The translator rejects a
32-bit host instead of silently using the wrong widths. Cross-compilation to
32-bit OCaml is not supported by this runtime.

| OCaml values | Gallina carrier | Arithmetic |
| --- | --- | --- |
| `int`, `Int.t` | `Z` | Signed 63-bit, modulo `2^63` |
| `Int32.t` | `Z` | Signed 32-bit, modulo `2^32` |
| `Int64.t` | `Z` | Signed 64-bit, modulo `2^64` |
| `Nativeint.t` | `Z` | Signed 64-bit on the supported platform |
| Zarith `Z.t` | `Z` | Arbitrary precision; no machine-width reduction |
| Project-configured natural numbers | `N` | Unchanged by this mapping |

For a width `w`, `OCamlMachineInt.Make` uses the existing
`OCamlZ.signed_repr`: first compute `u = x mod 2^w`, then return `u - 2^w`
when `u >= 2^(w-1)`, otherwise `u`. A nonnegative remainder alone would not
model signed OCaml values correctly.

## Translation

Stdlib arithmetic and bitwise operators, including first-class operator values,
are mapped to `OCamlInt` helpers. `Int`, `Int32`, `Int64`, and `Nativeint` use
the same width-parameterized implementation. Each intermediate operation wraps,
not just the final function result. Signed division truncates towards zero;
`min_int / -1`, `-min_int`, and `abs min_int` all return `min_int`.
Logical right shift masks the input to an unsigned bit pattern before shifting.
Arithmetic right shift replicates the sign bit.

Narrowing integer conversions use the **destination** width. For example,
`Int64.to_int Int64.max_int` is `-1` on the supported platform. Widening a
canonical signed integer preserves its value. Checked Zarith conversions remain
checked: they are not silently replaced by truncating conversions.

Integer literals are printed exactly, including 64-bit literals and match
patterns; they are never passed through the host's narrower tagged `int`.
Finite `Seq.take count (Seq.ints start)` lowering also wraps when it crosses
`max_int`.

String conversions have different overflow rules from arithmetic. The native
parser accepts signed decimal or unsigned base-prefixed bit patterns, including
`0u`, and then applies the optional sign. Out-of-range or malformed input
returns `None` from `of_string_opt`, not a wrapped value. The implementation
follows [OCaml 5.4's integer runtime](https://github.com/ocaml/ocaml/blob/5.4/runtime/ints.c).
The [Int](https://ocaml.org/manual/5.4/api/Int.html) and
[Int64](https://ocaml.org/manual/5.4/api/Int64.html) interfaces specify the
arithmetic and conversion contracts.

## Proof Boundary

`Z` does not enforce a finite range. A translated function's external inputs
must represent actual OCaml values, e.g. `-2^62 <= x < 2^62` for `int`.
The runtime does not pretend an arbitrary unbounded `Z` is an OCaml integer.
Fixed-width arithmetic preserves canonical signed values. Source-defined
fixed-width unsigned abstractions retain their own normalization operations;
this change does not insert a global modulus into arbitrary-precision code.

`OCamlInt.repr_range`, `repr_small`, and `add_no_overflow` are proved lemmas.
They allow arithmetic proofs to use ordinary addition once the relevant range
condition is established. `Termination.IncreasingIndex` includes a corresponding
machine-addition decrease lemma. Termination arguments based on an increasing
machine integer must account for wraparound; they cannot blindly assume that
`x + 1 > x`.

Division by zero and invalid throwing parsers use the existing typed
`Unreachable` argument and propagate it to translated callers. They are not
assigned a fabricated successful result, and this work does not model caught
exceptions or prove exception avoidance. Shifts with counts outside the range
specified by OCaml have no equivalence claim. Existing float conversions,
floating-point bit casts, and representation-dependent hashing are outside
this arithmetic correction. This is not a whole-translator soundness proof or
an assertion that all compatibility-library behavior has been verified.

## Reproduction

In the project's OCaml/Rocq environment:

```sh
dune build -p rocq-of-ocaml
(cd proofs && ./configure.sh && make -j4)
ruby test.rb
```

The regular suite checks translation snapshots and compiles them in Rocq. Its
machine-integer differential test also compiles OCaml wrappers with `ocamlopt`,
executes them, translates the same wrappers, and checks their results by Rocq
`vm_compute` proofs. Cases cover boundary and seeded random operands, signed and
unsigned division, specified shifts, narrowing/widening, malformed and
overflowing strings, literal patterns, operator aliases, branch decisions after
overflow, finite sequences, and an arbitrary-precision Zarith negative control.
No expected arithmetic answers are calculated by a Ruby wrapping model.

The differential test can be run alone:

```sh
ruby tests/machine_integers/differential.rb
```

Artifacts remain under `_build/machine-integer-differential`. To check against
an independently built predicative copy of the runtime, set `INTEGER_RUNTIME`
to its `proofs` directory and `PREDICATIVE=1`. The test introduces no axioms;
its `Unreachable` instances are explicit, concrete inhabitants, unused on the
successful native cases. Passing these tests is evidence, not a mechanized
proof that OCaml's implementation and Gallina agree on every input.
