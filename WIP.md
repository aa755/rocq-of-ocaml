# OCaml-to-Rocq Work in Progress

## 1. Version That Builds

- OCaml: `monad-execution-specs`, branch `cmcl/exp-rocq-baseline`, commit `6cee08b`.
- Translator: `d3afb526`.

Fresh translation, all sidecar proofs, assumption audits, and predicative kernel
checking passed on 2026-10-21. **This version still has arithmetic-translation
bugs and proof-driven OCaml changes absent from main.** See
[Problems in This Version](#problems-in-this-version). A successful build does
not establish equivalence to OCaml or axiom-freedom.

## 2. Corrected Translator and Target

`aa755/machine-integer-semantics` (code at `8470aaec`) fixes machine-integer
wrapping, shifts, narrowing, and several runtime replacements. These corrections
break termination arguments that relied on the old arithmetic. Translator tests
pass, but **a complete project translation with the repaired proofs does not**.

The goal is to translate **public main**, after
[Ryan's polymorphic-comparison removal PR #68](https://github.com/category-labs/monad-execution-specs/pull/68)
and perhaps [the RLP result-returning PR #70](https://github.com/category-labs/monad-execution-specs/pull/70)
merge. PR #70 is branch `aa755/rlp-result`, based on Ryan's PR.
Main does not contain the proof-driven changes listed below; they are not
prerequisites for this work.

Reuse the existing proofs, repair their arithmetic arguments, and establish
progress without adding runtime progress checks to OCaml. Some translator/proof
integration remains unfinished, including generic termination laws and their
concrete instances. The final check must regenerate and build from that source.

## 3. Separate-Proof Experiment

`aa755/separate-termination-proofs` (`f9019945`) lets a termination proof
import the generated function body without creating an import cycle.
Measures and substantial proofs then live in ordinary Rocq files, not JSON or
embedded tactics. See [Separate Termination Proofs](doc/separate-termination.md).

This is a prototype for flat functions of one to three arguments, not yet
local/mutual recursion or functors. It is not a replacement for the current
project translation.

## Problems in This Version

These apply to the building version in section 1.

**Arithmetic:** ordinary OCaml `int` addition/subtraction/multiplication became
unbounded `Z` operations rather than signed 63-bit arithmetic on a 64-bit host.
Logical right shift was mapped to `Z.shiftr`, which sign-extends negatives.
Some narrowing conversions and overflow parsing were also wrong. For example,
`max_int + 1` did not wrap to `min_int`. The corrected translator addresses
these problems; the old termination proofs cannot simply be reused unchanged.

**Proof-driven OCaml changes:**

| Source | Changes made to ease proofs |
| --- | --- |
| `rlp.ml` | Check that list payloads and remainders shrink before recursion; raise `invalid_arg` otherwise. |
| `mpt.ml` | Add key-depth/child-index checks; expose a local recursive worker; replace a finite `Seq` traversal with a list traversal. |
| `ec/algebra.ml` | Check remainder/polynomial degree decreases before recursing; raise `invalid_arg` otherwise; hoist a loop bound. |
| `vm.ml` | Check gas decreases on every continuing iteration; reject some host gas results; hoist bounds and opcode selection; replace an assertion with an explicit failure. |

These checks hand decrease facts to small proof tactics instead of deriving
them from the original operations. Some introduce additional failure paths;
they are not all cosmetic refactors.

## Build the Version That Passes

The source branch is currently local; publish it before using these clone
commands. The latest translator changes and separate-proof experiment are
also unpushed. Prerequisites: initialized opam, C/make tools, Python 3, Ruby,
jq, and ripgrep.

```sh
git clone --branch cmcl/exp-rocq-baseline \
  https://github.com/category-labs/monad-execution-specs.git monad-rocq
cd monad-rocq
mkdir -p .rocq-tools
git clone https://github.com/aa755/rocq-of-ocaml.git .rocq-tools/rocq-of-ocaml
git -C .rocq-tools/rocq-of-ocaml switch --detach d3afb526

opam switch create --no-switch "$PWD/.opam-rocq-of-ocaml" \
  ocaml-variants.5.4.0+options ocaml-option-flambda --yes
export ROCQ_OPAM_SWITCH="$PWD/.opam-rocq-of-ocaml"
export ROCQ_OF_OCAML_ROOT="$PWD/.rocq-tools/rocq-of-ocaml"
sh rocq/scripts/bootstrap.sh
sh rocq/scripts/generate-rocq.sh
DUNE_CACHE=disabled sh rocq/check-translation.sh
```

Generation writes ignored `rocq/generated/next/`; the check builds those files
and `proofs/rocq/` in a fresh directory using the pinned, predicative runtime.
These commands reproduce section 1, **not** the unfinished target in section 2.

## Architecture and Knobs

The project script builds OCaml typed artifacts, orders compilation units,
and invokes the translator with dependency metadata. The translator uses
Merlin's typed tree, emits Gallina, and records cross-file requirements;
**Rocq checks the proofs afterward**, not during translation.

In the translator, `src/rocqOfOCaml.ml` is the driver; `structure.ml`, `exp.ml`,
`type.ml`, and `moduleTyp.ml` translate declarations, expressions, types, and
modules. Functors/signatures become records/functions carrying associated
types and requirements. `assumptionMetadata.ml` propagates those requirements.
Translator `proofs/` implements primitives; project `rocq/support/` contains
intentional replacements. Their behavior needs auditing independently.

Configure `rocq/config/translation.json`, selecting by file suffix and qualified
**definition name**, not line number:

| Knob | Purpose |
| --- | --- |
| `recursion_strategies` | `well_founded` for nonstructural total recursion; `partial` for genuine divergence, propagating `Delay`/`Resumption` through callers. Ordinary structural recursion needs no certificate. |
| `termination_certificates` | A `nat` measure over `_rocq_state` plus a decrease-proof tactic. Arguments are tupled; mutual recursion uses tagged states. |
| `file_head_suffixes` | Import the sidecar containing the measure, lemmas, and tactic. |
| `module_overrides`, renamings | Substitute Gallina implementations, e.g. `Numeric.Uint` with `UintN`. |
| `excluded_definitions` | Omit unused declarations, not reachable behavior. |
| `module_laws` (new branch) | Explicit proof parameters for generic functor operations; concrete instances must prove them. |
| Certificate domain/fallback (new branch) | Optionally check the representable domain, specify the outside result, and prove preservation/decrease inside. |
| `forbid_polymorphic_comparison` (new branch) | Reject unmodeled comparison operations. |

`well_founded` alone is not a proof: provide its certificate and reject
remaining admissions. Never use guard-check bypasses. See
`src/configuration.ml` and `doc/docs/configuration.md` for syntax; the latter
still contains obsolete advice about disabling guard checking.

Keep reusable lemmas in sidecar proof files. The configured tactic applies
them inside the generated definition, where local variables and branch facts
are available. A sidecar imported by `X.v` cannot itself import `X.v`; this is
the dependency problem addressed by the separate-proof experiment.
Retranslation preserves handwritten proofs but requires them to be rechecked.
