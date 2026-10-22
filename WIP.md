# OCaml-to-Rocq Work in Progress

## Which Branches

**Development target:** `monad-execution-specs` branch `aa755/rlp-result`
(`3dfcf34`), our RLP PR on top of Ryan's comparison PR, then public `main`
once merged. The translator must work on that source, without requiring the
additional OCaml refactors from the integration experiment. There is **no
passing full build of this target with the corrected translator yet**.

| Purpose | OCaml project | Translator |
| --- | --- | --- |
| Development target (not yet passing) | [monad-execution-specs](https://github.com/category-labs/monad-execution-specs), `aa755/rlp-result`, `3dfcf34` | `aa755/machine-integer-semantics`, code at `8470aaec` |
| Historical guarded reproduction | `cmcl/exp-rocq-baseline` | This repository, `d3afb526` |
| Unfinished proof/reference experiment, not a prerequisite | `cmcl/exp-main-translator-integration`, `10ab3956` | `aa755/machine-integer-semantics`, code at `8470aaec` |
| Separate-proof experiment | Not integrated | `aa755/separate-termination-proofs`, `f9019945` |

The baseline branch starts at public source commit `a5a25f9` and carries the
OCaml changes, sidecar proofs, support library, and build configuration for the
known-building snapshot. It retains the earlier RLP/MPT, algebra, and VM progress
guards; it is **not current public main or a proposal to merge those guards**.
The integration experiment adds RLP/MPT refactors and a VM step/loop split on
top of `aa755/rlp-result`. Its proofs and translator fixes are reusable work,
not a requirement to merge those source changes. Its full build is unfinished.

Verified on 2026-10-21: fresh baseline generation matched all 42 recorded hashes;
the complete proof build, assumption audits, and predicative kernel check passed.

**Publication status:** the two `cmcl/exp-*` project branches, separate-proof branch, and ordinary
translator continuation beyond public tip `38225cb9` are currently local. The
clone commands below require those branches to be published.

## Reproduce the Historical Build

These commands reproduce the guarded baseline only, not the development target.
After publication, from an empty directory:

```sh
git clone --branch cmcl/exp-rocq-baseline \
  https://github.com/category-labs/monad-execution-specs.git monad-rocq
cd monad-rocq
mkdir -p .rocq-tools
git clone https://github.com/aa755/rocq-of-ocaml.git .rocq-tools/rocq-of-ocaml
git -C .rocq-tools/rocq-of-ocaml switch --detach d3afb526

# Requires initialized opam, C/make tools, Python 3, Ruby, jq, and ripgrep.
opam switch create --no-switch "$PWD/.opam-rocq-of-ocaml" \
  ocaml-variants.5.4.0+options ocaml-option-flambda --yes
export ROCQ_OPAM_SWITCH="$PWD/.opam-rocq-of-ocaml"
export ROCQ_OF_OCAML_ROOT="$PWD/.rocq-tools/rocq-of-ocaml"
sh rocq/scripts/bootstrap.sh

# Translate this checkout's lib/*.ml into rocq/generated/next/.
sh rocq/scripts/generate-rocq.sh

# Compile the generated code and sidecar proofs, audit, and kernel-check.
DUNE_CACHE=disabled sh rocq/check-translation.sh
```

Generated output is ignored by Git. The check builds a fresh runtime from the
pinned translator and applies the predicative patch. `rocq makefile` orders
generated files, support modules, and proofs by imports. Logs are retained in
the printed `.rocq-tools/translation-check.*` directory. Do not substitute
the legacy impredicative runtime build.

The experiment's `rocq/check-integration.sh` is reference build infrastructure,
not a passing recipe for `aa755/rlp-result`. Its proof/configuration support
must be adapted to the target without carrying over its `lib/` refactors.
It uses Dune 3.24.2 (`ROCQ_DUNE` selects it) and OCaml 5.4.0; the public source's
native packaging specifies OCaml 5.5.1, whose `.cmt` files are incompatible.

## Architecture and Knobs

In the baseline and experiment, the project script builds typed artifacts, orders compilation units,
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

## Architecting Termination Proofs

**Put substantial mathematics in sidecar lemmas; keep the tactic as an adapter.**
For example, `proofs/rocq/Termination/Natural.v` proves
`positive_halving_decreases`: nonzero `n : N` has a larger rank than `n / 2`.
Its `solve_uint_halving_decrease` tactic extracts branch facts and applies that
lemma. The actual curve multiplication configuration is:

```json
"recursion_strategies": [
  ["lib/ec/curve.ml", "Make.*.loop", "well_founded"]
],
"termination_certificates": [
  ["lib/ec/curve.ml", "Make.*.loop",
   "let '(n_value, _, _) := _rocq_state in MonadExecutionSpecs.Termination.Natural.n_rank n_value",
   "MonadExecutionSpecs.Termination.Natural.solve_uint_halving_decrease"]
],
"file_head_suffixes": [
  ["lib/ec/curve.ml", "Require Import MonadExecutionSpecs.Termination.Natural."]
]
```

Generated `Ec/Curve.v` defines a measure and one-step body, inserts
`ltac:(...solve_uint_halving_decrease)` at recursive calls, and builds the
function using well-founded `Fix`. The tactic runs **inside the generated
definition**, with local types, captured variables, and branch equations in scope.
Thus proofs are maintained separately, but their applications are checked there.

- **Avoid import cycles:** a sidecar imported by `X.v` cannot import `X.v`.
  Parameterize reusable lemmas over types and operations.
- **When generated definitions are essential:** solve the import dependency
  in translation/proof scaffolding, not by requiring OCaml source refactors.
  The experiment's `Vm_step`/`Vm_loop` split illustrates the dependency but is
  not the target source layout. Reuse its progress lemmas; adapting their
  application to the original layout is still open. Generic functor laws
  remain explicit proof parameters, with proofs required for concrete instances.
- **Retranslation:** generated files are replaced; sidecars are preserved.
  Rocq rechecks certificates. Update lemmas/adapters when code changes; compare
  against the last passing commit in another worktree. Do not hand-edit the
  generated algorithm to make a proof pass.

## Next Work

Make the ordinary translator and sidecar proofs work on `aa755/rlp-result`,
then `main`, without depending on the experimental source refactors. Reuse the
existing RLP/MPT and gas-progress proofs, adapting their integration rather than
rewriting the target OCaml. Complete polynomial division/concrete Euclidean
laws and host-gas contracts, then run fresh generation, the full proof build,
and assumption/kernel audits on that exact source. The experiment's backlog
is evidence about prior attempts, not proof that this target builds.
Build success is not semantic equivalence or axiom-freedom.

The optional separate-proof branch emits `X_internal.v`, preserves
`X_termproofs.v`, and generates wrappers in `X.v`. Its constructive
`mu1`/`mu2`/`mu3` let proofs import one-step bodies without a cycle. See
`doc/separate-termination.md`. It supports only flat, monomorphic, first-order
functions of one to three arguments, not the project's local recursion or
functors, and lacks later ordinary-branch fixes. Do not use it as the integration base.
