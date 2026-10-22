# Separate Termination Proofs

## Purpose and Status

Implementation: `aa755/separate-termination-proofs`, commit `f9019945`.
This document is also available on `aa755/machine-integer-semantics`; the
implementation and fixtures are **only on the experiment branch**.

The current mechanism inserts a tactic inside a generated recursive definition.
That is awkward when the termination proof needs to import the generated body:
the imports would form a cycle. This experiment separates the body, proof, and
public function, without requiring an OCaml source refactor.

**Prototype only:** flat, monomorphic, first-order functions with one to three
arguments. Local/mutual recursion, modules, functors, recursive higher-order
callbacks, and function-valued results are unsupported. It has not been
integrated into the full project and lacks later ordinary-branch fixes.

## Three Files

| File | Maintained by | Contents |
| --- | --- | --- |
| `X_internal.v` | Translator | One-step bodies; section parameters for termination proofs; total functions using `mu1`, `mu2`, or `mu3`. |
| `X_termproofs.v` | User | Proofs importing `X_internal.v` and existing proof libraries, with measures defined here rather than in JSON. |
| `X.v` | Translator | Public wrappers that supply the proved termination arguments. |

Nonstructural functions can be selected using `[@rocq.wf]` or
`recursion_strategies`. This mode rejects accompanying
`termination_certificates` entries, since the proofs now live separately.

A missing proof file gets a template ending in `Abort`, not `Admitted`.
The public wrappers cannot compile until the required theorems exist.
Regeneration replaces internal/public files but never overwrites the proof file.

## Example and Proof Reuse

The generated `tests/separate_termination/Count_internal.v` contains this
shape, with names shortened:

```coq
Section TerminationParameters.
Definition count_up_body (rec : int -> option int) (value : int) :=
  if Z.geb value 3 then Some value else rec (OCamlInt.add value 1).
Variable count_up_terminates : Separate.Terminates1 count_up_body.
Definition count_up := Separate.mu1 count_up_body count_up_terminates.
End TerminationParameters.
```

`Count_termproofs.v` imports this body and reuses the existing
`IncreasingIndex.increasing_index_machine_step_decreases` lemma.
`Separate.terminates1_by_measure` connects that ranking argument to the
termination certificate. The same existing argument is reused for two/three
arguments and non-tail calls; it was not rediscovered.

Earlier definitions can occur in later bodies and measures. Their proof
parameters are carried through section dependencies and supplied by the public
wrappers. The `after_previous` fixture checks this case.

## The Combinator

```coq
body : (A -> option B) -> A -> option B
Terminates1 body := forall x, exists n v, run1 body n x = Some v
```

`run1` is a structurally recursive fuel evaluator. `mu1` uses constructive
finite search and the termination proof to return a `B`. `mu2` and `mu3`
hide tuple packing. The combinators introduce no choice axiom, default result,
guard-check bypass, or impredicative-Set requirement.

The `option` is important: recursive calls are sequenced strictly even when
their result is discarded. Otherwise
`let rec f x = let _ = f x in 0` could incorrectly become the constant zero.
Here `None` means unfinished recursion, **not an OCaml exception**.

Unfolding and independence from the termination proof additionally require
`Monotone1`: completing more recursive calls cannot change an existing answer.
The examples prove it; the translator does not yet generate that proof.
Constructive search is a reference implementation, not an efficient extracted
runtime. Opaque certificates can obstruct reduction; the proved equations offer
an alternative way to reason about results.

## Build and Check

The following commands run from the root of a checkout of
`aa755/separate-termination-proofs`, with `SWITCH` containing the name or
absolute path of an existing switch with the repository dependencies
(OCaml 5.4.0 and Rocq 9.0.1 were used):

```sh
opam exec --switch="$SWITCH" -- dune build -p rocq-of-ocaml
(cd proofs &&
  opam exec --switch="$SWITCH" -- rocq makefile -f _CoqProject -o Makefile &&
  opam exec --switch="$SWITCH" -- make -j2)
opam exec --switch="$SWITCH" -- rocq c -Q proofs RocqOfOCaml \
  proofs/Termination/Separate.v
opam exec --switch="$SWITCH" -- ruby tests/separate_termination/check.rb
```

**Runtime qualification:** the experiment's legacy `proofs/_CoqProject` uses
`-impredicative-set`. The combinator and fixture checks above omit that flag;
this is not a completed predicative migration of the entire runtime.

The harness regenerates in a fresh temporary directory and checks all three
files, sixteen closed assumption reports, reuse of unchanged proofs, rejection
of stale/missing proofs, discarded-call divergence, and fail-closed handling of
unsupported inputs. It also checks short-circuiting, binding hygiene, pattern
matches, and repeated calls. These tests are not a general proof that the
translator preserves OCaml semantics; other runtime abstractions still apply.

## Updating Proofs

A typical update would regenerate the bodies and recompile the handwritten
proofs against them. Unchanged definitions reuse the old proof; changed
definitions require it to check again. New functions need corresponding proofs;
generation never silently admits obligations or updates the handwritten file.

A passing Git revision provides a useful comparison point. During a port,
`git show BASE:tests/separate_termination/Count_internal.v` shows the old body;
a worktree at `BASE` provides a compilable old proof beside the new one.

## Remaining Work

Possible next steps are:

1. **Updating the implementation.** A port onto the latest ordinary translator
   would retain the arithmetic and module fixes. This mode could remain opt-in
   while its coverage is incomplete.
2. **Local recursion, modules, and functors.** Captured variables could become
   explicit parameters of local one-step bodies. Module/type contexts and
   termination-proof parameters would then flow through callers and wrappers,
   including dependencies on earlier definitions in the same file.
   Another option is to simplify the OCaml source by replacing unnecessary
   functors with concrete modules or explicit function parameters, reducing
   translation and proof complexity. This could be an optional upstream
   simplification, rather than a prerequisite for translating main.
3. **Mutual recursion.** A tagged call state and one joint termination
   certificate could represent a recursive group, with wrappers exposing the
   original functions. This would preserve the OCaml source layout.
4. **The proof interface.** Generated monotonicity proofs, or explicit
   obligations, would make unfolding and proof-independence lemmas available.
   Generic functor laws could remain explicit proof parameters, discharged by
   concrete applications rather than supplied as assumed instances.
5. **Reusing project proofs.** Existing measures and lemmas could be adapted
   into handwritten `X_termproofs.v` files. The target remains public main after
   comparison removal and possibly the RLP PR described in [WIP.md](../WIP.md),
   without runtime progress checks or proof-driven OCaml refactors. Corrected
   arithmetic still requires repairing affected arguments.
6. **End-to-end validation.** A useful completion check would build the runtime
   and generated project predicatively, with no new admissions or disabled
   kernel checks. Local/mutual/functor regressions, proof-reuse tests, native
   comparisons, and the full proof build and assumption audit would cover the
   new behavior on the target source.

If execution performance becomes important, a later optimization could replace
constructive search, with a proof of agreement with the current combinator.
That is separate from making the proof architecture work.
