# Soundness TODOs for `monad-execution-specs`

This file tracks translator work needed to replace the current guard-check
bypasses and arbitrary fallback values for the `monad-execution-specs`
translation. The translator must warn whenever it relies on one of the
mechanisms below.

## Assertions and exceptions (implemented)

- The generated support library defines distinct fallback classes:

  ```rocq
  Class Unreachable (T : Type) := {
    unreachable : T
  }.

  Class Unimplemented (T : Type) := {
    unimplemented : T
  }.
  ```

- `assert`, `raise`, `invalid_arg`, ordinary `failwith`, unmatched exception
  propagation, and unmatched dynamic variants use `Unreachable`.
- Only `failwith "todo ..."` uses `Unimplemented`.
- Every definition exposes the required type-specific class constraints,
  including requirements at concrete result types. Those constraints
  propagate through calls, module projections, signatures, and synthesized
  functor-result records. The translator does not synthesize inhabitants.
- The translator warns with the source location whenever it introduces either
  assumption.
- It is the user's responsibility to prove that every `Unreachable`
  occurrence is unreachable, and that every `Unimplemented` occurrence is
  outside the executions covered by a correctness theorem.

## Coinductive types (partial computations implemented)

- Model lazy, potentially infinite types such as OCaml's `Seq.t` using
  coinduction rather than unchecked recursion or an unconditional list
  replacement.
- Preserve the thunked observation interface of `Seq.t`.
- Give productive producers and transformations, including `Seq.ints`,
  `Seq.repeat`, `Seq.forever`, and `Seq.map`, guarded `CoFixpoint`
  definitions.
- Check the execution-relevant finite pipelines in `monad-execution-specs`,
  especially `Seq.take n (Seq.ints k)`, map/set traversal, MPT construction,
  and monadic traversal.
- Treat consumers that may inspect an unbounded number of sequence elements
  as a termination issue; coinduction alone does not make them productive.
- Recursive functions explicitly classified as `partial` now translate to
  `Delay.t` or monadic `Resumption.t`. Their changed result types propagate
  through calls, module signatures, includes, and synthesized functor results.
- A `convergent` caller can recover the source result type using an explicit
  convergence proof. The translator currently admits that proof obligation
  and warns at its source definition.
- The compatibility implementation of OCaml's general `Seq` operations still
  uses guard-check bypasses. Replacing that library with a guarded
  observational model remains necessary.

## Termination

Remove blanket `Unset Guard Checking` and classify every recursive
definition before translating it.

The translator accepts explicit `structural`, `well_founded`, `partial`, and
`convergent` recursion strategies, supplied by an attribute or configuration.
Unclassified recursion is emitted as an ordinary `Fixpoint`, leaving Rocq's
guard checker to accept or reject it. Well-founded definitions use an abstract
measure and `Program Fixpoint`; partial definitions use an explicit partial
computation; convergent definitions introduce a convergence obligation.

### Actually terminating

- Ordinary `Fixpoint` definitions are emitted for structurally recursive
  functions and checked by Rocq.
- Top-level, local, and mutually recursive definitions can be translated with
  `Program Fixpoint` using a well-founded measure.
- Generate named decreasing obligations and warnings when automation cannot
  discharge them.
- Cover project examples such as list traversal, bytecode scanning, bounded
  memory traversal, RLP decoding, trie traversal, and substring search.
- Establish suitable gas and call-depth measures for the VM execution loop
  and nested host/VM execution.
- Replace the unrestricted recursive-module fixed point used for `Host` and
  `Vm` with a project-specific construction justified by gas, call depth, or
  an explicit depth index.

### Actually possibly non-terminating

- Identify functions that can genuinely diverge, rather than forcing Rocq to
  accept them as total functions.
- Include traversal of arbitrary infinite `Seq.t` values and lookup in
  malformed cyclic graph representations in this category.
- Explicitly classified partial functions use `Delay.t` or `Resumption.t`.
- Warn whenever translation changes a possibly non-terminating function's
  interface or introduces a fuel/partiality boundary.
- Do not use an unrestricted fixed point or a false decreasing obligation to
  encode genuine divergence.
