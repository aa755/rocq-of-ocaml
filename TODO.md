# Soundness TODOs

This file tracks the remaining soundness work for translating exceptional
control flow, sequences, and recursion. The translator must warn whenever it
introduces one of the explicit assumptions or proof obligations below.

## Assertions and exceptions

Implemented:

- The support library defines distinct type-indexed classes:

  ```rocq
  Class Unreachable (T : Type) := {
    unreachable : T
  }.

  Class Unimplemented (T : Type) := {
    unimplemented : T
  }.
  ```

- Assertions, exceptions, partial library operations, and unmatched dynamic
  variants use `Unreachable`.
- Only explicitly recognized implementation stubs use `Unimplemented`.
- Required instances propagate through calls, projections, signatures,
  includes, functor results, and compilation-unit metadata.
- The translator warns at the source definition whenever either requirement
  is introduced.
- The translator does not synthesize inhabitants or global instances for
  either class.

The user must prove that each `Unreachable` operation is outside the executions
covered by a theorem and must supply a specification or implementation for
each reachable `Unimplemented` operation.

## Inductive and coinductive sequences

Implemented for finite profiles:

- A configuration can map `Seq.t` to an inductive finite sequence with the
  same one-step observation interface.
- A configuration can exclude general infinite producers and consumers.
- A profile can replace a known bounded producer/consumer pipeline with an
  equivalent finite operation.
- Encountering an excluded reachable operation is a translation error, not an
  arbitrary total value.

Remaining generic work:

- Translate arbitrary `Seq.t` with a coinductive observation model.
- Check productivity of sequence producers.
- Distinguish finite consumers, productive producers, divergence, and unknown
  behavior without relying on project-specific names.

## Termination and divergence

Implemented:

- Recursive definitions without an explicit strategy are emitted as ordinary
  `Fixpoint`s and accepted or rejected by Rocq's guard checker.
- The translator accepts explicit `structural`, `well_founded`, `partial`, and
  `convergent` strategies from attributes or configuration.
- Well-founded definitions use an abstract ranking function and emit explicit
  decrease obligations.
- Partial definitions use `Delay.t` or monadic `Resumption.t`.
- Partial result types propagate through callers, signatures, includes, and
  functor results.
- No translation relies on `Unset Guard Checking`,
  `#[bypass_check(guard)]`, or an unrestricted fixed point over arbitrary
  types.

Remaining work:

- Infer structural recursion before requiring configuration.
- Infer or check common ranking functions and emit named, independently
  provable decrease lemmas.
- Replace the current `convergent` strategy's admitted convergence obligation
  with an explicit proof parameter that propagates through callers.
- Add a coinductive productivity analysis and a sound `Unknown`
  classification.
- Emit machine-checkable termination or divergence certificates rather than
  trusting the analysis implementation.
