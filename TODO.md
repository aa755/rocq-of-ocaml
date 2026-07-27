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
- Concrete result types receive only the type-specific admitted instances
  required by the generated program. There is no universal instance for
  either class.
- Polymorphic definitions expose the required class constraints, and those
  constraints propagate through calls, module projections, signatures, and
  synthesized functor-result records.
- The translator warns with the source location whenever it introduces either
  assumption.
- It is the user's responsibility to prove that every admitted
  `Unreachable` occurrence is unreachable, and that every `Unimplemented`
  occurrence is outside the executions covered by a correctness theorem.

## Coinductive types

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

## Termination

Remove blanket `Unset Guard Checking` and classify every recursive
definition before translating it.

The translator now accepts an explicit `[@rocq.wf]` strategy for a single
top-level recursive function. It emits an abstract measure and
`Program Fixpoint`, warns about the resulting trust boundary, and admits the
generated obligations. It also recognizes `[@rocq.partial]` but rejects it
until the partial computation effect can be propagated through callers and
signatures.

### Actually terminating

- Emit ordinary `Fixpoint` definitions for structurally recursive functions.
- Use a well-founded definition, such as `Program Fixpoint` or `Equations`,
  for recursion justified by a measure.
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
- Choose an explicit semantics for each such function: fuel, a delay or
  partiality monad, coinductive interaction trees, or a small-step relation.
- Warn whenever translation changes a possibly non-terminating function's
  interface or introduces a fuel/partiality boundary.
- Do not use an unrestricted fixed point or a false decreasing obligation to
  encode genuine divergence.
