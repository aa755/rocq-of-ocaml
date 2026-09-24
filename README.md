# 🐓🐫 rocq-of-ocaml [![CI](https://github.com/formal-land/rocq-of-ocaml/actions/workflows/ci.yml/badge.svg?branch=master)](https://github.com/formal-land/rocq-of-ocaml/actions/workflows/ci.yml)
> Formal verification for OCaml programs

Translate OCaml programs to **similar-looking code in Rocq**, an extremely expressive formal language to express and formally verify **any kinds of properties** (preservation of invariants, absence of assert failures, backward compatibility, ...). We use `rocq-of-ocaml` to formally verify the "protocol" (core part) of the crypto-currency [Tezos](https://tezos.com/), composed of **100,000 lines of OCaml**. We cover most of the code: **80% of files** have at least one formally verified property in the project [coq-tezos-of-ocaml](https://gitlab.com/formal-land/coq-tezos-of-ocaml). This is formal verification at a **large scale**.

| Do not hesitate to schedule a quick meeting with us for more information by going on [https://koalendar.com/e/meet-with-formal-land](https://koalendar.com/e/meet-with-formal-land).<br /> We offer formal verification services and advice and are always there for a quick chat. |
| --- |

**📚 Documentation on https://formal.land/docs/tools/rocq-of-ocaml/introduction**

## 🎯 Aim
`rocq-of-ocaml` enables formal verification for [OCaml](https://ocaml.org/) programs&nbsp;🦄. *The more you prove, the happier you are.*

By transforming OCaml code into similar [Rocq](https://rocq-prover.org/) programs, we can prove arbitrarily complex properties using the existing power of Rocq. The sweet spot of `rocq-of-ocaml` is purely functional and monadic programs. Side-effects outside of a monad, like references, and advanced features like object-oriented programming, may never be supported. By sticking to the supported subset of OCaml, you can import millions of lines of code to Rocq and write proofs at large. By running `rocq-of-ocaml` after each code change, you make sure that your proofs are still valid. The generated Rocq code is designed to be stable, with no generated variable names. We recommend organizing your proof files as you would organize your tests, with one proof file per code file.

The guiding idea of `rocq-of-ocaml` is [TypeScript](https://www.typescriptlang.org/). Instead of bringing types to an untyped language, we bring proofs to a typed language. The approach is the same: finding the right sweet spot, using heuristics when needed, guiding the user with error messages. We use `rocq-of-ocaml` for the crypto-currency Tezos in the hope of having near-zero bugs thanks to formal proofs. Tezos is currently one of the most advanced crypto-currencies, with smart contracts, proof-of-stake, encrypted transactions, and protocol upgrades. It aims to compete with Ethereum. Formal verification is key for crypto-currencies as there are no central authorities to forbid bug exploits and stealing money.

There are still some open problems with `rocq-of-ocaml`, like the axiom-free compilation of [GADTs](https://blog.janestreet.com/why-gadts-matter-for-performance/) (an ongoing project). If you are willing to work on a particular project, you can contact us at [&#099;&#111;&#110;&#116;&#097;&#099;&#116;&#064;formal&#046;&#108;&#097;&#110;&#100;](mailto:&#099;&#111;&#110;&#116;&#097;&#099;&#116;&#064;formal&#046;&#108;&#097;&#110;&#100;).

<p align="center">
  <img alt="happiness and proofs" width="347" height="auto" src="https://raw.githubusercontent.com/formal-land/rocq-of-ocaml/master/doc/proofs_happiness.png" />
</p>

## Example
Start with the file `main.ml`&nbsp;🐫:
```ocaml
type 'a tree =
  | Leaf of 'a
  | Node of 'a tree * 'a tree

let rec sum tree =
  match tree with
  | Leaf n -> n
  | Node (tree1, tree2) -> sum tree1 + sum tree2
```
Run:
```
rocq-of-ocaml main.ml
```
Get a file `Main.v`&nbsp;🦄:
```rocq
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import RocqOfOCaml.Settings.

Inductive tree (a : Set) : Set :=
| Leaf : a -> tree a
| Node : tree a -> tree a -> tree a.

Arguments Leaf {_}.
Arguments Node {_}.

Fixpoint sum (tree : tree int) : int :=
  match tree with
  | Leaf n => n
  | Node tree1 tree2 => Z.add (sum tree1) (sum tree2)
  end.
```
You can now write proofs by induction over the `sum` function using Rocq. To see how you can write proofs, you can simply look at the [Rocq documentation](https://rocq-prover.org/doc/v9.0/refman/). Learning to write proofs is like learning a new programming paradigm. It can take time, but it can be worthwhile! Here is an example of proof:
```rocq
(** Definition of a tree with only positive integers *)
Inductive positive : tree int -> Prop :=
| Positive_leaf : forall n, n > 0 -> positive (Leaf n)
| Positive_node : forall tree1 tree2,
  positive tree1 -> positive tree2 -> positive (Node tree1 tree2).

From Stdlib Require Import micromega.Lia.

Lemma positive_plus n m : n > 0 -> m > 0 -> n + m > 0.
  lia.
Qed.

(** Proof that if a tree is positive, then its sum is positive too *)
Fixpoint positive_sum (tree : tree int) (H : positive tree)
  : sum tree > 0.
  destruct tree; simpl; inversion H; trivial.
  apply positive_plus; now apply positive_sum.
Qed.
```

## Install
Using the OCaml package manager [opam](https://opam.ocaml.org/), run:
```
opam install rocq-of-ocaml
```

## Usage
The basic command is:
```
rocq-of-ocaml file.ml
```
You can start to experiment with the test files in `tests/` or look at our [online examples](https://foobar-land.github.io/rocq-of-ocaml/examples/). `rocq-of-ocaml` compiles the `.ml` or `.mli` files using [Merlin](https://github.com/ocaml/merlin) to understand the dependencies of a project. One first needs to have a **compiled project** with a working configuration of Merlin. This is automatically the case if you use [dune](https://dune.build/) as a build system.

Recursive definitions are emitted as ordinary Rocq `Fixpoint`s by default, so
Rocq's guard checker accepts structural recursion and rejects other recursion.
Use `[@rocq.wf]` for recursion justified by a well-founded measure, or
`[@rocq.partial]` when evaluation may diverge. A translation configuration can
supply the same classifications without changing the OCaml source:

```json
{
  "recursion_strategies": [
    ["path/to/source.ml", "Outer.Module.total_function", "well_founded"],
    ["path/to/source.ml", "Outer.Module.partial_function", "partial"]
  ]
}
```

The source path is matched as a path suffix. The definition name is its
dot-separated lexical path through enclosing modules and functions, which
also disambiguates repeated local names such as `loop`. Well-founded
definitions expose an abstract measure and explicit decrease obligations.
Partial definitions return `Delay.t` or monadic `Resumption.t`, and the changed
result type is propagated through strict callers and module interfaces.
The optional `termination_certificates` configuration supplies a concrete
Rocq measure and a named call-site tactic for a `well_founded` definition;
successfully checked certificates remove both the abstract measure and
`Admit Obligations` from the generated definition.

To map a partial computation between monads through a local action lift,
declare that operation explicitly:

```json
{
  "partial_monad_lifts": [
    ["path/to/source.ml", "Outer.Module.lift"]
  ]
}
```

The operation must have one polymorphic value type and a named action type
on each side, such as `'a Host.t -> 'a Machine.t`. A call whose argument is
partial becomes `Resumption.hoist` with the original polymorphic operation;
calls with total arguments retain their source form. The configuration uses
the declaration's exact lexical path and source file, rather than its final
name alone. This currently applies to declarations in the translated unit.
It is a semantic declaration: the lift must preserve return and bind under
the intended observation relation. `Resumption.run_hoist` states those proof
requirements explicitly; the translator does not prove them from a type.

Explicit state application of a local partial result-and-state action can
be configured separately:

```json
{
  "partial_state_observers": [
    ["path/to/source.ml", "Outer.Module.step", 1, "result_state"]
  ]
}
```

The arity counts ordinary arguments before the state: here `step input state`
becomes `ResultState.observe (step input) state`. The action must already be
configured as partial, with a named result type such as `'a M.t`, representing
`state -> ('a, error) result * state`. This declaration requires the canonical
return and bind of `ResultState`, including retaining the updated state on
error; those semantics do not follow from the type alone. The observer returns
a `Delay.t` of the result/state pair. Monadic callers embed it with
`Resumption.of_delay`. Calls that do not supply the state remain resumptions.
Matching uses the exact local declaration and source file, as for action lifts.
All ordinary arguments and the state must be supplied at the observed call.
Use `"state"` instead of `"result_state"` for plain actions of type
`state -> 'a * state` with the canonical state-monad operations. This emits
`StateAction.observe`; its convergence and result/state preservation laws
reuse the result/state interpreter with an empty error type.
Configured partial values with recursion arity `0` retain their effect when
referenced without an application, including branches that select between
partial and total monadic actions.

A computation-valued parameter can use the same arity-zero declaration:

```json
{
  "recursion_strategies": [
    ["path/to/source.ml", "Outer.choose", "partial", 2],
    ["path/to/source.ml", "Outer.choose.otherwise", "partial", 0]
  ]
}
```

Here `choose flag ~otherwise` receives the `otherwise` action as a resumption.
The parameter must have a named action type. Its declaration, references,
and synthesized result interface retain that partial type. Calls to the
local function lower the supplied argument in the parameter's source monad,
including ordinary total actions and compound partial expressions. Both
labeled and positional parameters are matched by their source binding names.

Pure sequencing whose continuation contains a recursive call uses the
`RocqOfOCaml.Partial.Delay.bind_guarded` notation. It expands to a local
`cofix` so Rocq can check the recursive call's guard. `DelayGuarded` proves
convergence in both directions and returned-value preservation, requiring
convergence only of the continuation selected by the first computation.

## Documentation
You can read the documentation on the website of the project at [https://formal.land/docs/tools/rocq-of-ocaml/introduction](https://formal.land/docs/tools/rocq-of-ocaml/introduction).

## Supported
* the core of OCaml (functions, let bindings, pattern-matching,...) ✔️
* type definitions (records, inductive types, synonyms, mutual types) ✔️
* monadic programs ✔️
* modules as namespaces ✔️
* modules as polymorphic records (signatures, functors, first-class modules) ✔️
* multiple-file projects (thanks to Merlin) ✔️
* `.ml` and `.mli` files ✔️
* existential types (we use impredicative sets to avoid a universe explosion) ✔️
* partial support of GADTs 🌊
* partial support of polymorphic variants 🌊
* partial support of extensible types 🌊
* ignores side-effects outside of a monad ❌
* no object-oriented programming ❌

Even in case of errors, we try to generate some Rocq code along with an error message. The generated Rocq code should be readable and with a size similar to the OCaml source. The generated code does not necessarily compile after a first try. This can be due to various errors, such as name collisions. Do not hesitate to fix these errors by updating the OCaml source accordingly. If you want more assistance, please contact us by opening an issue in this repository.

## Contribute
If you want to contribute to the project, you can submit a pull-requests.

### Build with opam
To install the current development version:
```
opam pin add https://github.com/formal-land/rocq-of-ocaml.git#master
```

### Build manually
Read the `rocq-of-ocaml.opam` file at the root of the project to know the dependencies to install and get the list of commands to build the project.

## License
MIT (open-source software)
