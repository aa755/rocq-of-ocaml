---
id: run
title: Run
---

`rocq-of-ocaml` translates the OCaml files one by one. It uses [Merlin](https://github.com/ocaml/merlin) to get the typing environment of each file. Thus you should first have a project which works with Merlin. This is generally the case for a project compiled with [dune](https://github.com/ocaml/dune).

## Minimal example
Create a file `example.ml`:
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
```sh
rocq-of-ocaml example.ml
```

You should get a file `Example.v` representing the corresponding version in Rocq:
```rocq
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import RocqOfOCaml.Settings.

Inductive tree (a : Set) : Set :=
| Leaf : a -> tree a
| Node : tree a -> tree a -> tree a.

Arguments Leaf {_}.
Arguments Node {_}.

Fixpoint sum (tree : tree Z) : Z :=
  match tree with
  | Leaf n => n
  | Node tree1 tree2 => Z.add (sum tree1) (sum tree2)
  end.

```

## Command line arguments
The general usage pattern is the following:
```sh
rocq-of-ocaml [options] file.ml
```

The options are:
* `-output file`: specify the name of the Rocq `.v` file to output (by default the capitalized OCaml file name with a `.v` extension)
* `-project-cmt-dir dir`: load cross-file module-shape hints from the project's compiled `.cmt` files
* `-assumption-metadata-dir dir`: load translated call requirements exported by previously translated dependency units
* `-assumption-metadata-output file`: write this unit's translated call requirements to a sidecar file
* `-assumption-prefix path`: add a source module path under which call requirements are exported; this option is repeatable to cover module aliases
* `-json-mode`: produce the list of error messages in JSON format; useful for post-processing

The assumption metadata options preserve generated `Unreachable` and
`Unimplemented` class requirements across OCaml compilation units. Translate
dependencies before their callers, write one sidecar per dependency into a
shared directory, and pass that directory while translating each caller.
