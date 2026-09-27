#!/bin/sh
set -eu

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
build="$repo_root/_build/zarith-parser-diff"
switch=${ROCQ_OPAM_SWITCH:-}

opam_exec() {
  if [ -n "$switch" ]; then
    opam exec --switch="$switch" -- "$@"
  else
    opam exec -- "$@"
  fi
}

mkdir -p "$build"
cat >"$build/ParserExtraction.v" <<'EOF'
From Stdlib Require Import Extraction.
Require Import RocqOfOCaml.OCamlZ.

Extraction Language OCaml.
Extraction "model_parser.ml" OCamlZ.of_string_opt.
EOF

(
  cd "$repo_root/proofs"
  opam_exec ./configure.sh
  opam_exec make -j"${JOBS:-4}"
)
(
  cd "$build"
  opam_exec rocq c -R "$repo_root/proofs" RocqOfOCaml ParserExtraction.v
  cp "$repo_root/experiments/zarith-parser/diff.ml" ./zarith_parser_diff.ml
  opam_exec ocamlfind ocamlopt -package zarith -linkpkg \
    model_parser.mli model_parser.ml zarith_parser_diff.ml -o parser_diff
  ./parser_diff
)
