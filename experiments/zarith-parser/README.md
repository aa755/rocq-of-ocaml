# Zarith literal model

`proofs/OCamlZ.v` models native `Z.of_string` for decimal, hexadecimal,
octal, and binary literals. It accepts either sign, Zarith's `-+` prefix,
and underscores after a digit. Empty and sign-only strings evaluate to zero,
as do empty base-prefixed strings. Invalid digits and leading underscores
remain invalid.

Run `ROCQ_OPAM_SWITCH=/path/to/switch experiments/zarith-parser/check.sh`
from this translator checkout. The script compiles the proof library, extracts
the executable `OCamlZ.of_string_opt` model, and compares it with native
Zarith on 54,144 deterministic inputs: every string through length three over
the chosen digit/prefix/sign/separator alphabet, 10,000 seeded strings through
length 24, and selected long cryptographic and malformed literals. The result
on OCaml 5.4.0 and Rocq 9.0.0 is zero mismatches. The translator's separate
420/5/5 regression matrix also passes. This is bounded differential evidence,
not a proof for every OCaml string or of all generated client constants.
