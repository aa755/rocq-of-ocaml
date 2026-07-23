(** A module-level renaming applies to every qualified descendant. *)
let positives =
  Stdlib.List.filter (fun value -> value > 0) [-1; 0; 2; 3]
