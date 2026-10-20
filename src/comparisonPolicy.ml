(** Identify the compiler primitive rather than an operator's spelling. *)
let primitive_operation (primitive : Primitive.description) : string option =
  match primitive.prim_name with
  | "%equal" -> Some "equal"
  | "%notequal" -> Some "not_equal"
  | "%lessthan" -> Some "lt"
  | "%greaterthan" -> Some "gt"
  | "%lessequal" -> Some "le"
  | "%greaterequal" -> Some "ge"
  | "%compare" -> Some "compare"
  | "%eq" | "%noteq" -> Some "physical_equal"
  | _ -> None

(** Compatibility operations whose implementations depend on unmodeled
    comparison primitives. Check resolved paths, including re-exports. *)
let forbidden_runtime_path (path : string) : bool =
  List.exists
    (fun (prefix, names) ->
      List.exists (fun name -> String.equal path (prefix ^ "." ^ name)) names)
    [
      ( "RocqOfOCaml.Basics.Stdlib",
        [ "polymorphic_equal"; "polymorphic_not_equal"; "physical_equal";
          "polymorphic_compare"; "lt"; "le"; "gt"; "ge"; "min"; "max";
          "compare" ] );
      ( "RocqOfOCaml.OCamlList",
        [ "mem"; "memq"; "assoc"; "assoc_opt"; "assq"; "assq_opt";
          "mem_assoc"; "mem_assq"; "remove_assoc"; "remove_assq" ] );
      ("RocqOfOCaml.List", [ "merge" ]);
    ]
