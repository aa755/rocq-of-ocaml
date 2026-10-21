(* PPX generators can use a variable named "_" instead of a wildcard node. *)
let mapper _ =
  let pat self pattern =
    let pattern = Ast_mapper.default_mapper.pat self pattern in
    match pattern.Parsetree.ppat_desc with
    | Parsetree.Ppat_any ->
        {pattern with ppat_desc = Parsetree.Ppat_var (Location.mknoloc "_")}
    | _ -> pattern
  in
  {Ast_mapper.default_mapper with pat}

let () = Ast_mapper.register "unused_generated_bindings" mapper
