(** Cross-compilation-unit hints recovered from project CMT files.

    OCaml's exported signature for [module M = F (X)] preserves the expanded
    result but not the original application.  Rocq-of-ocaml represents that
    result with the synthesized signature [F.F_result], so translating another
    compilation unit needs the application recorded in the implementation
    CMT.  This index is optional and has no effect on standalone translation. *)

type t = {
  module_results : (Path.t * Path.t) list;
  module_applications : (Path.t * Path.t) list;
  module_aliases : (Path.t * Path.t) list;
  functor_results : (Path.t * Path.t) list;
  anonymous_functor_parameters : (Path.t * string * Path.t) list;
  functor_parameter_types :
    (Path.t * FunctorParameterHint.t list) list;
  result_module_fields : (Path.t * string * Path.t) list;
  module_types : (Path.t * Types.module_type) list;
}

let empty =
  {
    module_results = [];
    module_applications = [];
    module_aliases = [];
    functor_results = [];
    anonymous_functor_parameters = [];
    functor_parameter_types = [];
    result_module_fields = [];
    module_types = [];
  }

let merge left right =
  {
    module_results = left.module_results @ right.module_results;
    module_applications =
      left.module_applications @ right.module_applications;
    module_aliases = left.module_aliases @ right.module_aliases;
    functor_results = left.functor_results @ right.functor_results;
    anonymous_functor_parameters =
      left.anonymous_functor_parameters
      @ right.anonymous_functor_parameters;
    functor_parameter_types =
      left.functor_parameter_types @ right.functor_parameter_types;
    result_module_fields =
      left.result_module_fields @ right.result_module_fields;
    module_types = left.module_types @ right.module_types;
  }

let project_paths_equal left right =
  Path.same left right
  ||
  let has_global_head path =
    match Path.head path with
    | head -> Ident.global head
    | exception _ -> false
  in
  has_global_head left
  && has_global_head right
  && String.equal
       (Str.global_replace (Str.regexp_string "__") "." (Path.name left))
       (Str.global_replace (Str.regexp_string "__") "." (Path.name right))

let find_path path entries =
  entries
  |> List.find_map (fun (candidate, value) ->
         if project_paths_equal candidate path then Some value else None)

let find_result_module_field_raw result_signature field_name hints =
  hints.result_module_fields
  |> List.find_map
       (fun (candidate_result, candidate_field, field_signature) ->
         if
           project_paths_equal candidate_result result_signature
           && String.equal candidate_field field_name
         then Some field_signature
         else None)

let find_module_result path hints =
  let rec find visited path =
    if List.exists (project_paths_equal path) visited then None
    else
      match find_path path hints.module_results with
      | Some _ as result -> result
      | None -> (
          match find_path path hints.module_applications with
          | Some functor_path ->
              find_path functor_path hints.functor_results
          | None -> (
              match find_path path hints.module_aliases with
              | Some target -> find (path :: visited) target
              | None -> (
                  match path with
                  | Path.Pdot (parent, field) ->
                      Option.bind
                        (find (path :: visited) parent)
                        (fun parent_result ->
                          Option.map
                            (fun field_signature ->
                              Option.value
                                (find (path :: visited) field_signature)
                                ~default:field_signature)
                            (find_result_module_field_raw parent_result field
                               hints))
                  | Path.Pextra_ty (parent, _) ->
                      find (path :: visited) parent
                  | Path.Pident _ | Path.Papply _ -> None)))
  in
  find [] path

let find_result_module_field result_signature field_name hints =
  find_result_module_field_raw result_signature field_name hints
  |> Option.map (fun field_signature ->
         Option.value
           (find_module_result field_signature hints)
           ~default:field_signature)

let has_module_result_reference path hints =
  let rec find visited path =
    if List.exists (project_paths_equal path) visited then false
    else
      Option.is_some (find_path path hints.module_results)
      || Option.is_some (find_path path hints.module_applications)
      ||
      match find_path path hints.module_aliases with
      | Some target -> find (path :: visited) target
      | None -> false
  in
  find [] path

let find_functor_result path hints =
  find_path path hints.functor_results

let find_anonymous_functor_parameter functor_path parameter_name hints =
  hints.anonymous_functor_parameters
  |> List.find_map
       (fun (candidate, candidate_parameter, signature) ->
         if
           project_paths_equal candidate functor_path
           && String.equal candidate_parameter parameter_name
         then Some signature
         else None)

let find_functor_parameter_types functor_path hints =
  find_path functor_path hints.functor_parameter_types

let find_module_type path hints =
  find_path path hints.module_types

let module_types hints = hints.module_types

let rec final_functor_body (module_expr : Typedtree.module_expr) =
  match module_expr.mod_desc with
  | Tmod_functor (_, body) -> (
      match final_functor_body body with
      | Some _ as result -> result
      | None -> Some body)
  | Tmod_constraint (inner, _, _, _) -> final_functor_body inner
  | _ -> None

let rec root_functor_path (module_expr : Typedtree.module_expr) =
  match module_expr.mod_desc with
  | Tmod_ident (path, _) -> Some path
  | Tmod_apply (functor_expr, _, _)
  | Tmod_apply_unit functor_expr
  | Tmod_constraint (functor_expr, _, _, _) ->
      root_functor_path functor_expr
  | Tmod_structure _
  | Tmod_functor _
  | Tmod_unpack _
  | Tmod_typed_hole ->
      None

let applied_functor_path (module_expr : Typedtree.module_expr) =
  let rec find module_expr =
    match module_expr.Typedtree.mod_desc with
    | Tmod_apply (functor_expr, _, _)
    | Tmod_apply_unit functor_expr ->
        root_functor_path functor_expr
    | Tmod_constraint (inner, _, _, _) -> find inner
    | _ -> None
  in
  find module_expr

let module_expr_structure (module_expr : Typedtree.module_expr) =
  let rec find module_expr =
    match module_expr.Typedtree.mod_desc with
    | Tmod_structure structure -> Some structure
    | Tmod_constraint (inner, _, _, _) -> find inner
    | _ -> None
  in
  find module_expr

let module_expr_alias (module_expr : Typedtree.module_expr) =
  let rec find module_expr =
    match module_expr.Typedtree.mod_desc with
    | Tmod_ident (path, _) -> Some path
    | Tmod_constraint (inner, _, _, _) -> find inner
    | _ -> None
  in
  find module_expr

let qualify_path locals path =
  let rec qualify = function
    | Path.Pident ident as path ->
        if Ident.global ident || Ident.is_predef ident then path
        else
          locals
          |> List.find_map (fun (candidate, target) ->
                 if Ident.same candidate ident then Some target else None)
          |> Option.value ~default:path
    | Path.Pdot (prefix, field) ->
        Path.Pdot (qualify prefix, field)
    | Path.Papply (functor_path, argument_path) ->
        Path.Papply (qualify functor_path, qualify argument_path)
    | Path.Pextra_ty (prefix, extra) ->
        Path.Pextra_ty (qualify prefix, extra)
  in
  qualify path

let module_type_shape (env : Env.t) (module_typ : Types.module_type) :
    SignatureShape.t option =
  match module_typ with
  | Mty_signature signature ->
      Some (SignatureShape.of_signature None signature)
  | _ -> (
      match Env.scrape_alias env module_typ with
      | Mty_signature signature ->
          Some (SignatureShape.of_signature None signature)
      | _ -> None
      | exception _ -> None)

let module_type_has_same_shape (env : Env.t) (expected : Types.module_type)
    (candidate : Types.module_type) : bool =
  match (module_type_shape env expected, module_type_shape env candidate) with
  | Some expected, Some candidate ->
      SignatureShape.are_equal expected candidate
  | _ -> false

let nested_module_types (env : Env.t)
    (declaration : Types.module_declaration) :
    (Path.t * Types.module_type) list =
  let rec collect prefix module_typ =
    match Env.scrape_alias env module_typ with
    | Mty_signature signature ->
        signature
        |> List.concat_map (function
             | Types.Sig_modtype
                 (ident, { Types.mtd_type = Some module_typ; _ }, _) ->
                 [ (Path.Pdot (prefix, Ident.name ident), module_typ) ]
             | Types.Sig_module
                 (ident, _, nested_declaration, _, _) ->
                 collect
                   (Path.Pdot (prefix, Ident.name ident))
                   nested_declaration.md_type
             | _ -> [])
    | _ -> []
    | exception _ -> []
  in
  match declaration.md_type with
  | module_typ -> collect (Path.Pident (Ident.create_local "_")) module_typ

let replace_dummy_prefix (root : Path.t) (path : Path.t) : Path.t =
  let rec replace = function
    | Path.Pident _ -> root
    | Path.Pdot (prefix, field) -> Path.Pdot (replace prefix, field)
    | Path.Papply (functor_path, argument_path) ->
        Path.Papply (replace functor_path, replace argument_path)
    | Path.Pextra_ty (prefix, extra) ->
        Path.Pextra_ty (replace prefix, extra)
  in
  replace path

let visible_module_types (env : Env.t) :
    (Path.t * Types.module_type) list =
  let direct =
    Env.fold_modtypes
      (fun _ path declaration candidates ->
        match declaration.Types.mtd_type with
        | Some module_typ -> (path, module_typ) :: candidates
        | None -> candidates)
      None env []
  in
  match direct with
  | _ :: _ -> direct
  | [] ->
      Env.fold_modules
        (fun _ path declaration candidates ->
          nested_module_types env declaration
          |> List.map (fun (nested_path, module_typ) ->
                 (replace_dummy_prefix path nested_path, module_typ))
          |> List.rev_append candidates)
        None env []

let latest_path (paths : Path.t list) : Path.t option =
  paths
  |> List.sort (fun left right ->
         match Int.compare (Path.scope right) (Path.scope left) with
         | 0 -> Path.compare left right
         | ordering -> ordering)
  |> List.find_opt (fun _ -> true)

(** Recover the same named result interface selected when the defining
    compilation unit is translated directly.  A functor implementation may
    strengthen abstract types, so textual equality is tried first and OCaml
    module-type inclusion second.  Merely matching field names is used only
    to bound the candidate set; it is never sufficient by itself. *)
let find_named_result_signature
    (declared_module_types :
      (Path.t * Path.t * Types.module_type) list)
    (body : Typedtree.module_expr) : Path.t option =
  match SignatureHints.module_expr_annotation body with
  | Some path -> Some path
  | None ->
      let implementation = body.mod_type in
      let env = body.mod_env in
      let declared_module_types =
        declared_module_types
        |> List.map (fun (canonical_path, local_path, fallback) ->
               let module_typ =
                 match (Env.find_modtype local_path env).mtd_type with
                 | Some module_typ -> module_typ
                 | None -> fallback
                 | exception Not_found -> fallback
               in
               (canonical_path, module_typ))
      in
      let candidates =
        visible_module_types env @ declared_module_types
        |> List.filter (fun (_, candidate) ->
               module_type_has_same_shape env implementation candidate)
      in
      candidates |> List.map fst |> latest_path

let of_structure (unit_name : string) (structure : Typedtree.structure) : t =
  let unit_path =
    Path.Pident (Ident.create_persistent unit_name)
  in
  let hints = ref empty in
  let locals = ref [] in
  let declared_module_types = ref [] in
  let canonical_anonymous_signatures = ref [] in
  let module_types_equivalent (module_type : Typedtree.module_type)
      candidate =
    try
      Includemod.check_modtype_equiv ~loc:module_type.mty_loc
        module_type.mty_env (Ident.create_local "_anonymous_signature")
        candidate module_type.mty_type;
      true
    with _ -> false
  in
  let add_anonymous_functor_parameters owner canonical module_name module_expr =
    let rec collect module_expr =
      match module_expr.Typedtree.mod_desc with
      | Tmod_functor (Named (parameter, _, module_type), body) ->
          (match module_type.mty_desc with
          | Tmty_signature _ ->
              let parameter_name =
                Name.string_of_optional_ident parameter
              in
              let derived_signature =
                Path.Pdot
                  ( owner,
                    module_name ^ "_" ^ parameter_name ^ "_signature" )
              in
              let canonical_signature =
                !canonical_anonymous_signatures
                |> List.find_map
                     (fun (candidate_type, candidate_path) ->
                       if module_types_equivalent module_type candidate_type then
                         Some candidate_path
                       else None)
              in
              let signature, is_new =
                match canonical_signature with
                | Some signature -> (signature, false)
                | None ->
                    canonical_anonymous_signatures :=
                      (module_type.mty_type, derived_signature)
                      :: !canonical_anonymous_signatures;
                    (derived_signature, true)
              in
              hints :=
                {
                  !hints with
                  anonymous_functor_parameters =
                    (canonical, parameter_name, signature)
                    :: !hints.anonymous_functor_parameters;
                  module_types =
                    if is_new then
                      (signature, module_type.mty_type)
                      :: !hints.module_types
                    else !hints.module_types;
                }
          | _ -> ());
          collect body
      | Tmod_functor (Unit, body)
      | Tmod_constraint (body, _, _, _) ->
          collect body
      | Tmod_ident _ | Tmod_apply _ | Tmod_apply_unit _
      | Tmod_structure _ | Tmod_unpack _ | Tmod_typed_hole ->
          ()
    in
    collect module_expr
  in
  let add_functor canonical binding =
    (match SignatureHints.functor_parameter_types binding.Typedtree.mb_expr with
    | [] -> ()
    | parameter_types ->
        let parameter_types =
          parameter_types
          |> List.map (fun parameter ->
                 {
                   parameter with
                   FunctorParameterHint.path_aliases = !locals;
                 })
        in
        hints :=
          {
            !hints with
            functor_parameter_types =
              (canonical, parameter_types)
              :: !hints.functor_parameter_types;
          });
    match final_functor_body binding.Typedtree.mb_expr with
    | Some body ->
        let result =
          match
            find_named_result_signature !declared_module_types body
          with
          | Some path -> qualify_path !locals path
          | None ->
              let suffix =
                match
                  SignatureHints.module_expr_anonymous_annotation body
                with
                | Some _ -> "_signature"
                | None -> "_result"
              in
              Path.Pdot
                (canonical, Path.last canonical ^ suffix)
        in
        hints :=
          {
            !hints with
            functor_results =
              (canonical, result) :: !hints.functor_results;
            module_types =
              (result, body.mod_type) :: !hints.module_types;
          };
        let rec relative_fields root path =
          if project_paths_equal root path then Some []
          else
            match path with
            | Path.Pdot (parent, field) ->
                Option.map
                  (fun fields -> fields @ [ field ])
                  (relative_fields root parent)
            | Path.Pextra_ty (parent, _) ->
                relative_fields root parent
            | Path.Pident _ | Path.Papply _ -> None
        in
        let local_module_results = ref [] in
        let find_qualified_local_result alias =
          match relative_fields canonical alias with
          | Some (_ :: _ as fields) ->
              List.fold_left
                (fun signature field ->
                  Option.bind signature (fun signature ->
                      find_result_module_field signature field !hints))
                (Some result) fields
          | Some [] | None -> None
        in
        let rec find_local_result alias =
          match alias with
          | Path.Pident ident ->
              !local_module_results
              |> List.find_map (fun (candidate, signature) ->
                     if Ident.same candidate ident then Some signature
                     else None)
          | Path.Pdot (parent, field) ->
              Option.bind (find_local_result parent) (fun signature ->
                  find_result_module_field signature field !hints)
          | Path.Pextra_ty (parent, _) ->
              find_local_result parent
          | Path.Papply _ -> find_qualified_local_result alias
        in
        let resolve_alias_result alias =
          match find_module_result alias !hints with
          | Some _ as result -> result
          | None -> (
              match find_local_result alias with
              | Some _ as result -> result
              | None -> find_qualified_local_result alias)
        in
        (match module_expr_structure body with
        | Some structure ->
            structure.str_items
            |> List.iter (fun (item : Typedtree.structure_item) ->
                   match item.str_desc with
                   | Tstr_module
                       {
                         mb_id = Some field_ident;
                         mb_expr;
                         _;
                       } ->
                       let field_name = Ident.name field_ident in
                       let field_path =
                         Path.Pdot (canonical, field_name)
                       in
                       let signature_and_type =
                         match
                           SignatureHints.module_expr_anonymous_annotation
                             mb_expr
                         with
                         | Some module_type ->
                             Some
                               ( Path.Pdot
                                   ( field_path,
                                     field_name ^ "_signature" ),
                                 Some module_type.mty_type )
                         | None -> (
                             match applied_functor_path mb_expr with
                             | Some source_functor ->
                                 let source_functor =
                                   qualify_path !locals source_functor
                                 in
                                 Option.map
                                   (fun signature -> (signature, None))
                                   (find_functor_result source_functor !hints)
                             | None ->
                                 (match module_expr_alias mb_expr with
                                 | Some alias ->
                                     let alias =
                                       qualify_path !locals alias
                                     in
                                     let alias_result =
                                       resolve_alias_result alias
                                     in
                                     (match alias_result with
                                     | Some signature ->
                                         Some (signature, None)
                                     | None
                                       when
                                         has_module_result_reference alias
                                           !hints ->
                                         Some (alias, None)
                                     | None -> None)
                                 | None ->
                                     Option.map
                                       (fun signature ->
                                         ( qualify_path !locals signature,
                                           None ))
                                       (SignatureHints
                                        .module_expr_annotation mb_expr)))
                       in
                       (match signature_and_type with
                       | Some (signature_path, module_type) ->
                           local_module_results :=
                             (field_ident, signature_path)
                             :: !local_module_results;
                           hints :=
                             {
                               !hints with
                               result_module_fields =
                                 (result, field_name, signature_path)
                                 :: !hints.result_module_fields;
                               module_types =
                                 (match module_type with
                                 | Some module_type ->
                                     (signature_path, module_type)
                                     :: !hints.module_types
                                 | None -> !hints.module_types);
                             }
                       | None -> ())
                   | _ -> ())
        | None -> ());
        (match body.mod_type with
        | Mty_signature signature ->
            signature
            |> List.iter (function
                 | Types.Sig_module
                     (field_ident, _, { Types.md_type = Mty_alias alias; _ },
                       _, _) ->
                     let field_name = Ident.name field_ident in
                     if
                       Option.is_none
                         (find_result_module_field result field_name !hints)
                     then
                       let alias = qualify_path !locals alias in
                       let alias_result = resolve_alias_result alias in
                       (match alias_result with
                       | Some field_signature ->
                           hints :=
                             {
                               !hints with
                               result_module_fields =
                                 (result, field_name, field_signature)
                                 :: !hints.result_module_fields;
                             }
                       | None
                         when
                           has_module_result_reference alias !hints ->
                           hints :=
                             {
                               !hints with
                               result_module_fields =
                                 (result, field_name, alias)
                                 :: !hints.result_module_fields;
                             }
                       | None -> ())
                 | _ -> ())
        | Mty_ident _
        | Mty_alias _
        | Mty_functor _
        | Mty_for_hole ->
            ())
    | None -> ()
  in
  let rec collect_structure owner (structure : Typedtree.structure) =
    List.iter
      (fun (item : Typedtree.structure_item) ->
        match item.str_desc with
        | Tstr_module binding -> collect_binding owner binding
        | Tstr_recmodule bindings ->
            List.iter (collect_binding owner) bindings
        | Tstr_modtype declaration -> (
            match declaration.mtd_type with
            | Some module_typ ->
                let path =
                  Path.Pdot (owner, Ident.name declaration.mtd_id)
                in
                declared_module_types :=
                  ( path,
                    Path.Pident declaration.mtd_id,
                    module_typ.mty_type )
                  :: !declared_module_types;
                hints :=
                  {
                    !hints with
                    module_types =
                      (path, module_typ.mty_type) :: !hints.module_types;
                  }
            | None -> ())
        | _ -> ())
      structure.str_items
  and collect_binding owner (binding : Typedtree.module_binding) =
    match binding.Typedtree.mb_id with
    | None -> ()
    | Some ident ->
        let canonical =
          Path.Pdot (owner, Ident.name ident)
        in
        locals := (ident, canonical) :: !locals;
        add_anonymous_functor_parameters owner canonical
          (Ident.name ident) binding.mb_expr;
        (match
           SignatureHints.module_expr_anonymous_annotation
             binding.mb_expr
         with
        | Some module_type ->
            let signature_path =
              Path.Pdot
                ( canonical,
                  Ident.name ident ^ "_signature" )
            in
            hints :=
              {
                !hints with
                module_types =
                  (signature_path, module_type.mty_type)
                  :: !hints.module_types;
              }
        | None -> ());
        add_functor canonical binding;
        (match applied_functor_path binding.mb_expr with
        | Some source_functor ->
            let source_functor =
              qualify_path !locals source_functor
            in
            hints :=
              {
                !hints with
                module_applications =
                  (canonical, source_functor)
                  :: !hints.module_applications;
              }
        | None -> (
            match module_expr_alias binding.mb_expr with
            | Some alias ->
                let alias = qualify_path !locals alias in
                hints :=
                  {
                    !hints with
                    module_aliases =
                      (canonical, alias) :: !hints.module_aliases;
                  }
            | None -> ()));
        (match module_expr_structure binding.mb_expr with
        | Some nested -> collect_structure canonical nested
        | None -> (
            match final_functor_body binding.mb_expr with
            | Some body -> (
                match module_expr_structure body with
                | Some nested ->
                    collect_structure canonical nested
                | None -> ())
            | None -> ()))
  in
  collect_structure unit_path structure;
  !hints

let cmt_file_hints file =
  try
    let cmt = Cmt_format.read_cmt file in
    match cmt.cmt_annots with
    | Cmt_format.Implementation structure ->
        of_structure cmt.cmt_modname structure
    | Cmt_format.Interface _
    | Cmt_format.Packed _
    | Cmt_format.Partial_implementation _
    | Cmt_format.Partial_interface _ ->
        empty
  with _ -> empty

let rec cmt_files directory =
  Sys.readdir directory |> Array.to_list
  |> List.concat_map (fun name ->
         let path = Filename.concat directory name in
         if Sys.is_directory path then cmt_files path
         else if String.ends_with ~suffix:".cmt" name then [ path ]
         else [])

let of_directory directory =
  cmt_files directory
  |> List.sort String.compare
  |> List.fold_left
       (fun hints file -> merge hints (cmt_file_hints file))
       empty
