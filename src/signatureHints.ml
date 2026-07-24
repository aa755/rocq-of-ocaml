(** Exact named module-type annotations recovered from the typed tree.

    OCaml strengthens a constrained module after type checking.  For example,
    later occurrences of [module M : S = ...] carry a concrete signature
    mentioning [M.t], not the original path [S].  Shape-based reconstruction
    cannot recover [S] when that concrete module happens to implement several
    interfaces.  This prepass retains the source annotation keyed by the
    compiler identifier used at later occurrences. *)

type t = {
  module_annotations : (Path.t * Path.t) list;
  module_types : (Path.t * Types.module_type * Location.t) list;
  anonymous_signatures :
    (Path.t * Types.module_type * Location.t) list;
  anonymous_functor_parameters : (Path.t * string * Path.t) list;
  functor_parameter_types :
    (Path.t * FunctorParameterHint.t list) list;
  functor_result_signatures : (Path.t * Path.t) list;
  result_module_fields : (Path.t * string * Path.t) list;
  result_namespace_includes : (Path.t * string * string) list;
  applied_functor_children :
    (Path.t * Path.t * Path.t) list;
}

let empty : t =
  {
    module_annotations = [];
    module_types = [];
    anonymous_signatures = [];
    anonymous_functor_parameters = [];
    functor_parameter_types = [];
    functor_result_signatures = [];
    result_module_fields = [];
    result_namespace_includes = [];
    applied_functor_children = [];
  }

let find (module_path : Path.t) (hints : t) : Path.t option =
  let exact_candidates =
    hints.module_annotations
    |> List.filter_map (fun (candidate, signature_path) ->
           if Path.same module_path candidate then Some signature_path else None)
  in
  let is_anonymous signature_path =
    hints.anonymous_signatures
    |> List.exists (fun (candidate, _, _) ->
           Path.same signature_path candidate)
  in
  match List.find_opt (fun path -> not (is_anonymous path)) exact_candidates with
  | Some _ as named -> named
  | None -> List.find_opt (fun _ -> true) exact_candidates

let add (module_path : Path.t) (signature_path : Path.t) (hints : t) : t =
  {
    hints with
    module_annotations =
      (module_path, signature_path) :: hints.module_annotations;
  }

let location_contains (outer : Location.t) (inner : Location.t) : bool =
  String.equal outer.loc_start.pos_fname inner.loc_start.pos_fname
  && outer.loc_start.pos_cnum <= inner.loc_start.pos_cnum
  && inner.loc_end.pos_cnum <= outer.loc_end.pos_cnum

let path_base_name (path : Path.t) : string option =
  match Path.head path with
  | ident -> Some (Ident.name ident)
  | exception _ -> None

let find_module_type (module_type_path : Path.t) (location : Location.t)
    (hints : t) :
    Types.module_type option =
  match
    hints.module_types
    |> List.find_map (fun (candidate, module_type, _) ->
           if Path.same module_type_path candidate then Some module_type
           else None)
  with
  | Some _ as module_type -> module_type
  | None -> (
      match
        hints.anonymous_signatures
        |> List.find_map
             (fun (candidate, module_type, _) ->
               if Path.same module_type_path candidate then
                 Some module_type
               else
                 None)
      with
      | Some _ as module_type -> module_type
      | None ->
      match path_base_name module_type_path with
      | None -> None
      | Some name ->
          hints.module_types
          |> List.filter (fun (candidate, _, declaration_location) ->
                 path_base_name candidate = Some name
                 && location_contains location declaration_location)
          |> List.sort (fun
               (_, _, (left : Location.t))
               (_, _, (right : Location.t)) ->
                 Int.compare right.loc_start.pos_cnum left.loc_start.pos_cnum)
          |> List.find_map (fun (_, module_type, _) -> Some module_type))

let module_types (hints : t) : (Path.t * Types.module_type) list =
  hints.module_types
  |> List.map (fun (path, module_type, _) -> (path, module_type))

let anonymous_signatures (location : Location.t) (hints : t) :
    (Path.t * Types.module_type) list =
  hints.anonymous_signatures
  |> List.filter_map
       (fun (path, module_type, (declaration_location : Location.t)) ->
         if
           String.equal location.loc_start.pos_fname
             declaration_location.loc_start.pos_fname
           && declaration_location.loc_end.pos_cnum
              <= location.loc_start.pos_cnum
         then Some (path, module_type)
         else None)

let find_anonymous_functor_parameter (functor_path : Path.t)
    (parameter_name : string) (hints : t) : Path.t option =
  hints.anonymous_functor_parameters
  |> List.find_map (fun (candidate_functor, candidate_parameter, signature) ->
         if
           Path.same functor_path candidate_functor
           && String.equal parameter_name candidate_parameter
         then Some signature
         else None)

let find_functor_parameter_types (functor_path : Path.t) (hints : t) :
    FunctorParameterHint.t list option =
  hints.functor_parameter_types
  |> List.find_map (fun (candidate, parameter_types) ->
         if Path.same functor_path candidate then Some parameter_types
         else None)

let find_functor_result_signature (functor_path : Path.t) (hints : t) :
    Path.t option =
  hints.functor_result_signatures
  |> List.find_map (fun (candidate, signature) ->
         if Path.same functor_path candidate then Some signature else None)

let find_result_module_field (result_signature : Path.t)
    (field_name : string) (hints : t) : Path.t option =
  hints.result_module_fields
  |> List.find_map (fun (candidate_result, candidate_field, field_signature) ->
         if
           Path.same candidate_result result_signature
           && String.equal candidate_field field_name
         then Some field_signature
         else None)

let find_result_namespace_include (result_signature : Path.t)
    (namespace : string) (hints : t) : string option =
  hints.result_namespace_includes
  |> List.find_map
       (fun (candidate_result, candidate_namespace, included_field) ->
         if
           Path.same candidate_result result_signature
           && String.equal candidate_namespace namespace
         then Some included_field
         else None)

let find_applied_functor_child (path : Path.t) (hints : t) :
    (Path.t * Path.t) option =
  hints.applied_functor_children
  |> List.find_map (fun (candidate, target, parent_application) ->
         if Path.same path candidate then
           Some (target, parent_application)
         else None)

let rec module_type_path (module_typ : Typedtree.module_type) : Path.t option =
  match module_typ.mty_desc with
  | Tmty_ident (path, _) -> Some path
  | Tmty_with (module_typ, _) -> module_type_path module_typ
  | Tmty_alias _ | Tmty_functor _ | Tmty_signature _ | Tmty_typeof _ -> None

let rec module_expr_annotation (module_expr : Typedtree.module_expr) :
    Path.t option =
  match module_expr.mod_desc with
  | Tmod_constraint
      (inner, _, Tmodtype_explicit module_typ, _) -> (
      match module_type_path module_typ with
      | Some _ as path -> path
      | None -> module_expr_annotation inner)
  | _ -> None

let rec module_expr_anonymous_annotation
    (module_expr : Typedtree.module_expr) :
    Typedtree.module_type option =
  match module_expr.mod_desc with
  | Tmod_constraint
      (inner, _, Tmodtype_explicit module_typ, _) -> (
      match module_typ.mty_desc with
      | Tmty_signature _ -> Some module_typ
      | _ -> module_expr_anonymous_annotation inner)
  | _ -> None

let rec final_functor_body (module_expr : Typedtree.module_expr) :
    Typedtree.module_expr option =
  match module_expr.mod_desc with
  | Tmod_functor (_, body) -> (
      match final_functor_body body with
      | Some _ as result -> result
      | None -> Some body)
  | Tmod_constraint (inner, _, _, _) -> final_functor_body inner
  | _ -> None

let rec functor_parameter_types (module_expr : Typedtree.module_expr) :
    FunctorParameterHint.t list =
  match module_expr.mod_desc with
  | Tmod_functor (Named (ident, _, parameter_type), body) ->
      {
        ident;
        module_type = parameter_type;
        path_aliases = [];
      }
      :: functor_parameter_types body
  | Tmod_functor (Unit, body) -> functor_parameter_types body
  | Tmod_constraint (inner, _, _, _) -> functor_parameter_types inner
  | _ -> []

let rec module_expr_structure (module_expr : Typedtree.module_expr) :
    Typedtree.structure option =
  match module_expr.mod_desc with
  | Tmod_structure structure -> Some structure
  | Tmod_constraint (inner, _, _, _) -> module_expr_structure inner
  | _ -> None

let module_type_has_shape (env : Env.t) (shape : SignatureShape.t)
    (module_type : Types.module_type) : bool =
  match Env.scrape_alias env module_type with
  | Mty_signature signature ->
      SignatureShape.are_equal shape
        (SignatureShape.of_signature None signature)
  | _ -> false
  | exception _ -> false

let rec module_type_contains_signature_shape (env : Env.t)
    (shape : SignatureShape.t) (module_type : Types.module_type) : bool =
  match Env.scrape_alias env module_type with
  | Mty_signature signature ->
      signature
      |> List.exists (function
           | Types.Sig_modtype
               (_, { Types.mtd_type = Some module_type; _ }, _) ->
               module_type_has_shape env shape module_type
           | Types.Sig_module (_, _, { Types.md_type; _ }, _, _) ->
               module_type_contains_signature_shape env shape md_type
           | _ -> false)
  | _ -> false
  | exception _ -> false

(** This mirrors the decision relevant to [Structure.of_module]: an
    unannotated functor body gets a generated [F_result] signature only when
    its inferred result does not already identify a named module type. *)
let needs_synthetic_result_signature (body : Typedtree.module_expr) : bool =
  match module_expr_annotation body with
  | Some _ -> false
  | None -> (
      match Env.scrape_alias body.mod_env body.mod_type with
      | Mty_signature signature ->
          let shape = SignatureShape.of_signature None signature in
          not
            ((Env.fold_modtypes
                (fun _ _ declaration found ->
                  found
                  ||
                  match declaration.Types.mtd_type with
                  | Some module_type ->
                      module_type_has_shape body.mod_env shape module_type
                  | None -> false)
                None body.mod_env false)
            || Env.fold_modules
                 (fun _ _ declaration found ->
                   found
                   || module_type_contains_signature_shape body.mod_env shape
                        declaration.Types.md_type)
                 None body.mod_env false)
      | _ -> false
      | exception _ -> false)

let rec root_module_path (module_expr : Typedtree.module_expr) :
    Path.t option =
  match module_expr.mod_desc with
  | Tmod_ident (path, _) -> Some path
  | Tmod_apply (functor_expr, _, _)
  | Tmod_apply_unit functor_expr
  | Tmod_constraint (functor_expr, _, _, _) ->
      root_module_path functor_expr
  | Tmod_structure _
  | Tmod_functor _
  | Tmod_unpack _
  | Tmod_typed_hole ->
      None

let rec applied_functor_path (module_expr : Typedtree.module_expr) :
    Path.t option =
  match module_expr.mod_desc with
  | Tmod_apply (functor_expr, _, _)
  | Tmod_apply_unit functor_expr ->
      root_module_path functor_expr
  | Tmod_constraint (inner, _, _, _) -> applied_functor_path inner
  | _ -> None

let derived_functor_result_signature (functor_path : Path.t) : Path.t =
  Path.Pdot
    (functor_path, Path.last functor_path ^ "_result")

let module_type_fingerprint (env : Env.t) (module_type : Types.module_type) :
    string =
  Printtyp.wrap_printing_env ~error:true env (fun () ->
      Format.asprintf "%a" Printtyp.modtype module_type)

let rec aliased_module_path (module_expr : Typedtree.module_expr) :
    Path.t option =
  match module_expr.mod_desc with
  | Tmod_ident (path, _) -> Some path
  | Tmod_constraint (inner, _, _, _) -> aliased_module_path inner
  | _ -> None

let of_typedtree (typedtree : Merlin_kernel.Mtyper.typedtree) : t =
  let module_annotations = ref [] in
  let module_types = ref [] in
  let anonymous_signatures = ref [] in
  let anonymous_signature_fingerprints = ref [] in
  let anonymous_module_signatures = ref [] in
  let anonymous_functor_parameters = ref [] in
  let add (ident : Ident.t option) (signature_path : Path.t option) : unit =
    match (ident, signature_path) with
    | Some ident, Some signature_path ->
        module_annotations :=
          (Path.Pident ident, signature_path) :: !module_annotations
    | _ -> ()
  in
  let rec add_anonymous_functor_parameters (module_path : Path.t)
      (module_name : string)
      (module_expr : Typedtree.module_expr) : unit =
    match module_expr.mod_desc with
    | Tmod_functor (Named (ident, _, module_type), body) ->
        (match module_type.mty_desc with
        | Tmty_signature _ ->
            let parameter_name = Name.string_of_optional_ident ident in
            let signature_name =
              module_name ^ "_" ^ parameter_name ^ "_signature"
            in
            let signature_path =
              Path.Pident (Ident.create_local signature_name)
            in
            anonymous_signatures :=
              (signature_path, module_type.mty_type, module_type.mty_loc)
              :: !anonymous_signatures
            ;
            anonymous_signature_fingerprints :=
              ( signature_path,
                module_type_fingerprint module_type.mty_env
                  module_type.mty_type )
              :: !anonymous_signature_fingerprints
            ;
            anonymous_functor_parameters :=
              ( module_path,
                parameter_name,
                Option.map (fun ident -> Path.Pident ident) ident,
                signature_path )
              :: !anonymous_functor_parameters
        | _ -> ());
        add_anonymous_functor_parameters module_path module_name body
    | Tmod_constraint (inner, _, _, _) ->
        add_anonymous_functor_parameters module_path module_name inner
    | _ -> ()
  in
  let open Tast_iterator in
  let iterator =
    {
      default_iterator with
      module_binding =
        (fun self binding ->
          add binding.mb_id (module_expr_annotation binding.mb_expr);
          (match binding.mb_id with
          | Some ident ->
              (match module_expr_anonymous_annotation binding.mb_expr with
              | Some module_type ->
                  let module_path = Path.Pident ident in
                  let signature_name =
                    Ident.name ident ^ "_signature"
                  in
                  let signature_path =
                    Path.Pdot (module_path, signature_name)
                  in
                  module_annotations :=
                    (module_path, signature_path)
                    :: !module_annotations;
                  anonymous_signatures :=
                    ( signature_path,
                      module_type.mty_type,
                      module_type.mty_loc )
                    :: !anonymous_signatures;
                  anonymous_signature_fingerprints :=
                    ( signature_path,
                      module_type_fingerprint module_type.mty_env
                        module_type.mty_type )
                    :: !anonymous_signature_fingerprints;
                  module_types :=
                    ( signature_path,
                      module_type.mty_type,
                      module_type.mty_loc )
                    :: !module_types;
                  anonymous_module_signatures :=
                    signature_path :: !anonymous_module_signatures
              | None -> ());
              add_anonymous_functor_parameters
                (Path.Pident ident) (Ident.name ident) binding.mb_expr
          | None -> ());
          default_iterator.module_binding self binding);
      module_expr =
        (fun self module_expr ->
          (match module_expr.mod_desc with
          | Tmod_functor (Named (ident, _, module_typ), _) ->
              add ident (module_type_path module_typ)
          | _ -> ());
          default_iterator.module_expr self module_expr);
      expr =
        (fun self expression ->
          (match expression.exp_desc with
          | Texp_letmodule (ident, _, _, module_expr, _) ->
              add ident (module_expr_annotation module_expr)
          | _ -> ());
          default_iterator.expr self expression);
      module_type_declaration =
        (fun self declaration ->
          (match declaration.mtd_type with
          | Some module_type ->
              module_types :=
                ( Path.Pident declaration.mtd_id,
                  module_type.mty_type,
                  declaration.mtd_loc )
                :: !module_types
          | None -> ());
          default_iterator.module_type_declaration self declaration);
    }
  in
  (match typedtree with
  | `Implementation structure -> iterator.structure iterator structure
  | `Interface signature -> iterator.signature iterator signature);
  let find_declared_result_signature (body : Typedtree.module_expr) :
      Path.t option =
    match module_expr_annotation body with
    | Some _ as result -> result
    | None -> (
        match Env.scrape_alias body.mod_env body.mod_type with
        | Mty_signature signature ->
            let shape = SignatureShape.of_signature None signature in
            !module_types
            |> List.filter (fun
                 (path, module_typ, (location : Location.t)) ->
                   location.loc_start.pos_cnum
                   <= body.mod_loc.loc_start.pos_cnum
                   && not
                        (List.exists (Path.same path)
                           !anonymous_module_signatures)
                   && IsFirstClassModule.module_type_has_same_names_as_shape
                        body.mod_env module_typ shape
                   && IsFirstClassModule.module_type_includes
                        body.mod_env body.mod_type
                        (Env.scrape_alias body.mod_env module_typ))
            |> List.sort (fun
                 (_, _, (left : Location.t))
                 (_, _, (right : Location.t)) ->
                   Int.compare right.loc_start.pos_cnum
                     left.loc_start.pos_cnum)
            |> List.find_map (fun (path, _, _) -> Some path)
        | _ -> None
        | exception _ -> None)
  in
  let named_functor_results = ref [] in
  let synthetic_functor_results = ref [] in
  let functor_parameter_types_by_path = ref [] in
  let direct_functor_children = ref [] in
  let direct_applied_children = ref [] in
  let direct_signature_children = ref [] in
  let nested_namespace_includes = ref [] in
  let module_applied_children = ref [] in
  let module_aliases = ref [] in
  let collect_synthetic_results =
    {
      Tast_iterator.default_iterator with
      module_binding =
        (fun self binding ->
          (match (binding.mb_id, module_expr_structure binding.mb_expr) with
          | Some parent_ident, Some structure ->
              structure.str_items
              |> List.iter (fun (item : Typedtree.structure_item) ->
                     match item.str_desc with
                     | Tstr_module
                         {
                           mb_id = Some child_ident;
                           mb_expr;
                           _;
                         } -> (
                         match applied_functor_path mb_expr with
                         | Some child_functor ->
                             module_applied_children :=
                               ( Path.Pident parent_ident,
                                 Ident.name child_ident,
                                 child_functor )
                               :: !module_applied_children
                         | None -> ())
                     | _ -> ())
          | _ -> ());
          (match binding.mb_id with
          | Some ident -> (
              match functor_parameter_types binding.mb_expr with
              | [] -> ()
              | parameter_types ->
                  functor_parameter_types_by_path :=
                    (Path.Pident ident, parameter_types)
                    :: !functor_parameter_types_by_path)
          | None -> ());
          (match (binding.mb_id, final_functor_body binding.mb_expr) with
          | Some outer_ident, Some body -> (
              match module_expr_structure body with
              | None -> ()
              | Some structure ->
                  let direct_applied_modules =
                    structure.str_items
                    |> List.filter_map
                         (fun (item : Typedtree.structure_item) ->
                           match item.str_desc with
                           | Tstr_module
                               {
                                 mb_id = Some child_ident;
                                 mb_expr;
                                 _;
                               }
                             when
                               Option.is_some
                                 (applied_functor_path mb_expr) ->
                               Some (Ident.name child_ident)
                           | _ -> None)
                  in
                  let rec collect_namespace_includes prefix structure =
                    structure.str_items
                    |> List.iter
                         (fun (item : Typedtree.structure_item) ->
                           match item.str_desc with
                           | Tstr_include { incl_mod; _ } -> (
                               match aliased_module_path incl_mod with
                               | Some included_module
                                 when prefix <> []
                                      && List.mem
                                           (Path.last included_module)
                                           direct_applied_modules ->
                                   nested_namespace_includes :=
                                     ( Path.Pident outer_ident,
                                       String.concat "_" prefix,
                                       Path.last included_module )
                                     :: !nested_namespace_includes
                               | Some _ | None -> ())
                           | Tstr_module
                               {
                                 mb_id = Some child_ident;
                                 mb_expr;
                                 _;
                               } -> (
                               match module_expr_structure mb_expr with
                               | Some child_structure ->
                                   collect_namespace_includes
                                     (prefix
                                     @ [ Ident.name child_ident ])
                                     child_structure
                               | None -> ())
                           | _ -> ())
                  in
                  collect_namespace_includes [] structure;
                  structure.str_items
                  |> List.iter (fun (item : Typedtree.structure_item) ->
                         (match item.str_desc with
                         | Tstr_module
                             {
                               mb_id = Some child_ident;
                               mb_expr;
                               _;
                             }
                           when
                             (match
                                Env.scrape_alias mb_expr.mod_env
                                  mb_expr.mod_type
                              with
                             | Mty_functor _ -> true
                             | _ -> false
                             | exception _ -> false) ->
                             direct_functor_children :=
                               ( Path.Pident outer_ident,
                                 Ident.name child_ident,
                                 Path.Pident child_ident,
                                 Path.Pdot
                                   ( Path.Pident outer_ident,
                                     Ident.name child_ident ) )
                               :: !direct_functor_children
                         | _ -> ());
                         (match item.str_desc with
                         | Tstr_module
                             {
                               mb_id = Some child_ident;
                               mb_expr;
                               _;
                             } -> (
                             match
                               module_expr_anonymous_annotation mb_expr
                             with
                             | Some module_type ->
                                 let child_path =
                                   Path.Pdot
                                     ( Path.Pident outer_ident,
                                       Ident.name child_ident )
                                 in
                                 let signature_path =
                                   Path.Pdot
                                     ( child_path,
                                       Ident.name child_ident
                                       ^ "_signature" )
                                 in
                                 module_types :=
                                   ( signature_path,
                                     module_type.mty_type,
                                     module_type.mty_loc )
                                   :: !module_types;
                                 direct_signature_children :=
                                   ( Path.Pident outer_ident,
                                     Ident.name child_ident,
                                     signature_path )
                                   :: !direct_signature_children
                             | None -> ())
                         | _ -> ());
                         (match item.str_desc with
                         | Tstr_include { incl_mod; _ } -> (
                             match aliased_module_path incl_mod with
                             | Some included_module ->
                                 !module_applied_children
                                 |> List.iter
                                      (fun
                                        ( parent,
                                          child_name,
                                          child_functor )
                                      ->
                                        if
                                          Path.same parent
                                            included_module
                                        then
                                          direct_applied_children :=
                                            ( Path.Pident outer_ident,
                                              child_name,
                                              child_functor )
                                            :: !direct_applied_children)
                             | None -> ())
                         | _ -> ());
                         match item.str_desc with
                         | Tstr_module
                             {
                               mb_id = Some child_ident;
                               mb_expr;
                               _;
                             } -> (
                             match applied_functor_path mb_expr with
                             | Some child_functor ->
                                 direct_applied_children :=
                                   ( Path.Pident outer_ident,
                                     Ident.name child_ident,
                                     child_functor )
                                   :: !direct_applied_children
                             | None -> ())
                         | _ -> ()))
          | _ -> ());
          (match (binding.mb_id, aliased_module_path binding.mb_expr) with
          | Some ident, Some target ->
              module_aliases :=
                (Path.Pident ident, target) :: !module_aliases
          | _ -> ());
          (match (binding.mb_id, final_functor_body binding.mb_expr) with
          | Some ident, Some body ->
              let functor_path = Path.Pident ident in
              (match find_declared_result_signature body with
              | Some result_path ->
                  named_functor_results :=
                    (functor_path, result_path)
                    :: !named_functor_results
              | None ->
                  let result_path =
                    match module_expr_anonymous_annotation body with
                    | Some _ ->
                        Path.Pdot
                          (functor_path, Ident.name ident ^ "_signature")
                    | None ->
                        Path.Pdot
                          (functor_path, Ident.name ident ^ "_result")
                  in
                  synthetic_functor_results :=
                    (functor_path, result_path)
                    :: !synthetic_functor_results;
                  module_types :=
                    (result_path, body.mod_type, body.mod_loc)
                    :: !module_types)
          | _ -> ());
          Tast_iterator.default_iterator.module_binding self binding);
    }
  in
  (match typedtree with
  | `Implementation structure ->
      collect_synthetic_results.structure collect_synthetic_results structure
  | `Interface signature ->
      collect_synthetic_results.signature collect_synthetic_results signature);
  let find_synthetic_result (path : Path.t) : Path.t option =
    let rec find visited path =
      if List.exists (Path.same path) visited then None
      else
        match
          !synthetic_functor_results
          |> List.find_map (fun (candidate, result) ->
                 if Path.same path candidate then Some result else None)
        with
        | Some _ as result -> result
        | None -> (
            match
              !module_aliases
              |> List.find_map (fun (alias, target) ->
                     if Path.same path alias then Some target else None)
            with
            | Some target ->
                Option.map
                  (fun result -> Path.Pdot (path, Path.last result))
                  (find (path :: visited) target)
            | None -> None)
    in
    find [] path
  in
  let find_functor_result (path : Path.t) : Path.t option =
    let direct_results =
      !named_functor_results @ !synthetic_functor_results
    in
    let rec find visited path =
      if List.exists (Path.same path) visited then None
      else
        match
          direct_results
          |> List.find_map (fun (candidate, result) ->
                 if Path.same path candidate then Some result else None)
        with
        | Some _ as result -> result
        | None -> (
            match
              !module_aliases
              |> List.find_map (fun (alias, target) ->
                     if Path.same path alias then Some target else None)
            with
            | Some target -> (
                match find (path :: visited) target with
                | Some (Path.Pdot (_, result_name) as result)
                  when String.ends_with ~suffix:"_result" result_name ->
                    Some (Path.Pdot (path, Path.last result))
                | result -> result)
            | None -> None)
    in
    find [] path
  in
  let collect_application_results =
    let applied_functor_aliases = ref [] in
    let applied_functor_children = ref [] in
    let rec resolve_module_alias visited path =
      if List.exists (Path.same path) visited then path
      else
        match
          !module_aliases
          |> List.find_map (fun (alias, target) ->
                 if Path.same path alias then Some target else None)
        with
        | Some target -> resolve_module_alias (path :: visited) target
        | None -> path
    in
    let find_source_child functor_path child_name =
      let functor_path = resolve_module_alias [] functor_path in
      !direct_functor_children
      |> List.find_map
           (fun (candidate, name, child_path, canonical_path) ->
             if
               Path.same candidate functor_path
               && String.equal name child_name
             then Some (child_path, canonical_path)
             else None)
    in
    let find_applied_child_result path =
      !applied_functor_children
      |> List.find_map
           (fun (candidate, canonical_child, _) ->
             if Path.same candidate path then
               !applied_functor_aliases
               |> List.find_map (fun (alias, source_child) ->
                      if Path.same alias path then
                        Option.map
                          (fun source_result ->
                            Path.Pdot
                              ( canonical_child,
                                Path.last source_result ))
                          (find_synthetic_result source_child)
                      else None)
             else None)
    in
    {
      Tast_iterator.default_iterator with
      module_binding =
        (fun self binding ->
          (match (binding.mb_id, applied_functor_path binding.mb_expr) with
          | Some ident, Some functor_path -> (
              let known_result =
                match find_applied_child_result functor_path with
                | Some _ as result -> result
                | None -> find_functor_result functor_path
              in
              match known_result with
              | Some result_path ->
                  module_annotations :=
                    (Path.Pident ident, result_path)
                    :: !module_annotations
              | None
                when needs_synthetic_result_signature binding.mb_expr ->
                  let result_path =
                    derived_functor_result_signature functor_path
                  in
                  module_annotations :=
                    (Path.Pident ident, result_path)
                    :: !module_annotations;
                  module_types :=
                    ( result_path,
                      binding.mb_expr.mod_type,
                      binding.mb_loc )
                    :: !module_types
              | None -> ())
          | _ -> ());
          (match (binding.mb_id, applied_functor_path binding.mb_expr) with
          | Some binding_ident, Some functor_path -> (
              match
                Env.scrape_alias binding.mb_expr.mod_env
                  binding.mb_expr.mod_type
              with
              | Mty_signature signature ->
                  signature
                  |> List.iter (function
                       | Types.Sig_module
                           (child_ident, _, { Types.md_type; _ }, _, _)
                         when
                           (match
                              Env.scrape_alias binding.mb_expr.mod_env
                                md_type
                            with
                           | Mty_functor _ -> true
                           | _ -> false
                           | exception _ -> false) ->
                           (match
                              find_source_child functor_path
                                (Ident.name child_ident)
                            with
                           | Some (source_child, canonical_child) ->
                               let applied_child =
                                 Path.Pdot
                                   ( Path.Pident binding_ident,
                                     Ident.name child_ident )
                               in
                               applied_functor_aliases :=
                                 (applied_child, source_child)
                                 :: !applied_functor_aliases;
                               applied_functor_children :=
                                 ( applied_child,
                                   canonical_child,
                                   Path.Pident binding_ident )
                                 :: !applied_functor_children
                           | None -> ())
                       | _ -> ())
              | _ -> ()
              | exception _ -> ())
          | _ -> ());
          Tast_iterator.default_iterator.module_binding self binding);
    }
    |> fun iterator ->
    (iterator, applied_functor_aliases, applied_functor_children)
  in
  let ( collect_application_results,
        applied_functor_aliases,
        applied_functor_children ) =
    collect_application_results
  in
  (match typedtree with
  | `Implementation structure ->
      collect_application_results.structure collect_application_results
        structure
  | `Interface signature ->
      collect_application_results.signature collect_application_results
        signature);
  let aliased_result_module_types =
    !module_aliases
    |> List.filter_map (fun (alias, target) ->
           match (find_synthetic_result alias, find_synthetic_result target) with
           | Some alias_result, Some target_result ->
               !module_types
               |> List.find_map
                    (fun (candidate, module_type, location) ->
                      if Path.same candidate target_result then
                        Some (alias_result, module_type, location)
                      else None)
           | _ -> None)
  in
  let applied_child_result_signatures =
    !applied_functor_children
    |> List.filter_map
         (fun (applied_child, canonical_child, _) ->
           !applied_functor_aliases
           |> List.find_map (fun (candidate, source_child) ->
                  if Path.same candidate applied_child then
                    Option.map
                      (fun source_result ->
                        ( applied_child,
                          Path.Pdot
                            ( canonical_child,
                              Path.last source_result ) ))
                      (find_synthetic_result source_child)
                  else None))
  in
  let applied_child_result_module_types =
    applied_child_result_signatures
    |> List.filter_map
         (fun (applied_child, canonical_result) ->
           !applied_functor_aliases
           |> List.find_map (fun (candidate, source_child) ->
                  if Path.same candidate applied_child then
                    match find_synthetic_result source_child with
                    | None -> None
                    | Some source_result ->
                        !module_types
                        |> List.find_map
                             (fun
                               ( candidate_result,
                                 module_type,
                                 location )
                             ->
                               if
                                 Path.same candidate_result
                                   source_result
                               then
                                 Some
                                   ( canonical_result,
                                     module_type,
                                     location )
                               else None)
                  else None))
  in
  module_types :=
    applied_child_result_module_types
    @ aliased_result_module_types
    @ !module_types;
  let functor_result_signatures =
    (List.map fst !named_functor_results
    @ List.map fst !synthetic_functor_results
    @ List.map fst !module_aliases
    @ List.map fst !applied_functor_aliases)
    |> List.sort_uniq Path.compare
    |> List.filter_map (fun functor_path ->
           let result =
             match find_functor_result functor_path with
             | Some _ as result -> result
             | None -> (
                 match
                   !applied_functor_aliases
                   |> List.find_map (fun (alias, target) ->
                          if Path.same alias functor_path then Some target
                          else None)
                 with
                 | Some target -> find_functor_result target
                 | None -> None)
           in
           Option.map
             (fun signature -> (functor_path, signature))
             result)
    |> fun inferred ->
    List.sort_uniq
      (fun (left, _) (right, _) -> Path.compare left right)
      (applied_child_result_signatures @ inferred)
  in
  let result_module_fields =
    ((!direct_applied_children
     |> List.filter_map
          (fun (outer_functor, field_name, field_functor) ->
            match
              ( find_synthetic_result outer_functor,
                find_synthetic_result field_functor )
            with
            | Some outer_result, Some field_result ->
                Some (outer_result, field_name, field_result)
            | _ -> None))
    @ (!direct_signature_children
      |> List.filter_map
           (fun (outer_functor, field_name, field_signature) ->
             Option.map
               (fun outer_result ->
                 (outer_result, field_name, field_signature))
               (find_synthetic_result outer_functor))))
    |> List.sort_uniq (fun
         (left_result, left_field, left_signature)
         (right_result, right_field, right_signature) ->
         match Path.compare left_result right_result with
         | 0 -> (
             match String.compare left_field right_field with
             | 0 -> Path.compare left_signature right_signature
             | ordering -> ordering)
         | ordering -> ordering)
  in
  let result_namespace_includes =
    !nested_namespace_includes
    |> List.filter_map
         (fun (outer_functor, namespace, included_field) ->
           Option.map
             (fun result_signature ->
               (result_signature, namespace, included_field))
             (find_functor_result outer_functor))
    |> List.sort_uniq
         (fun
           (left_result, left_namespace, left_field)
           (right_result, right_namespace, right_field)
         ->
           match Path.compare left_result right_result with
           | 0 -> (
               match String.compare left_namespace right_namespace with
               | 0 -> String.compare left_field right_field
               | ordering -> ordering)
           | ordering -> ordering)
  in
  let rec find_parameter_types visited path =
    if List.exists (Path.same path) visited then None
    else
      match
        !functor_parameter_types_by_path
        |> List.find_map (fun (candidate, parameter_types) ->
               if Path.same candidate path then Some parameter_types
               else None)
      with
      | Some _ as parameter_types -> parameter_types
      | None ->
          let aliases = !module_aliases @ !applied_functor_aliases in
          (match
             aliases
             |> List.find_map (fun (alias, target) ->
                    if Path.same alias path then Some target else None)
           with
          | Some target -> find_parameter_types (path :: visited) target
          | None -> None)
  in
  let aliased_functor_parameter_types =
    (!module_aliases @ !applied_functor_aliases)
    |> List.filter_map (fun (alias, _) ->
           Option.map
             (fun parameter_types -> (alias, parameter_types))
             (find_parameter_types [] alias))
  in
  let has_named_parameter_annotation parameter_path =
    !module_annotations
    |> List.exists (fun (candidate, signature_path) ->
           Path.same parameter_path candidate
           && not
                (!anonymous_signatures
                |> List.exists (fun (anonymous_path, _, _) ->
                       Path.same signature_path anonymous_path)))
  in
  let anonymous_functor_parameters =
    let canonical_signatures = ref [] in
    List.rev !anonymous_functor_parameters
    |> List.map
         (fun
           ( functor_path,
             parameter_name,
             parameter_path,
             signature_path )
         ->
           let canonical_path =
             match
               !anonymous_signature_fingerprints
               |> List.find_map (fun (candidate, fingerprint) ->
                      if Path.same candidate signature_path then
                        Some fingerprint
                      else
                        None)
             with
             | None -> signature_path
             | Some fingerprint -> (
                 match
                   !canonical_signatures
                   |> List.find_map
                        (fun (candidate_fingerprint, candidate_path) ->
                          if
                            String.equal candidate_fingerprint fingerprint
                          then
                            Some candidate_path
                          else
                            None)
                 with
                 | Some canonical_path -> canonical_path
                 | None ->
                     canonical_signatures :=
                       (fingerprint, signature_path)
                       :: !canonical_signatures;
                     signature_path)
           in
           ( functor_path,
             parameter_name,
             parameter_path,
             canonical_path ))
    |> List.filter_map
         (fun (functor_path, parameter_name, parameter_path, signature_path) ->
           match parameter_path with
           | Some parameter_path
             when has_named_parameter_annotation parameter_path ->
               None
           | Some _ | None ->
               Some (functor_path, parameter_name, signature_path))
  in
  let retained_anonymous_signatures =
    !anonymous_module_signatures
    @ (anonymous_functor_parameters |> List.map (fun (_, _, path) -> path))
  in
  let anonymous_signatures =
    !anonymous_signatures
    |> List.filter (fun (path, _, _) ->
           List.exists (Path.same path) retained_anonymous_signatures)
  in
  let module_annotations =
    let direct_annotations = !module_annotations in
    let canonical_annotations = ref [] in
    let rec collect_structure owner (structure : Typedtree.structure) =
      structure.str_items
      |> List.iter (fun (item : Typedtree.structure_item) ->
             match item.str_desc with
             | Tstr_module binding ->
                 collect_binding owner binding
             | Tstr_recmodule bindings ->
                 List.iter (collect_binding owner) bindings
             | _ -> ())
    and collect_binding owner (binding : Typedtree.module_binding) =
      match binding.mb_id with
      | None -> ()
      | Some ident ->
          let local_path = Path.Pident ident in
          let canonical_path =
            match owner with
            | None -> local_path
            | Some owner ->
                Path.Pdot (owner, Ident.name ident)
          in
          (match
             direct_annotations
             |> List.find_map (fun (candidate, signature) ->
                    if Path.same candidate local_path then
                      Some signature
                    else None)
           with
          | Some signature
            when not (Path.same canonical_path local_path) ->
              canonical_annotations :=
                (canonical_path, signature)
                :: !canonical_annotations
          | Some _ | None -> ());
          let nested_structure =
            match module_expr_structure binding.mb_expr with
            | Some _ as structure -> structure
            | None -> (
                match final_functor_body binding.mb_expr with
                | Some body -> module_expr_structure body
                | None -> None)
          in
          (match nested_structure with
          | Some structure ->
              collect_structure (Some canonical_path) structure
          | None -> ())
    in
    (match typedtree with
    | `Implementation structure ->
        collect_structure None structure
    | `Interface _ -> ());
    List.rev_append !canonical_annotations
      (List.rev direct_annotations)
  in
  {
    module_annotations;
    module_types = List.rev !module_types;
    anonymous_signatures = List.rev anonymous_signatures;
    anonymous_functor_parameters =
      anonymous_functor_parameters;
    functor_parameter_types =
      List.rev
        (aliased_functor_parameter_types
        @ !functor_parameter_types_by_path);
    functor_result_signatures;
    result_module_fields;
    result_namespace_includes;
    applied_functor_children =
      List.rev !applied_functor_children;
  }
