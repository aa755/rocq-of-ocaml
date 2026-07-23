open SmartPrint
(** An OCaml signature which will by transformed into a dependent record. *)

open Typedtree
open Monad.Notations

type item =
  | Error of string
  | Documentation of string
  | Module of Name.t * Type.t
  | ModuleWithSignature of item list
  | TypExistential of Name.t
  | TypSynonym of Name.t * Type.t
  | Value of Name.t * Type.t
  | ModuleWithTypeParams of Name.t * Type.t * (Name.t * int) list

type t = { items : item list; typ_params : (Name.t * int) list }

type let_in_type_target =
  | LocalConstructor of Name.t
  | ManifestConstructor of Type.t

type let_in_type = (Name.t list * let_in_type_target) list

let rec path_contains_functor_application (path : Path.t) : bool =
  match path with
  | Papply _ -> true
  | Pdot (path, _) | Pextra_ty (path, _) ->
      path_contains_functor_application path
  | Pident _ -> false

let rec is_functor_application_alias (env : Env.t) (typ : Types.type_expr) :
    bool =
  match Types.get_desc typ with
  | Tconstr (path, _, _) ->
      let path =
        try
          match path with
          | Path.Pdot (module_path, field) ->
              Path.Pdot
                (Env.normalize_module_path None env module_path, field)
          | _ -> Env.normalize_type_path None env path
        with _ -> path
      in
      path_contains_functor_application path
  | Tlink typ | Tsubst (typ, _) | Tpoly (typ, _) ->
      is_functor_application_alias env typ
  | _ -> false

let add_new_let_in_type (prefix : string list) (let_in_type : let_in_type)
    (id : Ident.t) : (Name.t * let_in_type) Monad.t =
  let* name = Name.of_ident false id in
  let* prefixed_name = Name.of_strings false (prefix @ [ Ident.name id ]) in
  let* qualified_source =
    prefix
    |> Monad.List.map (fun component -> Name.of_string false component)
  in
  let aliases =
    ([ name ], LocalConstructor prefixed_name)
    ::
    if prefix = [] then []
    else
      [
        ( qualified_source @ [ name ],
          LocalConstructor prefixed_name );
      ]
  in
  return (prefixed_name, aliases @ let_in_type)

let apply_let_in_type (let_in_type : let_in_type) (typ : Type.t) : Type.t =
  List.fold_left
    (fun typ (source, target) ->
      match target with
      | LocalConstructor target -> Type.subst_path source target typ
      | ManifestConstructor target ->
          Type.subst_constructor_definition source target typ)
    typ let_in_type

let quantified_value_type ?(expand_aliases = false) (typ : Types.type_expr) :
    Type.t Monad.t =
  let* typ, _, _ =
    Type.of_typ_expr ~expand_aliases true Name.Map.empty typ
  in
  let typ_args =
    Type.typ_args_of_typ typ |> Name.Set.elements
    |> List.map (fun typ -> (typ, 0))
  in
  return (Type.ForallTyps (typ_args, typ))

type constructor_alias = Name.t list * MixedPath.t

let constructor_aliases_of_signature
    ?(abstract_functor_applications = false) (signature : Types.signature) :
    constructor_alias list Monad.t =
  let* env = get_env in
  signature
  |> Monad.List.filter_map (function
       | Types.Sig_type
           (ident, { type_manifest = Some manifest; type_params; _ }, _, _)
         when
           not
             (abstract_functor_applications
             && is_functor_application_alias env manifest) ->
           let* source = Name.of_ident false ident in
           let* parameters =
             Monad.List.map Type.of_type_expr_variable type_params
           in
           let* target = Type.of_type_expr_without_free_vars manifest in
           let target =
             match parameters with
             | [] -> target
             | _ :: _ -> Type.FunTyps (parameters, target)
           in
           (match Type.direct_constructor_path target with
           | Some target
             when MixedPath.to_string target <> Name.to_string source ->
               return (Some ([ source ], target))
           | _ -> return None)
       | _ -> return None)

let apply_constructor_aliases (aliases : constructor_alias list) (typ : Type.t)
    : Type.t =
  List.fold_left
    (fun typ (source, target) ->
      Type.subst_constructor_path source target typ)
    typ aliases

let rec items_of_types_signature
    ?(abstract_functor_applications = false) ?(expand_aliases = false)
    ?signature_path
    (prefix : string list)
    (let_in_type : let_in_type) (signature : Types.signature) :
    (item list * let_in_type) Monad.t =
  let* env = get_env in
  let* constructor_aliases =
    constructor_aliases_of_signature ~abstract_functor_applications signature
  in
  let of_types_signature_item (signature_item : Types.signature_item) :
      (item * let_in_type) Monad.t =
    match signature_item with
    | Sig_value (ident, { val_type; _ }, _) ->
        let* prefixed_name =
          Name.of_strings true (prefix @ [ Ident.name ident ])
        in
        let* typ = quantified_value_type ~expand_aliases val_type in
        let typ = apply_constructor_aliases constructor_aliases typ in
        let typ_with_let_in_type =
          apply_let_in_type let_in_type typ
        in
        return (Value (prefixed_name, typ_with_let_in_type), let_in_type)
    | Sig_type (ident, { type_manifest = None; _ }, _, _) ->
        let* name, let_in_type = add_new_let_in_type prefix let_in_type ident in
        return (TypExistential name, let_in_type)
    | Sig_type
        ( ident,
          { type_manifest = Some typ; _ },
          _,
          _ )
      when abstract_functor_applications
           && is_functor_application_alias env typ ->
        let* name, let_in_type = add_new_let_in_type prefix let_in_type ident in
        return (TypExistential name, let_in_type)
    | Sig_type (ident, { type_manifest = Some typ; type_params; _ }, _, _) ->
        let* name, let_in_type = add_new_let_in_type prefix let_in_type ident in
        let* typ_args =
          type_params
          |> Monad.List.map (fun typ_param ->
                 let* typ = Type.of_type_expr_variable typ_param in
                 return (typ, 0))
        in
        let* typ = Type.of_type_expr_without_free_vars typ in
        let typ = apply_constructor_aliases constructor_aliases typ in
        let typ_with_let_in_type =
          apply_let_in_type let_in_type
            (Type.FunTyps (List.map fst typ_args, typ))
        in
        return (TypSynonym (name, typ_with_let_in_type), let_in_type)
    | Sig_typext (_, { ext_type_path; _ }, _, _)
      when abstract_functor_applications
           && Path.same ext_type_path Predef.path_exn ->
        return (ModuleWithSignature [], let_in_type)
    | Sig_typext (_, { ext_type_path; _ }, _, _) ->
        let name = Path.name ext_type_path in
        raise
          (Error ("extensible_type_definition `" ^ name ^ "`"), let_in_type)
          ExtensibleType
          ("Extensible type '" ^ name ^ "' not handled")
    | Sig_module (ident, _, { md_type; _ }, _, _) -> (
        let* name = Name.of_ident false ident in
        let* is_first_class =
          match signature_path with
          | Some parent_signature ->
              let* field_signature =
                get_result_module_field parent_signature
                  (Ident.name ident)
              in
              (match field_signature with
              | Some field_signature ->
                  return
                    (IsFirstClassModule.Found field_signature)
              | None ->
                  IsFirstClassModule.is_module_typ_first_class md_type
                    (Some (Path.Pident ident)))
          | None ->
              IsFirstClassModule.is_module_typ_first_class md_type
                (Some (Path.Pident ident))
        in
        match is_first_class with
        | Found signature_path ->
            PathName.of_path_with_convert false signature_path
            >>= fun signature_path_name ->
            let* constructor_aliases =
              let* env = get_env in
              match Mtype.scrape env md_type with
              | Mty_signature signature ->
                  constructor_aliases_of_signature
                    ~abstract_functor_applications signature
              | _ -> return []
            in
            let* manifest_aliases =
              let* env = get_env in
              match Mtype.scrape env md_type with
              | Mty_signature signature ->
                  signature
                  |> Monad.List.filter_map (function
                       | Types.Sig_type
                           ( type_ident,
                             {
                               type_manifest = Some manifest;
                               type_params;
                               _;
                             },
                             _,
                             _ )
                         when
                             not
                               (abstract_functor_applications
                             && is_functor_application_alias env manifest) ->
                           let* type_name =
                             Name.of_ident false type_ident
                           in
                           let* parameters =
                             Monad.List.map Type.of_type_expr_variable
                               type_params
                           in
                           let* target =
                             Type.of_type_expr_without_free_vars manifest
                           in
                           let target =
                             Type.FunTyps
                               ( parameters,
                                 apply_constructor_aliases constructor_aliases
                                   target )
                             |> apply_let_in_type let_in_type
                           in
                           return
                             (Some
                                ( [ name; type_name ],
                                  ManifestConstructor target ))
                       | _ -> return None)
              | _ -> return []
            in
            let mapper ident { Types.type_manifest; type_params; _ } =
              let name = Ident.name ident in
              (match type_manifest with
              | None -> return (Type.Arity (List.length type_params))
              | Some type_manifest
                when abstract_functor_applications
                     && is_functor_application_alias env type_manifest ->
                  return (Type.Arity (List.length type_params))
              | Some type_manifest ->
                  type_params |> Monad.List.map Type.of_type_expr_variable
                  >>= fun typ_args ->
                  Type.of_type_expr_without_free_vars type_manifest
                  >>= fun typ ->
                  let typ =
                    Type.FunTyps
                      (typ_args, apply_constructor_aliases constructor_aliases typ)
                  in
                  return (Type.Typ typ))
              >>= fun arity_or_typ ->
              return (Some (Tree.Item (name, arity_or_typ)))
            in
            let* typ_params =
              ModuleTypParams.get_module_typ_typ_params mapper md_type
            in
            let* target_typ_params =
              ModuleTyp.get_signature_typ_params_arity
                signature_path
            in
            let target_typ_param_paths =
              Tree.flatten target_typ_params |> List.map fst
            in
            let* typ_params =
              Tree.flatten typ_params
              |> List.filter (fun (path, _) ->
                     List.exists
                       (fun target_path -> target_path = path)
                       target_typ_param_paths)
              |> Monad.List.map (fun (path, arity_or_typ) ->
                     let* name = Name.of_strings false path in
                     let* typ_name =
                       Name.of_strings false (Ident.name ident :: path)
                     in
                     match arity_or_typ with
                     | Type.Arity _ ->
                         return (name, Some (Type.Variable typ_name))
                     | Typ typ -> return (name, Some typ))
            in
            let* let_in_type =
              typ_params
              |> Monad.List.fold_left
                   (fun let_in_type (typ_name, typ) ->
                     match typ with
                     | Some (Type.Variable target) ->
                         return
                           ( ( [ name; typ_name ],
                               LocalConstructor target )
                           :: let_in_type )
                     | Some typ ->
                         let typ = apply_let_in_type let_in_type typ in
                         return
                           ( ( [ name; typ_name ],
                               ManifestConstructor typ )
                           :: let_in_type )
                     | None -> return let_in_type)
                   (manifest_aliases @ let_in_type)
            in
            let* application_signature_hint =
              get_signature_hint (Path.Pident ident)
            in
            let record_typ_params =
              match application_signature_hint with
              | Some hint
                when Path.same hint signature_path
                     && String.ends_with ~suffix:"_result"
                          (Path.last signature_path) ->
                  ( Name.of_string_raw "_fargs",
                    Some
                      (Type.Variable
                         (Name.of_string_raw
                            (Name.to_string name ^ "_fargs"))) )
                  :: typ_params
              | Some _ | None -> typ_params
            in
            let result =
              ( Module
                  ( name,
                    Type.Signature
                      (signature_path_name, record_typ_params) ),
                let_in_type )
            in
            if abstract_functor_applications then return result
            else
              raise result Module
                ("Sub-module '" ^ Ident.name ident ^ "' in included "
               ^ "signature.\n\n"
               ^ "Sub-modules in included signatures are not handled well \
                  yet. It does not work if there are destructive type \
                  substitutions (:=) in the sub-module or type definitions in \
                  the sub-module's source signature. We do not develop this \
                  feature further as it is working in our cases.\n\n"
               ^ "A safer way is to make a sub-module instead of an `include`.")
        | Not_found reason -> (
            let* env = get_env in
            match Env.scrape_alias env md_type with
            | Mty_signature signature ->
                let prefix = prefix @ [ Ident.name ident ] in
                let* items, nested_let_in_type =
                  items_of_types_signature ~abstract_functor_applications
                    ~expand_aliases ?signature_path prefix let_in_type
                    signature
                in
                let nested_let_in_type =
                  nested_let_in_type
                  |> List.filter (fun ((source, _) as alias) ->
                         List.length source > 1
                         || List.mem alias let_in_type)
                in
                return (ModuleWithSignature items, nested_let_in_type)
            | Mty_functor _ when abstract_functor_applications ->
                (* Functor-valued module fields are static OCaml namespace
                   components.  The generated result record carries runtime
                   values, while later applications are translated from their
                   statically known module paths. *)
                return (ModuleWithSignature [], let_in_type)
            | Mty_functor _ ->
                let* field_name =
                  Name.of_strings false (prefix @ [ Ident.name ident ])
                in
                let* result_signature_path =
                  get_functor_result_signature (Path.Pident ident)
                in
                let* parameter_types =
                  get_functor_parameter_types (Path.Pident ident)
                in
                let* module_typ =
                  ModuleTyp.of_types ?result_signature_path
                    ?parameter_types md_type
                in
                let* (_, functor_params, result_free_vars), typ =
                  ModuleTyp.to_typ [] (Name.to_string field_name) false
                    module_typ
                in
                let typ =
                  match result_signature_path with
                  | None -> typ
                  | Some _ ->
                      let rec apply_result_fargs = function
                        | Type.ForallTyps (parameters, result) ->
                            Type.ForallTyps
                              (parameters, apply_result_fargs result)
                        | Type.ForallModule (name, parameter, result) ->
                            Type.ForallModule
                              (name, parameter, apply_result_fargs result)
                        | Type.Signature (path, parameters) ->
                            let build_fargs =
                              Type.Apply
                                ( MixedPath.PathName
                                    {
                                      path with
                                      PathName.base =
                                        Name.of_string_raw "Build_FArgs";
                                    },
                                  functor_params
                                  |> List.map (fun (name, _) ->
                                         (Type.Variable name, false)) )
                            in
                            Type.Signature
                              ( path,
                                ( Name.of_string_raw "_fargs",
                                  Some build_fargs )
                                :: parameters )
                        | result -> result
                      in
                      apply_result_fargs typ
                in
                let typ, result_free_vars =
                  match (result_signature_path, result_free_vars) with
                  | None, _ :: _ ->
                      let build_fargs =
                        String.concat " "
                          ((Name.to_string field_name ^ ".Build_FArgs")
                          :: List.map
                               (fun (name, _) -> Name.to_string name)
                               functor_params)
                      in
                      let typ =
                        result_free_vars
                        |> List.fold_left
                             (fun typ
                                  { ModuleTyp.name; source_name; _ } ->
                               let companion =
                                 MixedPath.AppliedAccess
                                   ( PathName.of_name [ field_name ]
                                       source_name,
                                     [ ("_fargs", build_fargs) ],
                                     [] )
                               in
                               Type.subst_constructor_application name
                                 (Type.Apply (companion, [])) typ)
                             typ
                      in
                      (typ, [])
                  | _ -> (typ, result_free_vars)
                in
                let typ_params =
                  result_free_vars
                  |> List.map (fun { ModuleTyp.name; arity; _ } ->
                         (name, arity))
                in
                let let_in_type =
                  result_free_vars
                  |> List.fold_left
                       (fun let_in_type
                            { ModuleTyp.name = target; source_name; _ } ->
                         ( [ name; source_name ],
                           LocalConstructor target )
                         :: let_in_type)
                       let_in_type
                in
                return
                  ( ModuleWithTypeParams (field_name, typ, typ_params),
                    let_in_type )
            | _ ->
                raise
                  (Error ("module " ^ Ident.name ident), let_in_type)
                  Module
                  ("Signature name for the module '" ^ Ident.name ident
                 ^ "' in included signature not found.\n\n" ^ reason)))
    | Sig_modtype (_, _, _) when abstract_functor_applications ->
        (* A module type is a static namespace component, not a runtime field
           of the first-class record representing a synthesized functor
           result.  Its declaration is emitted from the module body itself. *)
        return (ModuleWithSignature [], let_in_type)
    | Sig_modtype (ident, _, _) ->
        let name = Ident.name ident in
        raise
          (Error ("module_type" ^ name), let_in_type)
          NotSupported
          ("Signatures '" ^ name ^ "' inside signature is not handled")
    | Sig_class (ident, _, _, _) ->
        let name = Ident.name ident in
        raise
          (Error ("class" ^ name), let_in_type)
          NotSupported
          ("Class '" ^ name ^ "' not handled.")
    | Sig_class_type (ident, _, _, _) ->
        let name = Ident.name ident in
        raise
          (Error ("class_type" ^ name), let_in_type)
          NotSupported
          ("Class type '" ^ name ^ "' not handled.")
  in
  match signature with
  | [] -> return ([], let_in_type)
  | item :: items ->
      let* item, let_in_type = of_types_signature_item item in
      let* items, let_in_type =
        items_of_types_signature ~abstract_functor_applications ~expand_aliases
          ?signature_path prefix let_in_type items
      in
      return (item :: items, let_in_type)

let of_types_signature ?(abstract_functor_applications = false)
    ?(expand_aliases = false) ?signature_path
    (signature : Types.signature) : t Monad.t =
  let* items, _ =
    items_of_types_signature ~abstract_functor_applications ~expand_aliases
      ?signature_path [] [] signature
  in
  let* typ_params =
    if abstract_functor_applications then
      let* env = get_env in
      let mapper ident { Types.type_manifest; type_params; _ } =
        match type_manifest with
        | None ->
            return
              (Some
                 (Tree.Item (Ident.name ident, List.length type_params)))
        | Some typ when is_functor_application_alias env typ ->
            return
              (Some
                 (Tree.Item (Ident.name ident, List.length type_params)))
        | Some _ -> return None
      in
      ModuleTypParams.get_signature_typ_params mapper signature
    else ModuleTypParams.get_signature_typ_params_arity signature
  in
  let* typ_params =
    Tree.flatten typ_params
    |> Monad.List.map (fun (path, arity) ->
           let* name = Name.of_strings false path in
           return (name, arity))
  in
  let rec item_typ_params = function
    | ModuleWithTypeParams (_, _, typ_params) -> typ_params
    | ModuleWithSignature items ->
        items |> List.concat_map item_typ_params
    | _ -> []
  in
  let typ_params =
    List.fold_left
      (fun typ_params (name, arity) ->
        if List.exists (fun (other, _) -> Name.equal name other) typ_params then
          typ_params
        else typ_params @ [ (name, arity) ])
      typ_params (items |> List.concat_map item_typ_params)
  in
  return { items; typ_params }

let wrap_documentation (items_value : (item list * 'a) Monad.t) :
    (item list * 'a) Monad.t =
  let* documentation = get_documentation in
  match documentation with
  | None -> items_value
  | Some documentation ->
      let* items, value = items_value in
      return (Documentation documentation :: items, value)

let rec of_signature_items (prefix : string list) (let_in_type : let_in_type)
    (items : signature_item list) (last_env : Env.t) : item list Monad.t =
  let of_signature_item (item : signature_item) (next_env : Env.t) :
      (item list * let_in_type) Monad.t =
    set_env item.sig_env
      (set_loc item.sig_loc
         (wrap_documentation
            (match item.sig_desc with
            | Tsig_attribute _ -> return ([], let_in_type)
            | Tsig_class _ ->
                raise
                  ([ Error "class" ], let_in_type)
                  NotSupported "Signature item `class` not handled."
            | Tsig_class_type _ ->
                raise
                  ([ Error "class_type" ], let_in_type)
                  NotSupported "Signature item `class_type` not handled."
            | Tsig_exception _ -> return ([], let_in_type)
            | Tsig_include { incl_type; _ } ->
                set_env next_env
                  (items_of_types_signature prefix let_in_type incl_type)
            | Tsig_modsubst _ ->
                raise
                  ([ Error "module_substitution" ], let_in_type)
                  NotSupported "We do not handle module substitutions"
            | Tsig_modtype _ | Tsig_modtypesubst _ ->
                raise
                  ([ Error "module_type" ], let_in_type)
                  NotSupported "Signatures inside signatures are not handled."
            | Tsig_module { md_id = Some ident; _ }
              when Ident.name ident = "Internal_for_tests" ->
                return ([], let_in_type)
            | Tsig_module { md_id; md_type; _ } -> (
                let id =
                  match md_id with
                  | Some md_id -> Ident.name md_id
                  | None -> "_"
                in
                match md_type.mty_desc with
                | Tmty_signature signature ->
                    let prefix = prefix @ [ id ] in
                    let* items =
                      of_signature_items prefix let_in_type signature.sig_items
                        next_env
                    in
                    return ([ ModuleWithSignature items ], let_in_type)
                | _ ->
                    push_env
                      (let prefixed_id = String.concat "_" (prefix @ [ id ]) in
                       let* prefixed_name = Name.of_string false prefixed_id in
                       let* module_typ = ModuleTyp.of_ocaml md_type in
                       let* _, typ =
                         ModuleTyp.to_typ [] prefixed_id false module_typ
                       in
                       return ([ Module (prefixed_name, typ) ], let_in_type)))
            | Tsig_open _ -> return ([], let_in_type)
            | Tsig_recmodule _ ->
                raise
                  ([ Error "recursive_module" ], let_in_type)
                  NotSupported "Recursive module signatures are not handled."
            | Tsig_type
                (_, [ { typ_id; typ_type = { type_manifest = None; _ }; _ } ])
              ->
                let* name, let_in_type =
                  add_new_let_in_type prefix let_in_type typ_id
                in
                return ([ TypExistential name ], let_in_type)
            | Tsig_type (_, typs) | Tsig_typesubst typs -> (
                match typs with
                | [
                 {
                   typ_id;
                   typ_type = { type_manifest = Some typ; type_params; _ };
                   _;
                 };
                ] ->
                    let* name, let_in_type =
                      add_new_let_in_type prefix let_in_type typ_id
                    in
                    let* typ_args =
                      type_params |> Monad.List.map Type.of_type_expr_variable
                    in
                    let* typ = Type.of_type_expr_without_free_vars typ in
                    let typ_with_let_in_type =
                      apply_let_in_type let_in_type
                        (Type.FunTyps (typ_args, typ))
                    in
                    return
                      ([ TypSynonym (name, typ_with_let_in_type) ], let_in_type)
                | typs ->
                    let* rev_typs, let_in_type =
                      Monad.List.fold_left
                        (fun (rev_typs, let_in_type) typ ->
                          let* name, let_in_type =
                            add_new_let_in_type prefix let_in_type typ.typ_id
                          in
                          return (TypExistential name :: rev_typs, let_in_type))
                        ([], let_in_type) typs
                    in
                    raise
                      (List.rev rev_typs, let_in_type)
                      NotSupported
                      "Mutual type definitions in signatures not handled.")
            | Tsig_typext _ -> return ([], let_in_type)
            | Tsig_value { val_id; val_desc = { ctyp_type; _ }; _ } ->
                let* prefixed_name =
                  Name.of_strings true (prefix @ [ Ident.name val_id ])
                in
                let* typ = quantified_value_type ctyp_type in
                let typ_with_let_in_type =
                  apply_let_in_type let_in_type typ
                in
                return
                  ([ Value (prefixed_name, typ_with_let_in_type) ], let_in_type))))
  in
  match items with
  | [] -> return []
  | item :: items ->
      let next_env =
        match items with { sig_env; _ } :: _ -> sig_env | _ -> last_env
      in
      let* first_items, let_in_type = of_signature_item item next_env in
      let* last_items = of_signature_items prefix let_in_type items last_env in
      return (first_items @ last_items)

let of_signature (signature : signature) : t Monad.t =
  push_env
    (let* items =
       of_signature_items [] [] signature.sig_items signature.sig_final_env
     in
     ModuleTypParams.get_signature_typ_params_arity signature.sig_type
     >>= fun typ_params ->
     let* typ_params =
       Tree.flatten typ_params
       |> Monad.List.map (fun (path, arity) ->
              let* name = Name.of_strings false path in
              return (name, arity))
     in
     return { items; typ_params })

let to_coq_prefixed_name (prefix : Name.t list) (name : Name.t) : SmartPrint.t =
  separate !^"_" (List.map Name.to_coq (prefix @ [ name ]))

let rec to_coq_item (signature_item : item) : SmartPrint.t =
  match signature_item with
  | Error message -> !^("(* " ^ message ^ " *)")
  | Documentation message -> !^("(** " ^ message ^ " *)")
  | Module (name, typ) ->
      nest (Name.to_coq name ^^ !^":" ^^ Type.to_coq None None typ ^-^ !^";")
  | ModuleWithTypeParams (name, typ, _) ->
      nest (Name.to_coq name ^^ !^":" ^^ Type.to_coq None None typ ^-^ !^";")
  | ModuleWithSignature items -> separate newline (to_coq_items items)
  | TypExistential name ->
      nest (Name.to_coq name ^^ !^":=" ^^ Name.to_coq name ^-^ !^";")
  | TypSynonym (name, typ) ->
      nest (Name.to_coq name ^^ !^":=" ^^ Type.to_coq None None typ ^-^ !^";")
  | Value (name, typ) ->
      nest (Name.to_coq name ^^ !^":" ^^ Type.to_coq None None typ ^-^ !^";")

and to_coq_items (items : item list) : SmartPrint.t list =
  List.map to_coq_item items

let rec item_has_field (item : item) : bool =
  match item with
  | Error _ | Documentation _ -> false
  | ModuleWithSignature items -> List.exists item_has_field items
  | Module _
  | ModuleWithTypeParams _
  | TypExistential _
  | TypSynonym _
  | Value _ ->
      true

let to_coq_definition (fargs : FArgs.t) (name : Name.t) (signature : t) :
    SmartPrint.t =
  let declaration =
    if not (List.exists item_has_field signature.items) then
        nest
          (!^"Inductive" ^^ !^"signature" ^^ FArgs.to_coq fargs
          ^^ Type.to_coq_grouped_typ_params Type.Braces signature.typ_params
          ^^ nest (!^":" ^^ Pp.set)
          ^^ !^":=" ^^ newline
          ^^ !^"|" ^^ !^"Build_signature" ^^ !^":" ^^ !^"signature" ^-^ !^".")
    else
        nest
          (!^"Record" ^^ !^"signature" ^^ FArgs.to_coq fargs
          ^^ Type.to_coq_grouped_typ_params Type.Braces signature.typ_params
          ^^ nest (!^":" ^^ Pp.set)
          ^^ !^":=" ^^ !^"{" ^^ newline
          ^^ indent (separate newline (to_coq_items signature.items))
          ^^ newline ^^ !^"}" ^-^ !^".")
  in
  !^"Module" ^^ Name.to_coq name ^-^ !^"." ^^ newline
  ^^ indent declaration
  ^^ newline ^^ !^"End" ^^ Name.to_coq name ^-^ !^"." ^^ newline
  ^^ nest
       (!^"Definition" ^^ Name.to_coq name ^^ FArgs.to_coq fargs
       ^^ !^":="
       ^^
       match fargs with
       | Some _ ->
           separate space
             ((!^"@" ^-^ Name.to_coq name ^-^ !^"." ^-^ !^"signature")
             :: FArgs.to_coq_underscores fargs)
           ^-^ !^"."
       | None ->
           (match signature.typ_params with
           | [] -> empty
           | _ :: _ -> !^"@")
           ^-^ Name.to_coq name ^-^ !^"." ^-^ !^"signature" ^-^ !^".")
  ^^
  match (fargs, signature.typ_params) with
  | None, [] -> empty
  | _ ->
      newline
      ^^ nest
           (!^"Arguments" ^^ Name.to_coq name
           ^^ nest
                (braces
                   (separate space
                      (FArgs.to_coq_underscores fargs
                      @ Pp.n_underscores (List.length signature.typ_params))))
           ^-^ !^".")
