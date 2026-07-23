open SmartPrint
open Monad.Notations

type free_var = { name : Name.t; arity : int; source_name : Name.t }
type free_vars = free_var list

let to_coq_grouped_free_vars (free_vars : free_vars) : SmartPrint.t =
  free_vars
  |> List.map (fun { name; arity; _ } -> (name, arity))
  |> Type.to_coq_grouped_typ_params Type.Braces

module Module = struct
  type t =
    | Error of string
    | With of
        PathName.t
        * Type.arity_or_typ Tree.t
        * string list list
        * (Name.t * Type.t option) list

  (** Return a type together with the list of its free variables with arity. We
      prefix the names of the free variables by the module name. *)
  let to_typ (functor_params : Name.t list) (module_name : string)
      (with_implicits : bool) (module_typ : t) : (free_vars * Type.t) Monad.t =
    match module_typ with
    | Error message -> return ([], Type.Error message)
    | With (path_name, typ_values, parameter_paths, explicit_params) ->
        let typ_values =
          Tree.flatten typ_values
          |> List.filter (fun (path, _) ->
                 List.exists
                   (fun parameter_path -> parameter_path = path)
                   parameter_paths)
        in
        let* free_vars =
          if with_implicits then return []
          else
            typ_values
            |> Monad.List.filter_map (fun (path, arity_or_typ) ->
                   match arity_or_typ with
                   | Type.Arity arity ->
                       let* name =
                         Name.of_strings false (module_name :: path)
                       in
                       let* source_name = Name.of_strings false path in
                       return (Some { name; arity; source_name })
                   | _ -> return None)
        in
        let* typ_params =
          typ_values
          |> Monad.List.map (fun (path, arity_or_typ) ->
                 let* param_name = Name.of_strings false path in
                 match arity_or_typ with
                 | Type.Arity _ ->
                     if with_implicits then return (param_name, None)
                     else
                       let* name =
                         Name.of_strings false (module_name :: path)
                       in
                       let functor_params =
                         functor_params
                         |> List.map (fun name -> Type.Variable name)
                       in
                       let typs =
                         List.combine functor_params
                           (Type.tag_no_args functor_params)
                       in
                       let typ = Type.Apply (MixedPath.of_name name, typs) in
                       return (param_name, Some typ)
                 | Typ typ -> return (param_name, Some typ))
        in
        return
          ( free_vars,
            Type.Signature (path_name, explicit_params @ typ_params) )
end

type t = (string * Module.t) list * Module.t

let rec path_contains_functor_application (path : Path.t) : bool =
  match path with
  | Papply _ -> true
  | Pdot (path, _) | Pextra_ty (path, _) ->
      path_contains_functor_application path
  | Pident _ -> false

let is_functor_application_alias (typ : Types.type_expr) : bool =
  match Types.get_desc typ with
  | Tconstr (path, _, _) -> path_contains_functor_application path
  | _ -> false

(** Decompose a module-type path rooted below an applicative functor path.
    OCaml represents [F(A)(B).S] as path applications, while Rocq-of-OCaml
    represents the functor arguments by [F.Build_FArgs A B].  The static
    signature name is therefore [F.S], parameterized by that [FArgs] value. *)
let decompose_applied_signature_path (path : Path.t) :
    (Path.t * Path.t list) option =
  let rec collect_applications path arguments =
    match path with
    | Path.Papply (functor_path, argument_path) ->
        collect_applications functor_path (argument_path :: arguments)
    | _ -> (path, arguments)
  in
  let rec replace_application path =
    match path with
    | Path.Pdot (prefix, field) -> (
        match replace_application prefix with
        | Some (static_prefix, arguments) ->
            Some (Path.Pdot (static_prefix, field), arguments)
        | None -> None)
    | Path.Pextra_ty (prefix, extra) -> (
        match replace_application prefix with
        | Some (static_prefix, arguments) ->
            Some (Path.Pextra_ty (static_prefix, extra), arguments)
        | None -> None)
    | Path.Papply _ ->
        let static_path, arguments = collect_applications path [] in
        Some (static_path, arguments)
    | Path.Pident _ -> None
  in
  replace_application path

let signature_path_and_explicit_params (signature_path : Path.t) :
    (PathName.t * (Name.t * Type.t option) list) Monad.t =
  match decompose_applied_signature_path signature_path with
  | None ->
      let* signature_path_name =
        PathName.of_path_with_convert false signature_path
      in
      return (signature_path_name, [])
  | Some (static_signature_path, argument_paths) ->
      let* signature_path_name =
        PathName.of_path_with_convert false static_signature_path
      in
      let build_fargs_path =
        {
          signature_path_name with
          PathName.base = Name.of_string_raw "Build_FArgs";
        }
      in
      let* arguments =
        argument_paths
        |> Monad.List.map (fun argument_path ->
               let* argument = MixedPath.of_path false argument_path in
               return (Type.Apply (argument, []), false))
      in
      let fargs =
        Type.Apply (MixedPath.PathName build_fargs_path, arguments)
      in
      return
        ( signature_path_name,
          [ (Name.of_string_raw "_fargs", Some fargs) ] )

let get_signature_typ_params_arity (signature_path : Path.t) :
    int Tree.t Monad.t =
  let* env = get_env in
  match Env.find_modtype signature_path env with
  | declaration ->
      ModuleTypParams.get_module_typ_declaration_typ_params_arity declaration
  | exception Not_found ->
      let* hinted_module_type = get_module_type_hint signature_path in
      (match hinted_module_type with
      | None ->
          raise [] Unexpected
            ("The module type `" ^ Path.name signature_path
           ^ "` is not present in the current OCaml typing environment.")
      | Some module_type ->
          let abstract_functor_applications =
            String.ends_with ~suffix:"_result" (Path.last signature_path)
          in
          let mapper _path ident { Types.type_manifest; type_params; _ } =
            match type_manifest with
            | None ->
                return
                  (Some
                     (Tree.Item
                        (Ident.name ident, List.length type_params)))
            | Some manifest
              when abstract_functor_applications
                   && is_functor_application_alias manifest ->
                let is_constrained =
                  match Types.get_desc manifest with
                  | Types.Tconstr (path, _, _) -> (
                      match Env.find_type path env with
                      | { Types.type_manifest = Some _; _ } -> true
                      | { Types.type_manifest = None; _ }
                      | exception Not_found ->
                          false)
                  | _ -> false
                in
                if is_constrained then return None
                else
                  return
                    (Some
                       (Tree.Item
                          (Ident.name ident, List.length type_params)))
            | Some _ -> return None
          in
          ModuleTypParams.get_module_typ_typ_params mapper module_type)

let get_signature_type_declaration (signature_path : Path.t)
    (type_path : string list) : Types.type_declaration option Monad.t =
  let* env = get_env in
  let rec find_in_module_type visited_paths module_type type_path =
    match (module_type, type_path) with
    | Types.Mty_signature signature, [ type_name ] ->
        return
          (signature
          |> List.find_map (function
               | Types.Sig_type (ident, declaration, _, _)
                 when String.equal (Ident.name ident) type_name ->
                   Some declaration
               | _ -> None))
    | Types.Mty_signature signature, module_name :: remaining ->
        (match
           signature
           |> List.find_map (function
                | Types.Sig_module (ident, _, declaration, _, _)
                  when String.equal (Ident.name ident) module_name ->
                    Some declaration.Types.md_type
                | _ -> None)
         with
        | Some module_type ->
            find_in_module_type visited_paths module_type remaining
        | None -> return None)
    | (Types.Mty_alias path | Types.Mty_ident path), _ ->
        let path_name = Path.name path in
        if List.mem path_name visited_paths then return None
        else
          let visited_paths = path_name :: visited_paths in
          (match module_type with
          | Types.Mty_alias path -> (
              match Env.find_module path env with
              | { Types.md_type; _ } ->
                  find_in_module_type visited_paths md_type type_path
              | exception Not_found ->
                  let* hinted = get_module_type_hint path in
                  (match hinted with
                  | Some module_type ->
                      find_in_module_type visited_paths module_type type_path
                  | None -> return None))
          | Types.Mty_ident path -> (
              match Env.find_modtype path env with
              | { Types.mtd_type = Some module_type; _ } ->
                  find_in_module_type visited_paths module_type type_path
              | { Types.mtd_type = None; _ }
              | exception Not_found ->
                  let* hinted = get_module_type_hint path in
                  (match hinted with
                  | Some module_type ->
                      find_in_module_type visited_paths module_type type_path
                  | None -> return None))
          | _ -> return None)
    | Types.Mty_functor _, _
    | Types.Mty_for_hole, _
    | _, [] ->
        return None
  in
  let* module_type =
    match Env.find_modtype signature_path env with
    | { Types.mtd_type = Some module_type; _ } -> return (Some module_type)
    | { Types.mtd_type = None; _ }
    | exception Not_found ->
        get_module_type_hint signature_path
  in
  match module_type with
  | Some module_type -> find_in_module_type [] module_type type_path
  | None -> return None

let get_signature_concrete_manifest (signature_path : Path.t)
    (type_path : string list) : Types.type_expr option Monad.t =
  let* env = get_env in
  let rec local_path_components path =
    match path with
    | Path.Pident ident -> Some [ Ident.name ident ]
    | Path.Pdot (prefix, field) ->
        Option.map
          (fun prefix -> prefix @ [ field ])
          (local_path_components prefix)
    | Path.Pextra_ty (prefix, Path.Pext_ty) ->
        local_path_components prefix
    | Path.Pextra_ty (prefix, Path.Pcstr_ty field) ->
        Option.map
          (fun prefix -> prefix @ [ field ])
          (local_path_components prefix)
    | Path.Papply _ -> None
  in
  let rec resolve visited followed_declaration typ =
    match Types.get_desc typ with
    | Types.Tconstr (path, _, _) ->
        let path_name = Path.name path in
        if List.mem path_name visited then return None
        else
          let visited = path_name :: visited in
          (match Env.find_type path env with
          | { Types.type_manifest = Some manifest; _ } ->
              resolve visited true manifest
          | { Types.type_manifest = None; _ }
          | exception Not_found -> (
              match local_path_components path with
              | Some local_path ->
                  let* declaration =
                    get_signature_type_declaration signature_path local_path
                  in
                  (match declaration with
                  | Some { Types.type_manifest = Some manifest; _ } ->
                      resolve visited true manifest
                  | Some { Types.type_manifest = None; _ } ->
                      return None
                  | None ->
                      if
                        followed_declaration
                        && not (path_contains_functor_application path)
                      then return (Some typ)
                      else return None)
              | None ->
                  if
                    followed_declaration
                    && not (path_contains_functor_application path)
                  then return (Some typ)
                  else return None))
    | Types.Tlink typ
    | Types.Tsubst (typ, _)
    | Types.Tpoly (typ, _) ->
        resolve visited followed_declaration typ
    | _ ->
        if followed_declaration then return (Some typ)
        else return None
  in
  let* declaration =
    get_signature_type_declaration signature_path type_path
  in
  match declaration with
  | Some { Types.type_manifest = Some manifest; _ } ->
      resolve [] true manifest
  | Some { Types.type_manifest = None; _ }
  | None ->
      return None

let rec get_module_typ_desc_path (module_typ_desc : Typedtree.module_type_desc)
    : Path.t option =
  match module_typ_desc with
  | Tmty_ident (path, _) -> Some path
  | Tmty_signature _ -> None
  | Tmty_functor _ -> None
  | Tmty_with (module_typ, _) -> get_module_typ_path_name module_typ
  | Tmty_typeof _ -> None
  | Tmty_alias _ -> None

and get_module_typ_path_name (module_typ : Typedtree.module_type) :
    Path.t option =
  get_module_typ_desc_path module_typ.mty_desc

let of_ocaml_module_with_substitutions (signature_path : Path.t)
    (substitutions :
      (Path.t * Longident.t Asttypes.loc * Typedtree.with_constraint) list) :
    Module.t Monad.t =
  let* signature_path_name, explicit_params =
    signature_path_and_explicit_params signature_path
  in
  let* signature_typ_params =
    get_signature_typ_params_arity signature_path
  in
  substitutions
  |> Monad.List.filter_map
       (fun (_, { Asttypes.txt = long_ident; _ }, with_constraint) ->
         match with_constraint with
         | Typedtree.Twith_type typ_declaration
         | Twith_typesubst typ_declaration -> (
             let { Typedtree.typ_loc; typ_type; _ } = typ_declaration in
             match typ_type with
             | {
              type_kind = Type_abstract _;
              type_manifest = Some typ;
              type_params;
              _;
             } ->
                 set_loc typ_loc
                   ( Type.of_type_expr_without_free_vars typ >>= fun typ ->
                     Monad.List.map Type.of_type_expr_variable type_params
                     >>= fun typ_params ->
                     let path = Longident.flatten long_ident in
                     return (Some (path, typ_params, typ)) )
             | _ ->
                 raise None NotSupported
                   ("Can only do `with` on types in module types using type \
                     expressions " ^ "rather than type definitions"))
         | _ ->
             raise None NotSupported
               "Can only do `with` on types in module types")
  >>= fun (typ_substitutions : (string list * Name.t list * Type.t) list) ->
  let typ_values =
    List.fold_left
      (fun typ_values (path, typ_params, typ) ->
        Tree.map_at typ_values path (fun _ ->
            Type.Typ (Type.FunTyps (typ_params, typ))))
      (signature_typ_params |> Tree.map (fun arity -> Type.Arity arity))
      typ_substitutions
  in
  let parameter_paths =
    Tree.flatten signature_typ_params |> List.map fst
  in
  return
    (Module.With
       (signature_path_name, typ_values, parameter_paths, explicit_params))

let rec of_ocaml_desc (module_typ_desc : Typedtree.module_type_desc) : t Monad.t
    =
  match module_typ_desc with
  | Tmty_alias _ ->
      raise ([], Module.Error "alias") NotSupported
        "Aliases in module types are not handled"
  | Tmty_functor (Named (ident, _, param), result) ->
      let id = Name.string_of_optional_ident ident in
      let* params_of_param, param = of_ocaml param in
      let* params, result = of_ocaml result in
      let* param =
        match params_of_param with
        | [] -> return param
        | _ :: _ ->
            raise (Module.Error "functor_parameter") NotSupported
              ("Functors as functor parameters are not supported.\n\n"
             ^ "You can encapsulated it into a signature with this functor "
             ^ "as a field.")
      in
      return ((id, param) :: params, result)
  | Tmty_functor (Unit, _) ->
      raise
        ([], Module.Error "generative_functor")
        NotSupported "Generative functors are not handled"
  | Tmty_ident (path, _) ->
      let* modul = of_ocaml_module_with_substitutions path [] in
      return ([], modul)
  | Tmty_signature signature ->
      let* result =
        IsFirstClassModule.is_module_typ_first_class
          (Types.Mty_signature signature.sig_type)
          None
      in
      (match result with
      | IsFirstClassModule.Found signature_path ->
          let* modul =
            of_ocaml_module_with_substitutions signature_path []
          in
          return ([], modul)
      | IsFirstClassModule.Not_found reason ->
          raise
            ([], Module.Error "anonymous_signature")
            NotSupported
            ("Anonymous definition of a signature has no equivalent named \
              signature in the current OCaml environment.\n\n"
            ^ reason))
  | Tmty_typeof _ ->
      raise
        ([], Module.Error "typeof")
        NotSupported "The typeof in module types is not handled"
  | Tmty_with ({ mty_desc = Tmty_ident (path, _); _ }, substitutions) ->
      let* modul = of_ocaml_module_with_substitutions path substitutions in
      return ([], modul)
  | Tmty_with _ ->
      raise
        ([], Module.Error "signature")
        NotSupported
        "Operator 'with' on something else than a signature name is not handled"

and of_ocaml (module_typ : Typedtree.module_type) : t Monad.t =
  set_env module_typ.mty_env
    (set_loc module_typ.mty_loc (of_ocaml_desc module_typ.mty_desc))

let rec of_types ?result_signature_path
    ?(abstract_functor_applications = false) ?(parameter_types = [])
    (module_typ : Types.module_type) : t Monad.t =
  match module_typ with
  | Mty_alias path ->
      let* env = get_env in
      (match Env.find_module path env with
      | { Types.md_type; _ } ->
          of_types ?result_signature_path ~abstract_functor_applications
            ~parameter_types md_type
      | exception Not_found ->
          let* hinted_module_type = get_module_type_hint path in
          (match hinted_module_type with
          | Some hinted_module_type ->
              of_types ?result_signature_path ~abstract_functor_applications
                ~parameter_types
                hinted_module_type
          | None ->
              raise ([], Module.Error "module_alias") Unexpected
                ("The module `" ^ Path.name path
               ^ "` is not present in the current OCaml typing environment.")))
  | Mty_ident path ->
      let* modul = of_ocaml_module_with_substitutions path [] in
      return ([], modul)
  | Mty_functor (Named (ident, source_param), source_result) ->
      let id = Name.string_of_optional_ident ident in
      let parameter_type, remaining_parameter_types =
        match parameter_types with
        | parameter_type :: remaining ->
            (Some parameter_type, remaining)
        | [] -> (None, [])
      in
      let* params_of_param, param =
        match parameter_type with
        | Some parameter_type -> of_ocaml parameter_type
        | None ->
            of_types ~abstract_functor_applications source_param
      in
      let* env = get_env in
      let result_env =
        match ident with
        | Some ident ->
            Env.add_module ~arg:true ident Types.Mp_present
              source_param env
        | None -> env
      in
      let* params, result =
        set_env result_env
          (of_types ?result_signature_path ~abstract_functor_applications
             ~parameter_types:remaining_parameter_types source_result)
      in
      let* param =
        match params_of_param with
        | [] -> return param
        | _ :: _ ->
            raise (Module.Error "functor_parameter") NotSupported
              "Functors as functor parameters are not supported"
      in
      return ((id, param) :: params, result)
  | Mty_functor (Unit, _) ->
      raise
        ([], Module.Error "generative_functor")
        NotSupported "Generative functors are not handled"
  | Mty_signature signature ->
      let* result =
        match result_signature_path with
        | Some signature_path ->
            return (IsFirstClassModule.Found signature_path)
        | None ->
            IsFirstClassModule.is_module_typ_first_class
              (Types.Mty_signature signature) None
      in
      (match result with
      | IsFirstClassModule.Found signature_path ->
          let* signature_path_name =
            PathName.of_path_with_convert false signature_path
          in
          let mapper _path ident { Types.type_manifest; type_params; _ } =
            let name = Ident.name ident in
            let* arity_or_typ =
              match type_manifest with
              | None -> return (Type.Arity (List.length type_params))
              | Some manifest
                when abstract_functor_applications
                     && is_functor_application_alias manifest ->
                  return (Type.Arity (List.length type_params))
              | Some manifest ->
                  let* typ_args =
                    type_params
                    |> Monad.List.map Type.of_type_expr_variable
                  in
                  let* typ =
                    Type.of_type_expr_without_free_vars manifest
                  in
                  return (Type.Typ (Type.FunTyps (typ_args, typ)))
            in
            return (Some (Tree.Item (name, arity_or_typ)))
          in
          let* typ_values =
            ModuleTypParams.get_signature_typ_params mapper signature
          in
          let* signature_typ_params =
            get_signature_typ_params_arity signature_path
          in
          let parameter_paths =
            Tree.flatten signature_typ_params |> List.map fst
          in
          return
            ( [],
              Module.With
                (signature_path_name, typ_values, parameter_paths, []) )
      | IsFirstClassModule.Not_found reason ->
          raise
            ([], Module.Error "anonymous_signature")
            NotSupported
            ("Anonymous definition of a signature has no equivalent named \
              signature in the current OCaml environment.\n\n"
            ^ reason))
  | Mty_for_hole ->
      raise
        ([], Module.Error "mty_hole")
        NotSupported "Holes in module types are not supported"

let to_typ (functor_params : Name.t list) (module_name : string)
    (with_implicits : bool) (module_typ : t) :
    ((free_vars * (Name.t * Type.t) list * free_vars) * Type.t) Monad.t =
  let params, result = module_typ in
  let* new_functor_params =
    params |> Monad.List.map (fun (name, _) -> Name.of_string false name)
  in
  let* result_free_vars, result_typ =
    Module.to_typ
      (functor_params @ new_functor_params)
      module_name with_implicits result
  in
  let* params_free_vars, params =
    Monad.List.fold_right
      (fun (name, param) (params_free_vars, params) ->
        let* param_free_vars, param_typ = Module.to_typ [] name false param in
        let* name = Name.of_string false name in
        return (param_free_vars @ params_free_vars, (name, param_typ) :: params))
      params ([], [])
  in
  let typ =
    List.fold_right
      (fun (param_name, param_typ) typ ->
        Type.ForallModule (param_name, param_typ, typ))
      params result_typ
  in
  let typ =
    match params_free_vars with
    | [] -> typ
    | _ :: _ ->
        Type.ForallTyps
          ( params_free_vars
            |> List.map (fun { name; arity; _ } -> (name, arity)),
            typ )
  in
  return ((params_free_vars, params, result_free_vars), typ)

let to_coq_functor_parameters_modules (params_free_vars : free_vars)
    (params : (Name.t * Type.t) list) : SmartPrint.t =
  group (to_coq_grouped_free_vars params_free_vars)
  ^^ group
       (separate space
          (params
          |> List.map (fun (name, typ) ->
                 nest
                   (parens
                      (Name.to_coq name ^^ !^":" ^^ Type.to_coq None None typ)))
          ))
