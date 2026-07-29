open Monad.Notations

type 'a mapper =
  string list ->
  Ident.t ->
  Types.type_declaration ->
  'a Tree.item option Monad.t

(* We do not report user errors in this code as this would create duplicates
   with errors generated during the translation of the signatures themselves.

   Recursive modules make the module-type graph cyclic.  Track both physical
   module-type nodes and named aliases so parameter discovery visits that graph
   once instead of recursively expanding the knot. *)
let rec get_signature_typ_params_aux (mapper : 'a mapper)
    (visited_module_types : Types.module_type list)
    (visited_paths : string list) (prefix : string list)
    (signature : Types.signature) : 'a Tree.t Monad.t =
  let get_signature_item_typ_params (signature_item : Types.signature_item) :
      'a Tree.item option Monad.t =
    match signature_item with
    | Sig_value _ -> return None
    | Sig_type (ident, type_declaration, _, _) ->
        mapper prefix ident type_declaration
    | Sig_typext _ -> return None
    | Sig_module (ident, _, module_declaration, _, _) ->
        let name = Ident.name ident in
        let* configuration = get_configuration in
        let* enclosing_path = get_definition_path in
        if
          Configuration.is_definition_excluded configuration
            (enclosing_path @ prefix @ [ name ])
        then return None
        else
          get_module_typ_typ_params_aux mapper visited_module_types
            visited_paths (prefix @ [ name ]) module_declaration.md_type
          >>= fun typ_params -> return (Some (Tree.Module (name, typ_params)))
    | Sig_modtype _ | Sig_class _ | Sig_class_type _ -> return None
  in
  signature |> Monad.List.filter_map get_signature_item_typ_params

and get_module_typ_typ_params_aux (mapper : 'a mapper)
    (visited_module_types : Types.module_type list)
    (visited_paths : string list) (prefix : string list)
    (module_typ : Types.module_type) : 'a Tree.t Monad.t =
  if
    List.exists
      (fun visited_module_type -> visited_module_type == module_typ)
      visited_module_types
  then return []
  else
    let visited_module_types = module_typ :: visited_module_types in
    match module_typ with
    | Mty_signature signature ->
        get_signature_typ_params_aux mapper visited_module_types visited_paths
          prefix signature
    | Mty_alias path -> (
        let path_name = Path.name path in
        if List.mem path_name visited_paths then return []
        else
          let visited_paths = path_name :: visited_paths in
          get_env >>= fun env ->
          match Env.scrape_alias env module_typ with
          | Mty_signature _ as strengthened_module_type ->
              get_module_typ_typ_params_aux mapper visited_module_types
                visited_paths prefix strengthened_module_type
          | _ | (exception Not_found) -> (
              let* hinted_module_type = get_module_type_hint path in
              match hinted_module_type with
              | Some module_type ->
                  get_module_typ_typ_params_aux mapper visited_module_types
                    visited_paths prefix module_type
              | None -> return []))
    | Mty_ident path -> (
        let path_name = Path.name path in
        if List.mem path_name visited_paths then return []
        else
          let visited_paths = path_name :: visited_paths in
          get_env >>= fun env ->
          match Env.find_modtype path env with
          | module_typ ->
              get_module_typ_declaration_typ_params_aux mapper
                visited_module_types visited_paths prefix module_typ
          | exception Not_found -> (
              let* hinted_module_type = get_module_type_hint path in
              match hinted_module_type with
              | Some module_type ->
                  get_module_typ_typ_params_aux mapper visited_module_types
                    visited_paths prefix module_type
              | None -> return []))
    | Mty_functor _ -> return []
    | Mty_for_hole -> return []

and get_module_typ_declaration_typ_params_aux (mapper : 'a mapper)
    (visited_module_types : Types.module_type list)
    (visited_paths : string list) (prefix : string list)
    (module_typ_declaration : Types.modtype_declaration) : 'a Tree.t Monad.t =
  match module_typ_declaration.mtd_type with
  | None -> return []
  | Some module_typ ->
      get_module_typ_typ_params_aux mapper visited_module_types visited_paths
        prefix module_typ

let get_signature_typ_params (mapper : 'a mapper) (signature : Types.signature)
    : 'a Tree.t Monad.t =
  get_signature_typ_params_aux mapper [] [] [] signature

let get_module_typ_typ_params (mapper : 'a mapper)
    (module_typ : Types.module_type) : 'a Tree.t Monad.t =
  get_module_typ_typ_params_aux mapper [] [] [] module_typ

let get_module_typ_declaration_typ_params (mapper : 'a mapper)
    (module_typ_declaration : Types.modtype_declaration) : 'a Tree.t Monad.t =
  get_module_typ_declaration_typ_params_aux mapper [] [] []
    module_typ_declaration

let mapper_get_arity (_path : string list) (ident : Ident.t)
    (type_declaration : Types.type_declaration) : int Tree.item option Monad.t =
  match type_declaration.type_manifest with
  | None ->
      let arity = List.length type_declaration.type_params in
      return (Some (Tree.Item (Ident.name ident, arity)))
  | Some _ -> return None

let get_signature_typ_params_arity = get_signature_typ_params mapper_get_arity
let get_module_typ_typ_params_arity = get_module_typ_typ_params mapper_get_arity

let get_module_typ_declaration_typ_params_arity =
  get_module_typ_declaration_typ_params mapper_get_arity

(** The number of abstract types in a functor's parameters. *)
let rec get_functor_nb_free_vars_params (module_typ : Types.module_type) :
    int Monad.t =
  match module_typ with
  | Mty_functor (param, module_typ) ->
      let* param_free_vars_arities =
        match param with
        | Unit -> return []
        | Named (_, param) -> get_module_typ_typ_params_arity param
      in
      let nb_free_vars_param =
        param_free_vars_arities |> Tree.flatten |> List.length
      in
      let* nb_free_vars_module_typ =
        get_functor_nb_free_vars_params module_typ
      in
      return (nb_free_vars_param + nb_free_vars_module_typ)
  | _ -> return 0
