open SmartPrint
(** A [PathName.t], eventually followed by accesses inside first-class modules.
*)

open Monad.Notations

let path_to_string_list p =
  let open Path in
  let rec aux acc = function
    | Pident id -> Ident.name id :: acc
    | Pdot (p, str) -> aux (str :: acc) p
    | Pextra_ty (p, Pext_ty) -> aux acc p
    | Pextra_ty (p, Pcstr_ty str) -> aux (str :: acc) p
    | _ -> assert false
  in
  aux [] p

(** [Access] corresponds to projections from first-class modules. *)
type t =
  | Access of PathName.t * PathName.t list
  | AppliedAccess of PathName.t * (string * string) list * PathName.t list
  | PathName of PathName.t

(** Shortcut to introduce new local variables for example. *)
let of_name (name : Name.t) : t = PathName (PathName.of_name [] name)

let dec_name : t = PathName (Name.decode_vtag |> PathName.of_name [])
let projT1 : t = of_name (Name.of_string_raw "projT1")
let prim_proj_fst : t = PathName PathName.prim_proj_fst
let prim_proj_snd : t = PathName PathName.prim_proj_snd

let is_constr_tag : t -> bool = function
  | Access _ | AppliedAccess _ -> false
  | PathName { base; _ } -> Name.equal base Name.constr_tag

let get_pathName_base : t -> Name.t = function
  | PathName { base; _ } -> base
  | _ -> Name.Make ""

let rec resolve_included_signature_path_aliases (path : Path.t) : Path.t Monad.t
    =
  match path with
  | Pident ident -> (
      let* alias = get_included_signature_path_alias ident in
      match alias with
      | Some alias when not (Path.same alias path) ->
          resolve_included_signature_path_aliases alias
      | Some _ -> return path
      | None -> (
          let* env = get_env in
          match Env.find_module path env with
          | { Types.md_type = Mty_alias alias; _ }
            when not (Path.same alias path) ->
              resolve_included_signature_path_aliases alias
          | _ | (exception _) -> return path))
  | Pdot (parent, field) ->
      let* parent = resolve_included_signature_path_aliases parent in
      return (Path.Pdot (parent, field))
  | Papply (functor_path, argument_path) ->
      let* functor_path =
        resolve_included_signature_path_aliases functor_path
      in
      let* argument_path =
        resolve_included_signature_path_aliases argument_path
      in
      return (Path.Papply (functor_path, argument_path))
  | Pextra_ty (parent, extra) ->
      let* parent = resolve_included_signature_path_aliases parent in
      return (Path.Pextra_ty (parent, extra))

let rec get_signature_path (path : Path.t) : Path.t option Monad.t =
  let* env = get_env in
  let* is_static_local_module_alias =
    match path with
    | Path.Pident ident when not (Ident.global ident) -> (
        match (Env.find_module path env).Types.md_type with
        | Mty_alias target ->
            let rec root_and_has_field has_field = function
              | Path.Pdot (parent, _) | Path.Pextra_ty (parent, _) ->
                  root_and_has_field true parent
              | (Path.Pident _ | Path.Papply _) as root -> (root, has_field)
            in
            let root, has_field = root_and_has_field false target in
            if not has_field then return false
            else
              let* root_signature = get_signature_hint root in
              return
                (match root_signature with
                | Some root_signature ->
                    String.ends_with ~suffix:"_result"
                      (Path.last root_signature)
                | None -> false)
        | _ -> return false
        | exception _ -> return false)
    | Path.Pident _ | Path.Pdot _ | Path.Papply _ | Path.Pextra_ty _ ->
        return false
  in
  if is_static_local_module_alias then return None
  else
    let exact path =
      match Env.find_module path env with
      | module_declaration -> (
          let { Types.md_type; md_attributes; _ } = module_declaration in
          let* is_first_class =
            IsFirstClassModule.is_module_typ_first_class md_type (Some path)
          in
          match is_first_class with
          | IsFirstClassModule.Found signature_path ->
              return (Some signature_path)
          | IsFirstClassModule.Not_found _
            when List.exists
                   (fun attribute ->
                     attribute.Parsetree.attr_name.txt = "rocq_plain_module")
                   md_attributes ->
              return None
          | IsFirstClassModule.Not_found _ -> get_signature_hint path)
      | exception _ -> get_signature_hint path
    in
    let* result = exact path in
    match result with
    | Some _ -> return result
    | None -> (
        let* resolved_path = resolve_included_signature_path_aliases path in
        let* resolved_result =
          if Path.same path resolved_path then return None
          else exact resolved_path
        in
        match resolved_result with
        | Some _ -> return resolved_result
        | None -> (
            match resolved_path with
            | Path.Pdot (parent, field) -> (
                let* parent_signature = get_signature_path parent in
                match parent_signature with
                | Some parent_signature ->
                    get_result_module_field parent_signature field
                | None -> return None)
            | Path.Pident _ | Path.Papply _ | Path.Pextra_ty _ -> return None))

module SignedPath = struct
  type t = { path : Path.t; signature_path : Path.t option }

  let get (path : Path.t) : t Monad.t =
    let* signature_path = get_signature_path path in
    return { path; signature_path }
end

module RawDecomposedPath = struct
  type t = SignedPath.t * (SignedPath.t * string) list

  let rec get_rev (path : Path.t) : t Monad.t =
    let* signed_path = SignedPath.get path in
    match path with
    | Papply _ -> (
        let* alias = get_module_path_alias path in
        match alias with
        | Some alias -> get_rev alias
        | None ->
            raise (signed_path, []) Unexpected
              ("No local module binding found for applicative functor path "
             ^ Path.name path))
    | Pident ident -> (
        let* alias = get_included_path_alias ident in
        match alias with
        | Some alias -> get_rev alias
        | None -> return (signed_path, []))
    | Pdot (path', field) ->
        let* start_path, fields = get_rev path' in
        return (start_path, (signed_path, field) :: fields)
    | Pextra_ty (path', Pext_ty) -> get_rev path'
    | Pextra_ty (path', Pcstr_ty field) ->
        let* start_path, fields = get_rev path' in
        return (start_path, (signed_path, field) :: fields)
end

module DecomposedPath = struct
  type t = WithField of SignedPath.t * string * t | Final of SignedPath.t

  let rec get_of_raw_decomposed_path_rev
      (raw_decomposed_path_rev : RawDecomposedPath.t)
      (decomposed_path : SignedPath.t -> t) : t =
    let start_path, fields = raw_decomposed_path_rev in
    match fields with
    | [] -> decomposed_path start_path
    | (signed_path, field) :: fields ->
        get_of_raw_decomposed_path_rev (start_path, fields) (fun next_path ->
            WithField (next_path, field, decomposed_path signed_path))

  let get (path : Path.t) : t Monad.t =
    let* raw_decomposed_path_rev = RawDecomposedPath.get_rev path in
    return
      (get_of_raw_decomposed_path_rev raw_decomposed_path_rev (fun next_path ->
           Final next_path))
end

module FlattenedDecomposedPath = struct
  type t =
    | WithField of Path.t * Path.t * string list * t
    | Final of SignedPath.t

  let rec get (decomposed_path : DecomposedPath.t)
      (current_signed_path : (Path.t * Path.t * string list) option) : t =
    match (decomposed_path, current_signed_path) with
    | WithField ({ path; signature_path }, field, decomposed_path), None -> (
        match signature_path with
        | None -> get decomposed_path current_signed_path
        | Some signature_path ->
            let current_signed_path = Some (path, signature_path, [ field ]) in
            get decomposed_path current_signed_path)
    | ( WithField ({ path; signature_path }, field, decomposed_path),
        Some (current_path, current_signature_path, current_fields) ) -> (
        match signature_path with
        | None ->
            let current_signed_path =
              Some
                ( current_path,
                  current_signature_path,
                  current_fields @ [ field ] )
            in
            get decomposed_path current_signed_path
        | Some signature_path ->
            let current_signed_path = Some (path, signature_path, [ field ]) in
            WithField
              ( current_path,
                current_signature_path,
                current_fields,
                get decomposed_path current_signed_path ))
    | Final signed_path, None -> Final signed_path
    | ( Final signed_path,
        Some (current_path, current_signature_path, current_fields) ) ->
        WithField
          ( current_path,
            current_signature_path,
            current_fields,
            Final signed_path )
end

let rec of_path_aux (flattened_decomposed_path : FlattenedDecomposedPath.t) :
    Path.t * (Path.t * string list) list * Path.t option =
  match flattened_decomposed_path with
  | WithField (path, signature_path, fields, flattened_decomposed_path) ->
      let _, fields', _ = of_path_aux flattened_decomposed_path in
      (path, (signature_path, fields) :: fields', Some signature_path)
  | Final { path; signature_path } -> (path, [], signature_path)

(** If the module was declared in the current unbundled signature definition. *)
let is_module_path_local (path : Path.t) : bool Monad.t =
  let* env = get_env in
  (* Some paths may not exist, for example for the type of a record field in an
     algebraic type. *)
  let does_exist =
    match Env.find_module path env with _ -> true | exception _ -> false
  in
  let* env_stack = get_env_stack in
  let envs_without_path =
    env_stack
    |> List.filter (fun env ->
        match Env.find_module path env with _ -> false | exception _ -> true)
  in
  return (does_exist && List.length envs_without_path mod 2 = 1)

(** In case the base path is local, we need to make a special transformation.
    Indeed, unless if the path is a single name, this means that we access to a
    sub-module with an anonmous signature which has been flattened. *)
let rec get_local_base_path (is_value : bool) (path : Path.t) :
    PathName.t option Monad.t =
  match path with
  | Papply _ -> (
      let* alias = get_module_path_alias path in
      match alias with
      | Some alias -> get_local_base_path is_value alias
      | None ->
          raise None Unexpected
            ("No local module binding found for applicative functor path "
           ^ Path.name path))
  | Pextra_ty (path, Pext_ty) -> get_local_base_path is_value path
  | Pextra_ty _ -> return None
  | Pident _ -> return None
  | Pdot (path', _) ->
      let* is_local = is_module_path_local path' in
      if is_local then
        let name_string = String.concat "_" (path_to_string_list path) in
        let* name = Name.of_string is_value name_string in
        return (Some (PathName.of_name [] name))
      else return None

(** Replace applicative module paths with the local bindings that hold their
    translated results. An application can occur below a type or value field,
    for example [Set.Make(T).t], so aliases must be resolved recursively before
    the path is decomposed into module projections. *)
let rec resolve_module_path_aliases (path : Path.t) : Path.t Monad.t =
  let* alias = get_module_path_alias path in
  match alias with
  | Some alias -> resolve_module_path_aliases alias
  | None -> (
      match path with
      | Pident ident -> (
          let* included_alias = get_included_path_alias ident in
          match included_alias with
          | Some alias -> resolve_module_path_aliases alias
          | None -> return path)
      | Pdot (prefix, field) ->
          let* prefix = resolve_module_path_aliases prefix in
          return (Path.Pdot (prefix, field))
      | Papply (functor_path, argument_path) ->
          let* functor_path = resolve_module_path_aliases functor_path in
          let* argument_path = resolve_module_path_aliases argument_path in
          return (Path.Papply (functor_path, argument_path))
      | Pextra_ty (prefix, extra) ->
          let* prefix = resolve_module_path_aliases prefix in
          return (Path.Pextra_ty (prefix, extra)))

let rec path_has_global_head (path : Path.t) : bool =
  match path with
  | Path.Pident ident -> Ident.global ident || Ident.is_predef ident
  | Path.Pdot (prefix, _) | Path.Pextra_ty (prefix, _) ->
      path_has_global_head prefix
  | Path.Papply (functor_path, _) -> path_has_global_head functor_path

let of_included_record_alias (is_value : bool)
    ({ IncludedRecordAliasTarget.functor_path; signature_path; fields } :
      IncludedRecordAliasTarget.t) (trailing_fields : string list) : t Monad.t =
  let* functor_name = PathName.of_path_with_convert false functor_path in
  let* functor_name = PathName.to_name false functor_name in
  let include_name = Name.suffix_by_include functor_name in
  let base = PathName.of_name [] include_name in
  let* field_name = Name.of_strings is_value (fields @ trailing_fields) in
  let* field =
    PathName.of_path_and_name_with_convert signature_path field_name
  in
  return (Access (base, [ field ]))

let rec included_record_access (is_value : bool) (path : Path.t)
    (trailing_fields : string list) : t option Monad.t =
  match path with
  | Pident ident -> (
      let* alias = get_included_record_alias ident in
      match alias with
      | None -> return None
      | Some alias ->
          let* access =
            of_included_record_alias is_value alias trailing_fields
          in
          return (Some access))
  | Pdot (parent, field) ->
      included_record_access is_value parent (field :: trailing_fields)
  | Pextra_ty (parent, Pext_ty) ->
      included_record_access is_value parent trailing_fields
  | Pextra_ty (parent, Pcstr_ty field) ->
      included_record_access is_value parent (field :: trailing_fields)
  | Papply _ -> return None

(** The current environment must include the potential first-class module
    signature definition of the corresponding projection in the [path]. *)
let of_path (is_value : bool) (path : Path.t) : t Monad.t =
  let* included_access = included_record_access is_value path [] in
  match included_access with
  | Some access -> return access
  | None -> (
      let* path = resolve_module_path_aliases path in
      let* decomposed_path = DecomposedPath.get path in
      let flattened_decomposed_path =
        FlattenedDecomposedPath.get decomposed_path None
      in
      let base_path, fields, signature_path =
        of_path_aux flattened_decomposed_path
      in
      let fields = List.rev fields in
      let* local_base_path = get_local_base_path is_value base_path in
      match (fields, signature_path) with
      | [], None -> (
          match local_base_path with
          | None -> (
              let* path_name =
                PathName.of_path_without_convert is_value base_path
              in
              let* conversion =
                if path_has_global_head base_path then
                  PathName.try_convert path_name
                else return None
              in
              match conversion with
              | None -> return (PathName path_name)
              | Some path_name -> return (PathName path_name))
          | Some local_base_path -> return (PathName local_base_path))
      | _ ->
          let* base_path_name =
            match local_base_path with
            | None -> PathName.of_path_with_convert is_value base_path
            | Some local_base_path -> return local_base_path
          in
          let* fields =
            fields
            |> Monad.List.map (fun (signature_path, fields) ->
                let field = String.concat "_" fields in
                let* field_name = Name.of_string is_value field in
                PathName.of_path_and_name_with_convert signature_path field_name)
          in
          return (Access (base_path_name, List.rev fields)))

let is_native_type (path : t) : bool =
  match path with
  | Access _ | AppliedAccess _ -> false
  | PathName { base; _ } ->
      List.mem (Name.to_string base) Name.native_type_constructors

let to_string (mixed_path : t) : string =
  match mixed_path with
  | Access (path, fields) ->
      let path = PathName.to_string path in
      let fields =
        fields |> List.map (fun field -> "(" ^ PathName.to_string field ^ ")")
      in
      String.concat "." (path :: fields)
  | AppliedAccess (path, implicits, fields) ->
      let implicits =
        implicits
        |> List.map (fun (name, value) ->
            if String.equal name "" then value
            else "(" ^ name ^ " := " ^ value ^ ")")
      in
      let path =
        "(" ^ String.concat " " (PathName.to_string path :: implicits) ^ ")"
      in
      let fields =
        fields |> List.map (fun field -> "(" ^ PathName.to_string field ^ ")")
      in
      String.concat "." (path :: fields)
  | PathName path_name -> PathName.to_string path_name

let to_string_no_modules (mixed_path : t) : string =
  match mixed_path with
  | Access (path, fields) ->
      let path = PathName.to_string path in
      let fields =
        fields |> List.map (fun field -> "(" ^ PathName.to_string field ^ ")")
      in
      String.concat "." (path :: fields)
  | AppliedAccess (path, implicits, fields) ->
      to_string (AppliedAccess (path, implicits, fields))
  | PathName path_name -> PathName.to_string_base path_name

let to_coq (mixed_path : t) : SmartPrint.t = !^(to_string mixed_path)
