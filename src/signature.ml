open SmartPrint
(** An OCaml signature which will by transformed into a dependent record. *)

open Typedtree
open Monad.Notations

type item =
  | Error of string
  | Documentation of string
  | Module of Name.t * Type.t * Exp.assumption_requirement list
  | ModuleWithSignature of item list
  | TypExistential of Name.t
  | TypSynonym of Name.t * Type.t
  | Value of Name.t * Type.t * Exp.assumption_requirement list
  | ModuleWithTypeParams of Name.t * Type.t * (Name.t * int) list

type t = { items : item list; typ_params : (Name.t * int) list }

type let_in_type_target =
  | LocalConstructor of Name.t
  | ManifestConstructor of Type.t

type let_in_type = (Name.t list * let_in_type_target) list

let map_types (map : Type.t -> Type.t) (signature : t) : t =
  let map_requirements requirements =
    requirements |> List.map (fun (kind, typ) -> (kind, map typ))
  in
  let rec map_item = function
    | Module (name, typ, requirements) ->
        Module (name, map typ, map_requirements requirements)
    | ModuleWithSignature items -> ModuleWithSignature (List.map map_item items)
    | TypSynonym (name, typ) -> TypSynonym (name, map typ)
    | Value (name, typ, requirements) ->
        Value (name, map typ, map_requirements requirements)
    | ModuleWithTypeParams (name, typ, parameters) ->
        ModuleWithTypeParams (name, map typ, parameters)
    | (Error _ | Documentation _ | TypExistential _) as item -> item
  in
  { signature with items = List.map map_item signature.items }

let type_of_let_in_type_target = function
  | LocalConstructor target -> Type.Variable target
  | ManifestConstructor target -> target

(** A first-class module field fixes each named parameter of its result
    signature.  Subsequent fields should use those fixed parameters directly:
    retaining a projection such as [M.(S.t)] needlessly asks Rocq to infer the
    hidden arguments of [S], even though the enclosing dependent record already
    binds the same type as (say) [M_t]. *)
let abstract_fixed_associated_types (signature : t) (typ : Type.t) : Type.t =
  let rec abstract typ = function
    | Module
        ( module_name,
          Type.Signature (_signature_path, parameters),
          _ )
    | ModuleWithTypeParams
        ( module_name,
          Type.Signature (_signature_path, parameters),
          _ ) ->
        parameters
        |> List.fold_left
             (fun typ (parameter_name, target) ->
               match target with
               | None -> typ
               | Some target ->
                   Type.subst_constructor_definition
                     [ module_name; parameter_name ] target typ)
             typ
    | ModuleWithSignature items -> List.fold_left abstract typ items
    | Error _ | Documentation _ | Module _ | ModuleWithTypeParams _
    | TypExistential _ | TypSynonym _ | Value _ ->
        typ
  in
  List.fold_left abstract typ signature.items

(** Inferred requirements may arrive after a result signature was synthesized.
    Rebase qualified implementation paths such as [F.Make.Host.t] onto the
    flattened dependent-record parameter [Host_t]. *)
let abstract_owned_result_types (signature : t) (typ : Type.t) : Type.t =
  let rec add_manifest_names names = function
    | TypSynonym (name, _) | ModuleWithTypeParams (name, _, _) ->
        Name.Set.add name names
    | ModuleWithSignature items -> List.fold_left add_manifest_names names items
    | Error _ | Documentation _ | Module _ | TypExistential _ | Value _ -> names
  in
  let owned =
    signature.typ_params
    |> List.fold_left
         (fun names (name, _) ->
           Name.Set.add name names)
         (List.fold_left add_manifest_names Name.Set.empty signature.items)
    |> Name.Set.filter (fun name ->
        String.contains (Name.to_string name) '_')
  in
  Type.project_type_names ~unqualified:false
    (fun name ->
      if Name.Set.mem name owned then Some (MixedPath.of_name name) else None)
    typ

let add_assumption_requirements (specs : Exp.assumption_call_specs)
    (signature : t) : t =
  let rec call_type_correspondences items =
    items
    |> List.concat_map (function
      | Value (name, typ, _) | Module (name, typ, _) -> (
          match
            Exp.assumption_call_spec_for_field specs
              { PathName.path = []; base = name }
          with
          | Some spec -> [ (spec.Exp.call_typ, typ) ]
          | None -> [])
      | ModuleWithSignature items -> call_type_correspondences items
      | _ -> [])
  in
  let call_type_correspondences = call_type_correspondences signature.items in
  let normalize_requirement_type typ =
    typ |> abstract_fixed_associated_types signature
    |> abstract_owned_result_types signature
  in
  let requirements_for name typ existing_requirements =
    match
      Exp.assumption_call_spec_for_field specs
        { PathName.path = []; base = name }
    with
    | None ->
        existing_requirements
        |> List.map (fun (kind, typ) ->
            (kind, normalize_requirement_type typ))
    | Some
        {
          Exp.call_typ = declared_call;
          projected_types = _;
          Exp.result_typ = declared_result;
          requirements = inferred_requirements;
        } ->
        (if inferred_requirements = [] then existing_requirements
         else inferred_requirements)
        |> Exp.order_assumption_binders_with_specs specs
        |> List.map (fun (kind, required_typ) ->
            let specialize declared actual typ =
              match
                Type.specialize_matched_type ~relaxed_constructors:true
                  ~preserve_pattern_constructor:(fun _ -> false)
                  declared actual typ
              with
              | Some specialized when compare specialized typ <> 0 ->
                  Some specialized
              | Some _ | None -> None
            in
            let specialized =
              match specialize declared_call typ required_typ with
              | Some specialized -> specialized
              | None -> (
                  match
                    List.find_map
                      (fun (declared, actual) ->
                        specialize declared actual required_typ)
                      call_type_correspondences
                  with
                  | Some specialized -> specialized
                  | None ->
                      if compare required_typ declared_result = 0 then
                        Type.arrow_result typ
                      else required_typ)
            in
            (kind, normalize_requirement_type specialized))
  in
  let rec add_to_item = function
    | Value (name, typ, existing_requirements) ->
        Value (name, typ, requirements_for name typ existing_requirements)
    | Module (name, typ, existing_requirements) ->
        Module (name, typ, requirements_for name typ existing_requirements)
    | ModuleWithSignature items ->
        ModuleWithSignature (List.map add_to_item items)
    | item -> item
  in
  { signature with items = List.map add_to_item signature.items }

let is_generated_record_operation (name : Name.t) : bool =
  let text = Name.to_string name in
  let marker = "__rocq_record_" in
  let marker_length = String.length marker in
  let rec search offset =
    if offset + marker_length > String.length text then false
    else if String.sub text offset marker_length = marker then true
    else search (offset + 1)
  in
  search 0

(** Type parameters of a generated dependent record can themselves depend on
    translated assumptions.  Record fields whose types mention such a
    parameter must quantify over the same assumptions, even when their value
    expressions are total. *)
let contextual_typ_params (signature : t) :
    Exp.assumption_requirement list Name.Map.t =
  let rec uses parameter = function
    | Module (_, typ, requirements) ->
        if Type.uses_local_type_parameter parameter typ then [ requirements ]
        else []
    | ModuleWithSignature items -> List.concat_map (uses parameter) items
    | Error _ | Documentation _ | TypExistential _ | TypSynonym _ | Value _
    | ModuleWithTypeParams _ ->
        []
  in
  let common_requirements = function
    | [] -> None
    | first :: remaining ->
        let common =
          List.fold_left
            (fun candidates requirements ->
              List.filter
                (fun candidate ->
                  List.exists
                    (fun requirement ->
                      Exp.compare_assumption_requirement candidate requirement
                      = 0)
                    requirements)
                candidates)
            first remaining
          |> Exp.sort_uniq_assumptions
        in
        if common = [] then None else Some common
  in
  signature.typ_params
  |> List.fold_left
       (fun contextual (parameter, _) ->
         match
           common_requirements
             (List.concat_map (uses parameter) signature.items)
         with
         | Some requirements -> Name.Map.add parameter requirements contextual
         | None -> contextual)
       Name.Map.empty

let add_contextual_item_requirements contextual typ requirements =
  Name.Map.fold
    (fun parameter contexts requirements ->
      if not (Type.uses_local_type_parameter parameter typ) then requirements
      else
        List.fold_left
          (fun requirements context ->
            if
              List.exists
                (fun requirement ->
                  Exp.compare_assumption_requirement requirement context = 0)
                requirements
            then requirements
            else requirements @ [ context ])
          requirements contexts)
    contextual requirements

(** Persist contextual requirements before module-field arities are computed.
    Adding them only in [to_coq_item] makes a field declaration quantify over
    assumptions while its generated record assignment omits the corresponding
    lambdas. *)
let materialize_contextual_requirements (signature : t) : t =
  let contextual = contextual_typ_params signature in
  let rec materialize = function
    | Value (name, typ, requirements) ->
        Value
          ( name,
            typ,
            add_contextual_item_requirements contextual typ requirements )
    | Module (name, typ, requirements) ->
        Module
          ( name,
            typ,
            add_contextual_item_requirements contextual typ requirements )
    | ModuleWithSignature items ->
        ModuleWithSignature (List.map materialize items)
    | item -> item
  in
  { signature with items = List.map materialize signature.items }

(** Set requirements observed on concrete generated record fields. The field
    expressions have already gone through call-requirement propagation and type
    specialization, so these requirements are authoritative for matching fields
    in a synthesized functor-result signature.  Record constructors and
    projections execute no source operation; type dependencies for them are
    reconstructed later from their normalized field types. *)
let add_field_assumption_requirements
    (requirements : Exp.assumption_requirement list Name.Map.t) (signature : t)
    : t =
  let rec add_to_item = function
    | Value (name, typ, existing_requirements) ->
        Value
          ( name,
            typ,
            if is_generated_record_operation name then []
            else
              Name.Map.find_opt name requirements
              |> Option.value ~default:existing_requirements )
    | Module (name, typ, existing_requirements) ->
        Module
          ( name,
            typ,
            Name.Map.find_opt name requirements
            |> Option.value ~default:existing_requirements )
    | ModuleWithSignature items ->
        ModuleWithSignature (List.map add_to_item items)
    | item -> item
  in
  { signature with items = List.map add_to_item signature.items }
  |> materialize_contextual_requirements

let field_assumption_requirements (signature : t) :
    Exp.assumption_requirement list Name.Map.t =
  let rec collect requirements = function
    | Value (name, _, required) | Module (name, _, required) ->
        Name.Map.add name required requirements
    | ModuleWithSignature items -> List.fold_left collect requirements items
    | Error _ | Documentation _ | TypExistential _ | TypSynonym _
    | ModuleWithTypeParams _ ->
        requirements
  in
  List.fold_left collect Name.Map.empty signature.items

let rec is_self_manifest name = function
  | Type.Variable target -> Name.equal name target
  | Type.Apply (MixedPath.PathName { PathName.path = []; base = target }, []) ->
      Name.equal name target
  | Type.FunTyps ([], body) -> is_self_manifest name body
  | _ -> false

let manifest_types (signature : t) =
  let rec manifest_types manifests = function
    | (TypSynonym (name, typ) | ModuleWithTypeParams (name, typ, _))
      when not (is_self_manifest name typ) ->
        (name, typ) :: manifests
    | ModuleWithSignature items -> List.fold_left manifest_types manifests items
    | Error _ | Documentation _ | Module _ | Value _ | TypExistential _
    | TypSynonym _ | ModuleWithTypeParams _ ->
        manifests
  in
  List.fold_left manifest_types [] signature.items

let normalize_manifest_type (signature : t) (typ : Type.t) : Type.t =
  let manifests = manifest_types signature in
  let substitute_manifest_once typ =
    List.fold_left
      (fun typ (name, manifest) ->
        typ
        |> Type.rewrite_exact_subtypes (Type.Variable name) manifest
        |> Type.rewrite_exact_subtypes
             (Type.Apply (MixedPath.of_name name, []))
             manifest)
      typ manifests
  in
  let substitute_manifests typ =
    let rec close remaining typ =
      if remaining = 0 then typ
      else
        let updated = substitute_manifest_once typ in
        if compare typ updated = 0 then typ else close (remaining - 1) updated
    in
    close (List.length manifests) typ
  in
  substitute_manifests typ

let normalize_manifest_requirements (signature : t)
    (requirements : Exp.assumption_requirement list) :
    Exp.assumption_requirement list =
  let requirements =
    requirements
    |> List.map (fun (kind, typ) ->
        ( kind,
          typ |> abstract_fixed_associated_types signature
          |> abstract_owned_result_types signature
          |> normalize_manifest_type signature ))
    |> Exp.stable_uniq_assumptions
  in
  let rendered_type typ =
    typ |> Type.to_coq None None |> SmartPrint.to_string 1_000_000 0
  in
  (* OCaml aliases can leave a local type represented either as a variable or
     as a nullary constructor. Both generate the same Rocq binder type. *)
  List.fold_left
    (fun unique ((kind, typ) as requirement) ->
      if
        List.exists
          (fun (other_kind, other_typ) ->
            kind = other_kind
            && String.equal (rendered_type typ) (rendered_type other_typ))
          unique
      then unique
      else unique @ [ requirement ])
    [] requirements

let assumption_call_specs (signature : t) : Exp.assumption_call_specs =
  let add_projected_type source target projected =
    if Name.Map.mem source projected then projected
    else Name.Map.add source target projected
  in
  let rec abstract_types abstract = function
    | TypExistential name -> Name.Set.add name abstract
    | (TypSynonym (name, typ) | ModuleWithTypeParams (name, typ, _))
      when is_self_manifest name typ ->
        Name.Set.add name abstract
    | ModuleWithSignature items -> List.fold_left abstract_types abstract items
    | Error _ | Documentation _ | Module _ | Value _ | TypSynonym _
    | ModuleWithTypeParams _ ->
        abstract
  in
  let abstract_types =
    List.fold_left abstract_types Name.Set.empty signature.items
  in
  let manifests = manifest_types signature in
  let rec is_alias_manifest = function
    | Type.Variable _
    | Type.Apply (_, []) ->
        true
    | Type.FunTyps ([], body) -> is_alias_manifest body
    | _ -> false
  in
  let abstract_manifest_types typ =
    manifests
    |> List.fold_left
         (fun typ (name, manifest) ->
           let normalized_manifest =
             normalize_manifest_type signature manifest
           in
           if
             is_alias_manifest normalized_manifest
             && not (is_self_manifest name normalized_manifest)
           then
             typ
             |> Type.rewrite_exact_subtypes manifest (Type.Variable name)
             |> Type.rewrite_exact_subtypes normalized_manifest
                  (Type.Variable name)
           else typ)
         typ
  in
  let rec direct_type_name = function
    | Type.Variable name -> Some (name, true)
    | Type.Apply (MixedPath.PathName { PathName.path = []; base = name }, []) ->
        Some (name, false)
    | Type.FunTyps ([], body) -> direct_type_name body
    | _ -> None
  in
  let add_public_alias source target projected =
    match Name.Map.find_opt source projected with
    | None -> Name.Map.add source target projected
    | Some current when Name.equal current source ->
        Name.Map.add source target projected
    | Some _ -> projected
  in
  let rec projected_aliases projected = function
    | TypSynonym (name, typ) | ModuleWithTypeParams (name, typ, _) -> (
        match direct_type_name typ with
        | Some (source, is_free_variable)
          when is_free_variable || Name.Set.mem source abstract_types ->
            projected
            |> add_projected_type name name
            |> add_public_alias source name
        | Some _ | None -> projected)
    | ModuleWithSignature items ->
        List.fold_left projected_aliases projected items
    | Error _ | Documentation _ | Module _ | Value _ | TypExistential _ ->
        projected
  in
  let projected_types =
    Name.Set.fold
      (fun name -> add_projected_type name name)
      abstract_types Name.Map.empty
    |> fun projected ->
    List.fold_left projected_aliases projected signature.items
    |> fun projected ->
    List.fold_left
      (fun projected (name, _) -> add_projected_type name name projected)
      projected manifests
  in
  let rec add_projected_modules projected = function
    | Module (name, _, _) -> add_projected_type name name projected
    | ModuleWithSignature items ->
        List.fold_left add_projected_modules projected items
    | Error _ | Documentation _ | Value _ | TypExistential _ | TypSynonym _
    | ModuleWithTypeParams _ ->
        projected
  in
  let projected_types =
    List.fold_left add_projected_modules projected_types signature.items
  in
  let rec collect specs = function
    | Value (name, typ, requirements) | Module (name, typ, requirements) ->
        let typ =
          normalize_manifest_type signature typ |> abstract_manifest_types
        in
        let requirements =
          normalize_manifest_requirements signature requirements
          |> List.map (fun (kind, typ) ->
              (kind, abstract_manifest_types typ))
        in
        Name.Map.add name
          {
            Exp.call_typ = typ;
            projected_types;
            Exp.result_typ = Type.arrow_result typ;
            requirements;
          }
          specs
    | ModuleWithSignature items -> List.fold_left collect specs items
    | _ -> specs
  in
  List.fold_left collect Name.Map.empty signature.items

let partial_value_requirements (prefix : string list) (name : string)
    (typ : Type.t) : Exp.assumption_requirement list =
  let path = String.concat "." (prefix @ [ name ]) in
  if Exp.is_partial_operation_name path then
    [ (Exp.Unreachable, Type.arrow_result typ) ]
  else if path = "Map.of_yojson" || Exp.string_ends_with path ".Map.of_yojson"
  then
    let rec first_type_parameter = function
      | Type.ForallTyps ((parameter, _) :: _, _) ->
          Some (Type.Variable parameter)
      | Type.ForallTyps ([], body) -> first_type_parameter body
      | _ -> None
    in
    Option.to_list
      (Option.map
         (fun element -> (Exp.Unreachable, element))
         (first_type_parameter typ))
    @ [ (Exp.Unreachable, Type.arrow_result typ) ]
    |> Exp.sort_uniq_assumptions
  else []

let rec type_is_self_reference (name : Name.t) (typ : Type.t) : bool =
  match typ with
  | Type.Variable target -> Name.equal name target
  | Type.FunTyps ([], typ) -> type_is_self_reference name typ
  | _ -> false

let target_is_self_reference (name : Name.t) (target : let_in_type_target) :
    bool =
  match target with
  | LocalConstructor target -> Name.equal name target
  | ManifestConstructor typ -> type_is_self_reference name typ

let rec path_suffixes = function
  | [] -> []
  | _ :: rest as path -> path :: path_suffixes rest

let names_equal (left : Name.t list) (right : Name.t list) : bool =
  List.length left = List.length right && List.for_all2 Name.equal left right

let find_let_in_type_target (source : Name.t list) (let_in_type : let_in_type) :
    let_in_type_target option =
  let_in_type
  |> List.find_map (fun (alias_source, target) ->
      if names_equal source alias_source then Some target else None)

let remove_path_prefix (prefix : Name.t list) (path : Name.t list) :
    Name.t list option =
  let rec remove prefix path =
    match (prefix, path) with
    | [], path -> Some path
    | prefix_name :: prefix, path_name :: path
      when Name.equal prefix_name path_name ->
        remove prefix path
    | _ -> None
  in
  remove prefix path

let local_type_aliases (prefix : string list) (id : Ident.t)
    (target : let_in_type_target) : let_in_type Monad.t =
  let* source =
    prefix @ [ Ident.name id ] |> Monad.List.map (Name.of_string false)
  in
  return (source |> path_suffixes |> List.map (fun source -> (source, target)))

let rec path_contains_functor_application (path : Path.t) : bool =
  match path with
  | Papply _ -> true
  | Pdot (path, _) | Pextra_ty (path, _) ->
      path_contains_functor_application path
  | Pident _ -> false

let path_suffix_after_functor_application (path : Path.t) : string list option =
  let rec collect path suffix =
    match path with
    | Path.Pdot (path, field) -> collect path (field :: suffix)
    | Path.Pextra_ty (path, Path.Pext_ty) -> collect path suffix
    | Path.Pextra_ty (path, Path.Pcstr_ty field) ->
        collect path (field :: suffix)
    | Path.Papply _ -> Some suffix
    | Path.Pident _ -> None
  in
  collect path []

let rec path_components_without_application (path : Path.t) : string list option
    =
  match path with
  | Path.Pident ident -> Some [ Ident.name ident ]
  | Path.Pdot (prefix, field) ->
      Option.map
        (fun prefix -> prefix @ [ field ])
        (path_components_without_application prefix)
  | Path.Pextra_ty (prefix, Path.Pext_ty) ->
      path_components_without_application prefix
  | Path.Pextra_ty (prefix, Path.Pcstr_ty field) ->
      Option.map
        (fun prefix -> prefix @ [ field ])
        (path_components_without_application prefix)
  | Path.Papply _ -> None

let normalize_type_path (env : Env.t) (path : Path.t) : Path.t =
  try
    match path with
    | Path.Pdot (module_path, field) ->
        Path.Pdot (Env.normalize_module_path None env module_path, field)
    | _ -> Env.normalize_type_path None env path
  with _ -> path

let rec is_functor_application_alias_aux (env : Env.t) (visited : Path.t list)
    (typ : Types.type_expr) : bool =
  match Types.get_desc typ with
  | Tconstr (path, _, _) -> (
      path_contains_functor_application path
      || path_contains_functor_application (normalize_type_path env path)
      ||
      if List.exists (Path.same path) visited then false
      else
        match Env.find_type path env with
        | { Types.type_manifest = Some manifest; _ } ->
            is_functor_application_alias_aux env (path :: visited) manifest
        | { Types.type_manifest = None; _ } | (exception Not_found) -> false)
  | Tlink typ | Tsubst (typ, _) | Tpoly (typ, _) ->
      is_functor_application_alias_aux env visited typ
  | _ -> false

let is_functor_application_alias (env : Env.t) (typ : Types.type_expr) : bool =
  is_functor_application_alias_aux env [] typ

let concrete_manifest_declaration (env : Env.t) (typ : Types.type_expr) :
    Types.type_expr option =
  let rec resolve visited followed_declaration typ =
    match Types.get_desc typ with
    | Tconstr (path, arguments, _) -> (
        if List.exists (Path.same path) visited then None
        else
          match Env.find_type path env with
          | {
           Types.type_manifest = Some manifest;
           type_params = parameters;
           _;
          } ->
              let manifest =
                try Ctype.apply env parameters manifest arguments
                with Ctype.Cannot_apply -> manifest
              in
              resolve (path :: visited) true manifest
          | { Types.type_manifest = None; _ } | (exception Not_found) ->
              if followed_declaration then Some typ else None)
    | Tlink typ | Tsubst (typ, _) | Tpoly (typ, _) ->
        resolve visited followed_declaration typ
    | _ -> if followed_declaration then Some typ else None
  in
  resolve [] false typ

let applicative_manifest_declaration (env : Env.t) (typ : Types.type_expr) :
    Types.type_expr option =
  if is_functor_application_alias env typ then
    concrete_manifest_declaration env typ
  else None

let add_new_let_in_type (prefix : string list) (let_in_type : let_in_type)
    (id : Ident.t) : (Name.t * let_in_type) Monad.t =
  let* name = Name.of_ident false id in
  let* prefixed_name = Name.of_strings false (prefix @ [ Ident.name id ]) in
  let* qualified_source =
    prefix |> Monad.List.map (fun component -> Name.of_string false component)
  in
  let aliases =
    qualified_source @ [ name ]
    |> path_suffixes
    |> List.map (fun source -> (source, LocalConstructor prefixed_name))
  in
  return (prefixed_name, aliases @ let_in_type)

let propagate_module_alias (prefix : string list) (ident : Ident.t)
    (target_path : Path.t) (let_in_type : let_in_type) : let_in_type Monad.t =
  if path_contains_functor_application target_path then return let_in_type
  else
    let* { PathName.path; base } =
      PathName.of_path_without_convert false target_path
    in
    let target_prefix = path @ [ base ] in
    let* local_prefix =
      prefix @ [ Ident.name ident ] |> Monad.List.map (Name.of_string false)
    in
    let propagated =
      let_in_type
      |> List.concat_map (fun (source, target) ->
          match remove_path_prefix target_prefix source with
          | Some (_ :: _ as suffix) ->
              local_prefix @ suffix |> path_suffixes
              |> List.filter (fun source ->
                  List.length source > List.length suffix)
              |> List.map (fun source -> (source, target))
          | Some [] | None -> [])
    in
    return (propagated @ let_in_type)

let direct_manifest_alias ?(scope = []) (let_in_type : let_in_type)
    (typ : Types.type_expr) : Type.t option Monad.t =
  match Types.get_desc typ with
  | Tconstr (path, [], _) when not (path_contains_functor_application path) ->
      let* { PathName.path; base } =
        PathName.of_path_without_convert false path
      in
      let* scope = scope |> Monad.List.map (Name.of_string false) in
      let source = path @ [ base ] in
      let candidates =
        if scope = [] then [ source ] else [ scope @ source; source ]
      in
      return
        (candidates
        |> List.find_map (fun source ->
            find_let_in_type_target source let_in_type)
        |> Option.map type_of_let_in_type_target)
  | _ -> return None

let manifest_alias_by_suffix (prefix : string list) (let_in_type : let_in_type)
    (typ : Types.type_expr) : let_in_type_target option Monad.t =
  match Types.get_desc typ with
  | Tconstr (path, [], _) -> (
      let components, follows_functor_application =
        match path_suffix_after_functor_application path with
        | Some (_ :: _ as suffix) -> (Some suffix, true)
        | Some [] -> (None, true)
        | None -> (path_components_without_application path, false)
      in
      match components with
      | Some (_ :: _ as components) ->
          let* components =
            components |> Monad.List.map (Name.of_string false)
          in
          let suffixes =
            path_suffixes components
            |> List.filter (fun suffix -> List.length suffix > 1)
          in
          let rec prefix_ancestors = function
            | [] -> [ [] ]
            | prefix ->
                prefix
                :: prefix_ancestors (List.rev prefix |> List.tl |> List.rev)
          in
          let* prefix = prefix |> Monad.List.map (Name.of_string false) in
          let may_reference_enclosing_representation =
            (not follows_functor_application)
            && suffixes
               |> List.exists (function
                 | first :: _ -> String.equal (Name.to_string first) "Impl"
                 | [] -> false)
          in
          let prefixes =
            if may_reference_enclosing_representation then
              prefix_ancestors prefix
            else [ prefix ]
          in
          let candidates =
            prefixes
            |> List.concat_map (fun prefix ->
                suffixes |> List.map (fun suffix -> prefix @ suffix))
          in
          let target =
            candidates
            |> List.find_map (fun source ->
                find_let_in_type_target source let_in_type)
          in
          return target
      | Some [] | None -> return None)
  | _ -> return None

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
  let* typ, _, _ = Type.of_typ_expr ~expand_aliases true Name.Map.empty typ in
  let typ_args =
    Type.typ_args_of_typ typ |> Name.Set.elements
    |> List.map (fun typ -> (typ, 0))
  in
  return (Type.ForallTyps (typ_args, typ))

(** Translate a record field in the scope of the record's type parameters.
    Translating the field as an independent value would quantify those
    parameters inside the field type and leave the surrounding [t a]
    occurrence unbound. *)
let record_field_type (parameters : Name.t list) (typ : Types.type_expr) :
    Type.t Monad.t =
  let variables =
    parameters
    |> List.fold_left
         (fun variables parameter ->
           Name.Map.add parameter parameter variables)
         Name.Map.empty
  in
  let* typ, _, _ = Type.of_typ_expr true variables typ in
  return typ

let quantify_record_operation (parameters : (Name.t * int) list)
    (typ : Type.t) : Type.t =
  match parameters with [] -> typ | _ :: _ -> Type.ForallTyps (parameters, typ)

type constructor_alias = Name.t list * MixedPath.t

let mixed_path_of_dotted_name (name : string) : MixedPath.t =
  match List.rev (String.split_on_char '.' name) with
  | [] -> failwith "empty configured Rocq type-constructor path"
  | base :: path -> MixedPath.PathName (PathName.__make (List.rev path) base)

let configured_type_constructor (configuration : Configuration.t)
    (prefix : string list) (ident : Ident.t) : MixedPath.t option =
  Configuration.is_in_renaming_type_constructor configuration
    (String.concat "." (prefix @ [ Ident.name ident ]))
  |> Option.map mixed_path_of_dotted_name

let configured_manifest_rewrites (configuration : Configuration.t)
    (prefix : string list) (signature : Types.signature) :
    (Type.t * Type.t) list Monad.t =
  let* configured_aliases =
    signature
    |> Monad.List.filter_map (function
      | Types.Sig_type (ident, _, _, _) -> (
          match configured_type_constructor configuration prefix ident with
          | None -> return None
          | Some target ->
              let* source = Name.of_ident false ident in
              return (Some ([ source ], target)))
      | _ -> return None)
  in
  signature
  |> Monad.List.filter_map (function
    | Types.Sig_type
        (ident, { type_manifest = Some manifest; type_params; _ }, _, _) -> (
        match configured_type_constructor configuration prefix ident with
        | None -> return None
        | Some target ->
            let* parameters =
              Monad.List.map Type.of_type_expr_variable type_params
            in
            let* manifest = Type.fully_expand_aliases manifest in
            let* pattern = Type.of_type_expr_without_free_vars manifest in
            let pattern =
              configured_aliases
              |> List.fold_left
                   (fun pattern (source, target) ->
                     Type.subst_constructor_path source target pattern)
                   pattern
            in
            let replacement =
              Type.Apply
                ( target,
                  List.map
                    (fun parameter -> (Type.Variable parameter, false))
                    parameters )
            in
            return (Some (pattern, replacement)))
    | _ -> return None)

let rewrite_configured_manifests (prefix : string list)
    (signature : Types.signature) (typ : Type.t) : Type.t Monad.t =
  let* configuration = get_configuration in
  let* rewrites = configured_manifest_rewrites configuration prefix signature in
  return
    (rewrites
    |> List.fold_left
         (fun typ (pattern, replacement) ->
           Type.rewrite_matching_subtypes pattern replacement typ)
         typ)

let constructor_aliases_of_signature ?(abstract_functor_applications = false)
    ~(prefix : string list) (signature : Types.signature) :
    constructor_alias list Monad.t =
  let* env = get_env in
  let* configuration = get_configuration in
  signature
  |> Monad.List.filter_map (function
    | Types.Sig_type
        (ident, { type_manifest = Some manifest; type_params; _ }, _, _) -> (
        let* source = Name.of_ident false ident in
        match configured_type_constructor configuration prefix ident with
        | Some target -> return (Some ([ source ], target))
        | None
          when abstract_functor_applications
               && is_functor_application_alias env manifest ->
            return None
        | None -> (
            let* parameters =
              Monad.List.map Type.of_type_expr_variable type_params
            in
            let* target = Type.of_type_expr_without_free_vars manifest in
            let target =
              match parameters with
              | [] -> target
              | _ :: _ -> Type.FunTyps (parameters, target)
            in
            match Type.direct_constructor_path target with
            | Some target
              when MixedPath.to_string target <> Name.to_string source ->
                return (Some ([ source ], target))
            | _ -> return None))
    | _ -> return None)

let apply_constructor_aliases (aliases : constructor_alias list) (typ : Type.t)
    : Type.t =
  List.fold_left
    (fun typ (source, target) -> Type.subst_constructor_path source target typ)
    typ aliases

let record_operation_name (is_constructor : bool) (prefix : string list)
    (type_name : string) (field_name : string option) : Name.t Monad.t =
  let operation =
    if is_constructor then "_rocq_record_make"
    else "_rocq_record_get_" ^ Option.get field_name
  in
  Name.of_strings true (prefix @ [ type_name; operation ])

let rec items_of_types_signature ?(abstract_functor_applications = false)
    ?(expand_aliases = false) ?signature_path ?partial_monad_manifest
    ?operation_prefix (prefix : string list) (let_in_type : let_in_type)
    (signature : Types.signature) : (item list * let_in_type) Monad.t =
  let* env = get_env in
  let* configuration = get_configuration in
  let operation_prefix = Option.value operation_prefix ~default:prefix in
  let has_configured_type_manifest =
    signature
    |> List.exists (function
      | Types.Sig_type (ident, { type_manifest = Some _; _ }, _, _) ->
          Option.is_some
            (configured_type_constructor configuration prefix ident)
      | _ -> false)
  in
  let* manifest_rewrites =
    configured_manifest_rewrites configuration prefix signature
  in
  let apply_configured_manifest_rewrites typ =
    manifest_rewrites
    |> List.fold_left
         (fun typ (pattern, replacement) ->
           Type.rewrite_matching_subtypes pattern replacement typ)
         typ
  in
  let* constructor_aliases =
    constructor_aliases_of_signature ~abstract_functor_applications ~prefix
      signature
  in
  let concrete_result_manifest type_path =
    match signature_path with
    | Some signature_path ->
        ModuleTyp.get_signature_concrete_manifest signature_path type_path
    | None -> return None
  in
  let find_partial_monad_manifest () : Type.t option Monad.t =
    let has_monad_operations =
      signature
      |> List.exists (function
        | Types.Sig_value (ident, _, _) ->
            let name = Ident.name ident in
            name = ">>=" || name = "op_gtgteq" || name = "bind" || name = "let$"
        | _ -> false)
    in
    if not has_monad_operations then return None
    else
      match
        signature
        |> List.find_opt (function
          | Types.Sig_type (ident, { type_manifest = Some _; _ }, _, _)
            when String.equal (Ident.name ident) "t" ->
              true
          | _ -> false)
      with
      | Some
          (Types.Sig_type
             (_, { type_manifest = Some manifest; type_params; _ }, _, _)) ->
          let* parameters =
            type_params |> Monad.List.map Type.of_type_expr_variable
          in
          let* body = Type.of_type_expr_without_free_vars manifest in
          let manifest =
            Type.FunTyps (parameters, body)
            |> apply_constructor_aliases constructor_aliases
            |> apply_let_in_type let_in_type
          in
          return (Some manifest)
      | Some _ | None -> return None
  in
  let* effective_partial_monad_manifest =
    let* local_manifest = find_partial_monad_manifest () in
    match local_manifest with
    | Some _ as manifest -> return manifest
    | None -> return partial_monad_manifest
  in
  let of_types_signature_item (signature_item : Types.signature_item) :
      (item * let_in_type) Monad.t =
    match signature_item with
    | Sig_value (ident, { val_type; _ }, _) ->
        let* prefixed_name =
          Name.of_strings true (prefix @ [ Ident.name ident ])
        in
        let* configuration = get_configuration in
        let is_partial =
          Configuration.has_recursion_strategy_suffix configuration
            (prefix @ [ Ident.name ident ])
            Configuration.RecursionStrategy.Partial
        in
        let partial_arity =
          Configuration.recursion_strategy_arity_suffix configuration
            (prefix @ [ Ident.name ident ])
            Configuration.RecursionStrategy.Partial
        in
        let* typ =
          quantified_value_type
            ~expand_aliases:
              (expand_aliases
              && (not has_configured_type_manifest)
              && not is_partial)
            val_type
        in
        let typ =
          typ
          |> apply_constructor_aliases constructor_aliases
          |> apply_configured_manifest_rewrites
        in
        let typ_with_let_in_type = apply_let_in_type let_in_type typ in
        let typ_with_let_in_type =
          let introduced_variables =
            Name.Set.diff
              (Type.typ_args_of_typ typ_with_let_in_type)
              (Type.typ_args_of_typ typ)
          in
          let local_constructors =
            let_in_type
            |> List.fold_left
                 (fun names (_, target) ->
                   match target with
                   | LocalConstructor name -> Name.Set.add name names
                   | ManifestConstructor _ -> names)
                 Name.Set.empty
          in
          if Name.Set.subset introduced_variables local_constructors then
            typ_with_let_in_type
          else typ
        in
        let* typ_with_let_in_type =
          if is_partial then
            return
              (match effective_partial_monad_manifest with
              | Some manifest -> (
                  match
                    Type.partialize_with_manifest ?arity:partial_arity manifest
                      typ_with_let_in_type
                  with
                  | Some typ -> typ
                  | None -> Type.partialize typ_with_let_in_type)
              | None -> Type.partialize typ_with_let_in_type)
          else return typ_with_let_in_type
        in
        let requirements =
          partial_value_requirements operation_prefix (Ident.name ident)
            typ_with_let_in_type
        in
        return
          ( Value (prefixed_name, typ_with_let_in_type, requirements),
            let_in_type )
    | Sig_type
        ( ident,
          { type_manifest = None; type_params; type_kind; _ },
          _,
          _ ) ->
        let* name, let_in_type = add_new_let_in_type prefix let_in_type ident in
        (match type_kind with
        | Type_record (labels, _) ->
            let* typ_args =
              type_params |> Monad.List.map Type.of_type_expr_variable
            in
            let record_type =
              match typ_args with
              | [] -> Type.Variable name
              | arguments ->
                  Type.Apply
                    ( MixedPath.of_name name,
                      List.map
                        (fun argument -> (Type.Variable argument, false))
                        arguments )
            in
            let* fields =
              labels
              |> Monad.List.map (fun ({ Types.ld_id; ld_type; _ } :
                                      Types.label_declaration) ->
                  let* field_type = record_field_type typ_args ld_type in
                  return
                    ( Ident.name ld_id,
                      apply_let_in_type let_in_type field_type ))
            in
            let* constructor_name =
              record_operation_name true prefix (Ident.name ident) None
            in
            let record_parameters =
              List.map (fun parameter -> (parameter, 0)) typ_args
            in
            let constructor_type =
              List.fold_right
                (fun (_, field_type) result -> Type.Arrow (field_type, result))
                fields record_type
              |> quantify_record_operation record_parameters
            in
            let* projections =
              fields
              |> Monad.List.map (fun (field, field_type) ->
                  let* projection_name =
                    record_operation_name false prefix (Ident.name ident)
                      (Some field)
                  in
                  return
                    (Value
                       ( projection_name,
                         quantify_record_operation record_parameters
                           (Type.Arrow (record_type, field_type)),
                         [] )))
            in
            return
              ( ModuleWithSignature
                  (TypExistential name
                   :: Value (constructor_name, constructor_type, [])
                   :: projections),
                let_in_type )
        | Type_abstract _ | Type_variant _ | Type_open ->
            return (TypExistential name, let_in_type))
    | Sig_type (ident, { type_manifest = Some typ; _ }, _, _)
      when abstract_functor_applications && is_functor_application_alias env typ
      -> (
        let* name = Name.of_strings false (prefix @ [ Ident.name ident ]) in
        let* source =
          prefix @ [ Ident.name ident ] |> Monad.List.map (Name.of_string false)
        in
        let* concrete_manifest =
          concrete_result_manifest (prefix @ [ Ident.name ident ])
        in
        let prefer_closed_source_manifest target =
          if Name.Set.is_empty (Type.typ_args_of_typ target) then return target
          else
            let* source = Type.of_type_expr_without_free_vars typ in
            if Name.Set.is_empty (Type.typ_args_of_typ source) then return source
            else return target
        in
        match concrete_manifest with
        | Some declaration ->
            let* target = Type.of_type_expr_without_free_vars declaration in
            let* target = prefer_closed_source_manifest target in
            let target =
              target
              |> apply_constructor_aliases constructor_aliases
              |> apply_let_in_type let_in_type
            in
            let manifest = ManifestConstructor target in
            let* aliases = local_type_aliases prefix ident manifest in
            return (TypSynonym (name, target), aliases @ let_in_type)
        | None -> (
            let* suffix_target =
              manifest_alias_by_suffix prefix let_in_type typ
            in
            let target =
              match suffix_target with
              | Some _ as target -> target
              | None -> find_let_in_type_target source let_in_type
            in
            let target =
              match target with
              | Some target when target_is_self_reference name target -> None
              | target -> target
            in
            match target with
            | Some target ->
                let target_type = type_of_let_in_type_target target in
                let* aliases = local_type_aliases prefix ident target in
                return (TypSynonym (name, target_type), aliases @ let_in_type)
            | None -> (
                match applicative_manifest_declaration env typ with
                | Some declaration ->
                    let* target =
                      Type.of_type_expr_without_free_vars declaration
                    in
                    let* target = prefer_closed_source_manifest target in
                    let target =
                      target
                      |> apply_constructor_aliases constructor_aliases
                      |> apply_let_in_type let_in_type
                    in
                    let manifest = ManifestConstructor target in
                    let* aliases = local_type_aliases prefix ident manifest in
                    return (TypSynonym (name, target), aliases @ let_in_type)
                | None ->
                    let* name, let_in_type =
                      add_new_let_in_type prefix let_in_type ident
                    in
                    return (TypExistential name, let_in_type))))
    | Sig_type
        ( ident,
          { type_manifest = Some typ; type_params; type_kind; _ },
          _,
          _ ) ->
        let previous_let_in_type = let_in_type in
        let* name, let_in_type = add_new_let_in_type prefix let_in_type ident in
        let* typ_args =
          type_params
          |> Monad.List.map (fun typ_param ->
              let* typ = Type.of_type_expr_variable typ_param in
              return (typ, 0))
        in
        let* typ =
          match configured_type_constructor configuration prefix ident with
          | Some target ->
              return
                (Type.Apply
                   ( target,
                     List.map
                       (fun (name, _) -> (Type.Variable name, false))
                       typ_args ))
          | None -> (
              let* direct_typ =
                if type_params = [] then
                  direct_manifest_alias ~scope:prefix previous_let_in_type typ
                else return None
              in
              match direct_typ with
              | Some typ -> return typ
              | None -> Type.of_type_expr_without_free_vars typ)
        in
        let typ = apply_constructor_aliases constructor_aliases typ in
        let typ_with_let_in_type =
          apply_let_in_type previous_let_in_type
            (Type.FunTyps (List.map fst typ_args, typ))
        in
        let type_item = TypSynonym (name, typ_with_let_in_type) in
        (match type_kind with
        | Type_record (labels, _) ->
            let record_type =
              match List.map fst typ_args with
              | [] -> Type.Variable name
              | arguments ->
                  Type.Apply
                    ( MixedPath.of_name name,
                      List.map
                        (fun argument -> (Type.Variable argument, false))
                        arguments )
            in
            let* fields =
              labels
              |> Monad.List.map (fun ({ Types.ld_id; ld_type; _ } :
                                      Types.label_declaration) ->
                  let* field_type =
                    record_field_type (List.map fst typ_args) ld_type
                  in
                  let field_type =
                    field_type
                    |> apply_constructor_aliases constructor_aliases
                    |> apply_let_in_type previous_let_in_type
                  in
                  return (Ident.name ld_id, field_type))
            in
            let* constructor_name =
              record_operation_name true prefix (Ident.name ident) None
            in
            let record_parameters = typ_args in
            let constructor_type =
              List.fold_right
                (fun (_, field_type) result -> Type.Arrow (field_type, result))
                fields record_type
              |> quantify_record_operation record_parameters
            in
            let* projections =
              fields
              |> Monad.List.map (fun (field, field_type) ->
                  let* projection_name =
                    record_operation_name false prefix (Ident.name ident)
                      (Some field)
                  in
                  return
                    (Value
                       ( projection_name,
                         quantify_record_operation record_parameters
                           (Type.Arrow (record_type, field_type)),
                         [] )))
            in
            return
              ( ModuleWithSignature
                  (type_item :: Value (constructor_name, constructor_type, [])
                   :: projections),
                let_in_type )
        | Type_abstract _ | Type_variant _ | Type_open ->
            return (type_item, let_in_type))
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
        let* let_in_type =
          match md_type with
          | Mty_alias target ->
              propagate_module_alias prefix ident target let_in_type
          | _ -> return let_in_type
        in
        let* name = Name.of_ident false ident in
        let* field_name =
          Name.of_strings false (prefix @ [ Ident.name ident ])
        in
        let module_path = Path.Pident ident in
        let* resolved_module_path =
          IsFirstClassModule.resolve_included_signature_path_aliases module_path
        in
        let* module_path_alias = get_module_path_alias module_path in
        let* is_first_class =
          match signature_path with
          | Some parent_signature -> (
              let* field_signature =
                get_result_module_field parent_signature (Ident.name ident)
              in
              match field_signature with
              | Some field_signature ->
                  return (IsFirstClassModule.Found field_signature)
              | None ->
                  IsFirstClassModule.is_module_typ_first_class md_type
                    (Some module_path))
          | None ->
              IsFirstClassModule.is_module_typ_first_class md_type
                (Some module_path)
        in
        match is_first_class with
        | Found signature_path ->
            let* signature_path_name =
              PathName.of_path_with_convert false signature_path
            in
            let* application_signature_hint =
              get_signature_hint resolved_module_path
            in
            let* explicit_record_params =
              match application_signature_hint with
              | Some hint
                when Path.same hint signature_path
                     && String.ends_with ~suffix:"_result"
                          (Path.last signature_path) ->
                  let* namespace =
                    prefix |> Monad.List.map (Name.of_string false)
                  in
                  let* fargs_path =
                    match module_path_alias with
                    | Some alias ->
                        let* path = PathName.of_path_with_convert false alias in
                        return
                          {
                            path with
                            PathName.base =
                              Name.of_string_raw
                                (Name.to_string path.base ^ "_fargs");
                          }
                    | None -> (
                        match resolved_module_path with
                        | Path.Pdot (parent, field)
                          when not (Path.same resolved_module_path module_path)
                          ->
                            PathName.of_path_with_convert false
                              (Path.Pdot (parent, field ^ "_fargs"))
                        | _ ->
                            let fargs_name =
                              Name.of_string_raw (Name.to_string name ^ "_fargs")
                            in
                            return (PathName.of_name namespace fargs_name))
                  in
                  return
                    [
                      ( Name.of_string_raw "_fargs",
                        Some (Type.Apply (MixedPath.PathName fargs_path, [])) );
                    ]
              | Some _ | None -> return []
            in
            let* constructor_aliases =
              let* env = get_env in
              match Mtype.scrape env md_type with
              | Mty_signature signature ->
                  constructor_aliases_of_signature
                    ~abstract_functor_applications
                    ~prefix:(prefix @ [ Ident.name ident ])
                    signature
              | _ -> return []
            in
            let manifest_aliases_with let_in_type =
              let* env = get_env in
              match Mtype.scrape env md_type with
              | Mty_signature signature ->
                  signature
                  |> Monad.List.filter_map (function
                    | Types.Sig_type
                        ( type_ident,
                          { type_manifest = Some manifest; type_params; _ },
                          _,
                          _ )
                      when not
                             (abstract_functor_applications
                             && is_functor_application_alias env manifest) ->
                        let* type_name = Name.of_ident false type_ident in
                        let* parameters =
                          Monad.List.map Type.of_type_expr_variable type_params
                        in
                        let* target_concrete_manifest =
                          ModuleTyp.get_signature_concrete_manifest
                            signature_path
                            [ Ident.name type_ident ]
                        in
                        (* A short path such as [Impl.t] denotes the child
                              module in this result, not a same-named module
                              inherited by the enclosing result. *)
                        let manifest_uses_local_module =
                          match Types.get_desc manifest with
                          | Tconstr (path, [], _) -> (
                              match
                                path_components_without_application path
                              with
                              | Some (module_name :: _ :: _) ->
                                  signature
                                  |> List.exists (function
                                    | Types.Sig_module (ident, _, _, _, _) ->
                                        String.equal (Ident.name ident)
                                          module_name
                                    | _ -> false)
                              | Some _ | None -> false)
                          | _ -> false
                        in
                        let specialized_target () =
                          match concrete_manifest_declaration env manifest with
                          | Some manifest ->
                              Type.of_type_expr_without_free_vars manifest
                          | None -> (
                              let* direct_target =
                                if type_params = [] then
                                  direct_manifest_alias
                                    ~scope:(prefix @ [ Ident.name ident ])
                                    let_in_type manifest
                                else return None
                              in
                              match direct_target with
                              | Some target -> return target
                              | None ->
                                  Type.of_type_expr_without_free_vars manifest)
                        in
                        let* target =
                          (* A scraped [md_type] already contains the
                                application-site specialization.  The generic
                                result signature is needed only to materialize
                                an applicative functor path. *)
                          if is_functor_application_alias env manifest then
                            match target_concrete_manifest with
                            | Some manifest ->
                                Type.of_type_expr_without_free_vars manifest
                            | None -> specialized_target ()
                          else if manifest_uses_local_module then
                            match target_concrete_manifest with
                            | Some manifest ->
                                Type.of_type_expr_without_free_vars manifest
                            | None -> specialized_target ()
                          else specialized_target ()
                        in
                        let target =
                          Type.FunTyps
                            ( parameters,
                              apply_constructor_aliases constructor_aliases
                                target )
                        in
                        return
                          (Some ([ name; type_name ], ManifestConstructor target))
                    | _ -> return None)
              | _ -> return []
            in
            let source_module_name = Ident.name ident in
            let concrete_specialized_manifest type_prefix type_name =
              let* parent_manifest =
                concrete_result_manifest
                  (prefix @ [ source_module_name ] @ type_prefix @ [ type_name ])
              in
              match parent_manifest with
              | Some _ as manifest -> return manifest
              | None ->
                  ModuleTyp.get_signature_concrete_manifest signature_path
                    (type_prefix @ [ type_name ])
            in
            let mapper type_prefix ident { Types.type_manifest; type_params; _ }
                =
              let name = Ident.name ident in
              let* mapped_name =
                Name.of_strings false
                  (prefix @ [ source_module_name ] @ type_prefix @ [ name ])
              in
              (match type_manifest with
                | None -> (
                    let* concrete_manifest =
                      concrete_specialized_manifest type_prefix name
                    in
                    match concrete_manifest with
                    | Some concrete_manifest ->
                        let* typ =
                          Type.of_type_expr_without_free_vars concrete_manifest
                        in
                        return (Type.Typ typ)
                    | None -> return (Type.Arity (List.length type_params)))
                | Some type_manifest
                  when abstract_functor_applications
                       && is_functor_application_alias env type_manifest -> (
                    let* concrete_manifest =
                      concrete_specialized_manifest type_prefix name
                    in
                    match concrete_manifest with
                    | Some concrete_manifest ->
                        let* typ =
                          Type.of_type_expr_without_free_vars concrete_manifest
                        in
                        return (Type.Typ typ)
                    | None -> (
                        let* alias_target =
                          manifest_alias_by_suffix
                            (prefix @ [ source_module_name ] @ type_prefix)
                            let_in_type type_manifest
                        in
                        let alias_target =
                          match alias_target with
                          | Some target
                            when target_is_self_reference mapped_name target ->
                              None
                          | alias_target -> alias_target
                        in
                        match alias_target with
                        | Some target ->
                            return
                              (Type.Typ (type_of_let_in_type_target target))
                        | None -> return (Type.Arity (List.length type_params)))
                    )
                | Some type_manifest -> (
                    match concrete_manifest_declaration env type_manifest with
                    | Some type_manifest ->
                        let* typ =
                          Type.of_type_expr_without_free_vars type_manifest
                        in
                        return (Type.Typ typ)
                    | None -> (
                        let* direct_typ =
                          if type_params = [] then
                            direct_manifest_alias
                              ~scope:(prefix @ [ Ident.name ident ])
                              let_in_type type_manifest
                          else return None
                        in
                        match direct_typ with
                        | Some typ -> return (Type.Typ typ)
                        | None ->
                            type_params
                            |> Monad.List.map Type.of_type_expr_variable
                            >>= fun typ_args ->
                            Type.of_type_expr_without_free_vars type_manifest
                            >>= fun typ ->
                            let typ =
                              Type.FunTyps
                                ( typ_args,
                                  apply_constructor_aliases constructor_aliases
                                    typ )
                            in
                            return (Type.Typ typ))))
              >>= fun arity_or_typ ->
              return (Some (Tree.Item (name, arity_or_typ)))
            in
            let* typ_params =
              ModuleTypParams.get_module_typ_typ_params mapper md_type
            in
            let* target_typ_params =
              ModuleTyp.get_signature_typ_params_arity signature_path
            in
            let target_typ_param_paths =
              Tree.flatten target_typ_params |> List.map fst
            in
            let* typ_params_with_paths =
              Tree.flatten typ_params
              |> List.filter (fun (path, _) ->
                  List.exists
                    (fun target_path -> target_path = path)
                    target_typ_param_paths)
              |> Monad.List.map (fun (path, arity_or_typ) ->
                  let* name = Name.of_strings false path in
                  let* typ_name =
                    Name.of_strings false (prefix @ (Ident.name ident :: path))
                  in
                  let* source =
                    prefix @ (Ident.name ident :: path)
                    |> Monad.List.map (Name.of_string false)
                  in
                  let alias_target =
                    find_let_in_type_target source let_in_type
                  in
                  let alias_target =
                    match alias_target with
                    | Some target when target_is_self_reference typ_name target
                      ->
                        None
                    | alias_target -> alias_target
                  in
                  match (alias_target, arity_or_typ) with
                  | Some target, _ ->
                      return
                        ( path,
                          name,
                          Some (type_of_let_in_type_target target),
                          Some target )
                  | None, Type.Arity _ ->
                      return (path, name, Some (Type.Variable typ_name), None)
                  | None, Typ typ -> return (path, name, Some typ, None))
            in
            let typ_params =
              typ_params_with_paths
              |> List.map (fun (_, name, typ, _) -> (name, typ))
            in
            let* alias_type_fields =
              typ_params_with_paths
              |> Monad.List.filter_map (fun (path, _, _, alias_target) ->
                  match alias_target with
                  | None -> return None
                  | Some target ->
                      let* name =
                        Name.of_strings false
                          (prefix @ (Ident.name ident :: path))
                      in
                      return
                        (Some
                           (TypSynonym (name, type_of_let_in_type_target target))))
            in
            let* local_typ_param_aliases =
              typ_params_with_paths
              |> Monad.List.concat_map (fun (path, _, typ, _) ->
                  let* source = Monad.List.map (Name.of_string false) path in
                  let* qualified_prefix =
                    Monad.List.map (Name.of_string false) prefix
                  in
                  let sources =
                    path_suffixes (qualified_prefix @ (name :: source))
                  in
                  let aliases target =
                    sources |> List.map (fun source -> (source, target))
                  in
                  match typ with
                  | Some (Type.Variable target) ->
                      return (aliases (LocalConstructor target))
                  | Some typ -> return (aliases (ManifestConstructor typ))
                  | None -> return [])
            in
            let* manifest_aliases =
              manifest_aliases_with (local_typ_param_aliases @ let_in_type)
            in
            let* applicative_manifest_aliases =
              let* env = get_env in
              match Mtype.scrape env md_type with
              | Mty_signature signature ->
                  signature
                  |> Monad.List.filter_map (function
                    | Types.Sig_type
                        ( type_ident,
                          { type_manifest = Some manifest; type_params = []; _ },
                          _,
                          _ )
                      when abstract_functor_applications
                           && is_functor_application_alias env manifest -> (
                        let* type_name = Name.of_ident false type_ident in
                        let* local_target =
                          match Types.get_desc manifest with
                          | Tconstr (path, [], _) -> (
                              match
                                path_suffix_after_functor_application path
                              with
                              | Some (_ :: _ as suffix) ->
                                  let* suffix =
                                    suffix
                                    |> Monad.List.map (Name.of_string false)
                                  in
                                  return
                                    (find_let_in_type_target suffix
                                       local_typ_param_aliases)
                              | Some [] | None -> return None)
                          | _ -> return None
                        in
                        match local_target with
                        | Some target ->
                            return (Some ([ name; type_name ], target))
                        | None -> (
                            match
                              applicative_manifest_declaration env manifest
                            with
                            | None -> return None
                            | Some declaration ->
                                let* target =
                                  Type.of_type_expr_without_free_vars
                                    declaration
                                in
                                let target =
                                  target
                                  |> apply_constructor_aliases
                                       constructor_aliases
                                  |> apply_let_in_type local_typ_param_aliases
                                  |> apply_let_in_type let_in_type
                                in
                                return
                                  (Some
                                     ( [ name; type_name ],
                                       ManifestConstructor target ))))
                    | _ -> return None)
              | _ -> return []
            in
            let manifest_aliases =
              applicative_manifest_aliases
              @ (manifest_aliases
                |> List.map (fun (source, target) ->
                    let target =
                      match target with
                      | LocalConstructor _ -> target
                      | ManifestConstructor typ ->
                          ManifestConstructor
                            (typ
                            |> apply_let_in_type local_typ_param_aliases
                            |> apply_let_in_type let_in_type)
                    in
                    (source, target)))
            in
            let* let_in_type =
              typ_params_with_paths
              |> Monad.List.fold_left
                   (fun let_in_type (path, _, typ, _) ->
                     let* source_path =
                       Monad.List.map (Name.of_string false) path
                     in
                     let* qualified_prefix =
                       Monad.List.map (Name.of_string false) prefix
                     in
                     let sources =
                       path_suffixes (qualified_prefix @ (name :: source_path))
                       |> List.filter (fun source -> List.length source > 1)
                     in
                     let aliases target =
                       sources |> List.map (fun source -> (source, target))
                     in
                     match typ with
                     | Some (Type.Variable target) ->
                         return (aliases (LocalConstructor target) @ let_in_type)
                     | Some typ ->
                         let typ = apply_let_in_type let_in_type typ in
                         return (aliases (ManifestConstructor typ) @ let_in_type)
                     | None -> return let_in_type)
                   (manifest_aliases @ let_in_type)
            in
            let record_typ_params = explicit_record_params @ typ_params in
            let result =
              ( (match alias_type_fields with
                | [] ->
                    Module
                      ( field_name,
                        Type.Signature (signature_path_name, record_typ_params),
                        [] )
                | _ :: _ ->
                    ModuleWithSignature
                      (alias_type_fields
                      @ [
                          Module
                            ( field_name,
                              Type.Signature
                                (signature_path_name, record_typ_params),
                              [] );
                        ])),
                let_in_type )
            in
            return result
        | Not_found reason -> (
            let* env = get_env in
            let strengthened_module_type = Env.scrape_alias env md_type in
            match strengthened_module_type with
            | Mty_signature signature ->
                let prefix = prefix @ [ Ident.name ident ] in
                let* items, nested_let_in_type =
                  items_of_types_signature ~abstract_functor_applications
                    ~expand_aliases ?signature_path
                    ?partial_monad_manifest:effective_partial_monad_manifest
                    ~operation_prefix:(operation_prefix @ [ Ident.name ident ])
                    prefix let_in_type signature
                in
                let nested_let_in_type =
                  nested_let_in_type
                  |> List.filter (fun ((source, _) as alias) ->
                      List.length source > 1 || List.mem alias let_in_type)
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
                let parameter_types =
                  Option.map
                    (List.map (fun parameter ->
                         parameter.FunctorParameterHint.module_type))
                    parameter_types
                in
                let* module_typ =
                  ModuleTyp.of_types ?result_signature_path ?parameter_types
                    md_type
                in
                let* (_, functor_params, result_free_vars), typ =
                  ModuleTyp.to_typ []
                    (Name.to_string field_name)
                    false module_typ
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
                                (Name.of_string_raw "_fargs", Some build_fargs)
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
                             (fun typ { ModuleTyp.name; source_name; _ } ->
                               let companion =
                                 MixedPath.AppliedAccess
                                   ( PathName.of_name [ field_name ] source_name,
                                     [ ("_fargs", build_fargs) ],
                                     [] )
                               in
                               Type.subst_constructor_application name
                                 (Type.Apply (companion, []))
                                 typ)
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
                         ([ name; source_name ], LocalConstructor target)
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
      let* excluded =
        match item with
        | Sig_value (ident, _, _) | Sig_module (ident, _, _, _, _) ->
            let* configuration = get_configuration in
            let* enclosing_path = get_definition_path in
            return
              (Configuration.is_definition_excluded configuration
                 (enclosing_path @ prefix @ [ Ident.name ident ]))
        | _ -> return false
      in
      if excluded then
        items_of_types_signature ~abstract_functor_applications ~expand_aliases
          ?signature_path
          ?partial_monad_manifest:effective_partial_monad_manifest
          ~operation_prefix prefix let_in_type items
      else
        let* item, let_in_type = of_types_signature_item item in
        let* items, let_in_type =
          items_of_types_signature ~abstract_functor_applications
            ~expand_aliases ?signature_path
            ?partial_monad_manifest:effective_partial_monad_manifest
            ~operation_prefix prefix let_in_type items
        in
        return (item :: items, let_in_type)

let of_types_signature ?(abstract_functor_applications = false)
    ?(expand_aliases = false) ?signature_path (signature : Types.signature) :
    t Monad.t =
  let* items, _ =
    items_of_types_signature ~abstract_functor_applications ~expand_aliases
      ?signature_path [] [] signature
  in
  let* typ_params =
    if abstract_functor_applications then
      let* env = get_env in
      let mapper path ident { Types.type_manifest; type_params; _ } =
        match type_manifest with
        | None ->
            return
              (Some (Tree.Item (Ident.name ident, List.length type_params)))
        | Some typ when is_functor_application_alias env typ ->
            let* concrete_manifest =
              match signature_path with
              | Some signature_path ->
                  ModuleTyp.get_signature_concrete_manifest signature_path
                    (path @ [ Ident.name ident ])
              | None -> return None
            in
            if
              Option.is_some concrete_manifest
              || Option.is_some (applicative_manifest_declaration env typ)
            then return None
            else
              return
                (Some (Tree.Item (Ident.name ident, List.length type_params)))
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
    | ModuleWithSignature items -> items |> List.concat_map item_typ_params
    | _ -> []
  in
  let typ_params =
    List.fold_left
      (fun typ_params (name, arity) ->
        if List.exists (fun (other, _) -> Name.equal name other) typ_params then
          typ_params
        else typ_params @ [ (name, arity) ])
      typ_params
      (items |> List.concat_map item_typ_params)
  in
  let rec manifest_type_fields = function
    | TypSynonym (name, _) -> [ name ]
    | ModuleWithSignature items -> items |> List.concat_map manifest_type_fields
    | _ -> []
  in
  let manifest_type_fields = items |> List.concat_map manifest_type_fields in
  let typ_params =
    typ_params
    |> List.filter (fun (name, _) ->
        not
          (List.exists
             (fun manifest_name -> Name.equal name manifest_name)
             manifest_type_fields))
  in
  let rec item_type_variables = function
    | Module (_, typ, _)
    | ModuleWithTypeParams (_, typ, _)
    | TypSynonym (_, typ)
    | Value (_, typ, _) ->
        Type.typ_args_of_typ typ
    | ModuleWithSignature items ->
        items
        |> List.map item_type_variables
        |> List.fold_left Name.Set.union Name.Set.empty
    | Error _ | Documentation _ | TypExistential _ -> Name.Set.empty
  in
  let rec item_type_fields = function
    | TypExistential name | TypSynonym (name, _) -> Name.Set.singleton name
    | ModuleWithSignature items ->
        items |> List.map item_type_fields
        |> List.fold_left Name.Set.union Name.Set.empty
    | Error _ | Documentation _ | Module _ | ModuleWithTypeParams _ | Value _ ->
        Name.Set.empty
  in
  let referenced_types =
    items
    |> List.map item_type_variables
    |> List.fold_left Name.Set.union Name.Set.empty
  in
  let defined_types =
    items |> List.map item_type_fields
    |> List.fold_left Name.Set.union Name.Set.empty
  in
  let existing_parameters = typ_params |> List.map fst |> Name.Set.of_list in
  let missing_parameters =
    Name.Set.diff
      (Name.Set.diff referenced_types defined_types)
      existing_parameters
    |> Name.Set.elements
  in
  let typ_params =
    typ_params
    @ List.map
        (fun name ->
          (* A generated dependent record must be closed over every
             associated type that survived specialization. *)
          (name, 0))
        missing_parameters
  in
  let contextual_type_fields =
    typ_params
    |> List.filter_map (fun (name, _) ->
        if Name.Set.mem name defined_types then None
        else
          (* A nested module's associated type is a contextual parameter of
             the flattened result record.  Expose that parameter as a
             definitional field as well, so clients can refer to it through
             the instantiated result (for example [R.C_t]) rather than a
             binder that is no longer in scope. *)
          Some (TypExistential name))
  in
  return { items = items @ contextual_type_fields; typ_params }

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
            | Tsig_include { incl_mod; incl_type; _ } ->
                let operation_prefix =
                  match incl_mod.mty_desc with
                  | Tmty_ident (path, _) | Tmty_alias (path, _) ->
                      String.split_on_char '.' (Path.name path)
                  | _ -> prefix
                in
                set_env next_env
                  (items_of_types_signature ~operation_prefix prefix let_in_type
                     incl_type)
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
                let* configuration = get_configuration in
                let* enclosing_path = get_definition_path in
                if
                  Configuration.is_definition_excluded configuration
                    (enclosing_path @ prefix @ [ id ])
                then return ([], let_in_type)
                else
                  match md_type.mty_desc with
                  | Tmty_signature signature ->
                      let prefix = prefix @ [ id ] in
                      let* items =
                        of_signature_items prefix let_in_type
                          signature.sig_items next_env
                      in
                      return ([ ModuleWithSignature items ], let_in_type)
                  | _ ->
                      push_env
                        (let prefixed_id =
                           String.concat "_" (prefix @ [ id ])
                         in
                         let* prefixed_name =
                           Name.of_string false prefixed_id
                         in
                         let* module_typ = ModuleTyp.of_ocaml md_type in
                         let* (_, _, free_vars), typ =
                           ModuleTyp.to_typ [] prefixed_id false module_typ
                         in
                         let* module_name = Name.of_string false id in
                         let let_in_type =
                           free_vars
                           |> List.fold_left
                                (fun let_in_type
                                     { ModuleTyp.name; source_name; _ } ->
                                  ( [ module_name; source_name ],
                                    LocalConstructor name )
                                  :: let_in_type)
                                let_in_type
                         in
                         return
                           ([ Module (prefixed_name, typ, []) ], let_in_type)))
            | Tsig_open _ -> return ([], let_in_type)
            | Tsig_recmodule _ ->
                raise
                  ([ Error "recursive_module" ], let_in_type)
                  NotSupported "Recursive module signatures are not handled."
            | Tsig_type
                ( _,
                  [
                    {
                      typ_id;
                      typ_type =
                        { type_manifest = None; type_params; type_kind; _ };
                      _;
                    };
                  ] )
              ->
                let* name, let_in_type =
                  add_new_let_in_type prefix let_in_type typ_id
                in
                (match type_kind with
                | Type_record (labels, _) ->
                    let* typ_args =
                      type_params |> Monad.List.map Type.of_type_expr_variable
                    in
                    let record_type =
                      match typ_args with
                      | [] -> Type.Variable name
                      | arguments ->
                          Type.Apply
                            ( MixedPath.of_name name,
                              List.map
                                (fun argument -> (Type.Variable argument, false))
                                arguments )
                    in
                    let* fields =
                      labels
                      |> Monad.List.map (fun ({ Types.ld_id; ld_type; _ } :
                                              Types.label_declaration) ->
                          let* field_type = record_field_type typ_args ld_type in
                          return
                            ( Ident.name ld_id,
                              apply_let_in_type let_in_type field_type ))
                    in
                    let* constructor_name =
                      record_operation_name true prefix (Ident.name typ_id) None
                    in
                    let record_parameters =
                      List.map (fun parameter -> (parameter, 0)) typ_args
                    in
                    let constructor_type =
                      List.fold_right
                        (fun (_, field_type) result ->
                          Type.Arrow (field_type, result))
                        fields record_type
                      |> quantify_record_operation record_parameters
                    in
                    let* projections =
                      fields
                      |> Monad.List.map (fun (field, field_type) ->
                          let* projection_name =
                            record_operation_name false prefix
                              (Ident.name typ_id) (Some field)
                          in
                          return
                            (Value
                               ( projection_name,
                                 quantify_record_operation record_parameters
                                   (Type.Arrow (record_type, field_type)),
                                 [] )))
                    in
                    return
                      ( TypExistential name
                        :: Value (constructor_name, constructor_type, [])
                        :: projections,
                        let_in_type )
                | Type_abstract _ | Type_variant _ | Type_open ->
                    return ([ TypExistential name ], let_in_type))
            | Tsig_type (_, typs) | Tsig_typesubst typs -> (
                match typs with
                | [
                 {
                   typ_id;
                   typ_type =
                     { type_manifest = Some typ; type_params; type_kind; _ };
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
                    let type_item = TypSynonym (name, typ_with_let_in_type) in
                    (match type_kind with
                    | Type_record (labels, _) ->
                        let record_type =
                          match typ_args with
                          | [] -> Type.Variable name
                          | arguments ->
                              Type.Apply
                                ( MixedPath.of_name name,
                                  List.map
                                    (fun argument ->
                                      (Type.Variable argument, false))
                                    arguments )
                        in
                        let* fields =
                          labels
                          |> Monad.List.map (fun ({ Types.ld_id; ld_type; _ } :
                                                  Types.label_declaration) ->
                              let* field_type = record_field_type typ_args ld_type in
                              return
                                ( Ident.name ld_id,
                                  apply_let_in_type let_in_type field_type ))
                        in
                        let* constructor_name =
                          record_operation_name true prefix (Ident.name typ_id)
                            None
                        in
                        let record_parameters =
                          List.map (fun parameter -> (parameter, 0)) typ_args
                        in
                        let constructor_type =
                          List.fold_right
                            (fun (_, field_type) result ->
                              Type.Arrow (field_type, result))
                            fields record_type
                          |> quantify_record_operation record_parameters
                        in
                        let* projections =
                          fields
                          |> Monad.List.map (fun (field, field_type) ->
                              let* projection_name =
                                record_operation_name false prefix
                                  (Ident.name typ_id) (Some field)
                              in
                              return
                                (Value
                                   ( projection_name,
                                     quantify_record_operation record_parameters
                                       (Type.Arrow (record_type, field_type)),
                                     [] )))
                        in
                        return
                          ( type_item
                            :: Value (constructor_name, constructor_type, [])
                            :: projections,
                            let_in_type )
                    | Type_abstract _ | Type_variant _ | Type_open ->
                        return ([ type_item ], let_in_type))
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
                let* configuration = get_configuration in
                let* enclosing_path = get_definition_path in
                if
                  Configuration.is_definition_excluded configuration
                    (enclosing_path @ prefix @ [ Ident.name val_id ])
                then return ([], let_in_type)
                else
                  let* prefixed_name =
                    Name.of_strings true (prefix @ [ Ident.name val_id ])
                  in
                  let* typ = quantified_value_type ctyp_type in
                  let typ_with_let_in_type =
                    apply_let_in_type let_in_type typ
                  in
                  let requirements =
                    partial_value_requirements prefix (Ident.name val_id)
                      typ_with_let_in_type
                  in
                  return
                    ( [
                        Value (prefixed_name, typ_with_let_in_type, requirements);
                      ],
                      let_in_type ))))
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

let contextualize_item_type contextual requirements typ =
  Name.Map.fold
    (fun parameter contexts typ ->
      List.fold_right
        (fun context typ ->
          let binder =
            requirements
            |> List.mapi (fun index requirement -> (index, requirement))
            |> List.find_map (fun (index, requirement) ->
                if Exp.compare_assumption_requirement context requirement = 0
                then
                  Some
                    (Name.of_string_raw
                       (Printf.sprintf "_rocq_assumption_%d" index))
                else None)
          in
          match binder with
          | Some binder -> Type.apply_local_type_parameter parameter binder typ
          | None -> typ)
        contexts typ)
    contextual typ

(** If an associated type is indexed by generated assumptions, every field
    whose type mentions that associated type must quantify over those indices.
    The source field itself may be total (record constructors and projections
    are typical examples), so its ordinary call-requirement analysis does not
    necessarily discover them. *)
let to_coq_signature_typ_params contextual typ_params =
  typ_params
  |> List.map (fun (name, arity) ->
      let kind = Type.Kind (Kind.set_arrows arity) in
      let typ =
        match Name.Map.find_opt name contextual with
        | None -> kind
        | Some requirements ->
            List.fold_right
              (fun requirement typ ->
                Type.Arrow (Exp.assumption_class_type requirement, typ))
              requirements kind
      in
      braces (nest (Name.to_coq name ^^ !^":" ^^ Type.to_coq None None typ)))
  |> separate space

let named_requirements requirements =
  requirements
  |> List.mapi (fun index requirement ->
      ( Name.of_string_raw (Printf.sprintf "_rocq_assumption_%d" index),
        requirement ))

let materialize_named_requirements materialize_requirement_type requirements =
  requirements
  |> named_requirements
  |> List.fold_left
       (fun materialized (name, (kind, typ)) ->
         let requirement =
           (kind, materialize_requirement_type materialized typ)
         in
         materialized @ [ (name, requirement) ])
       []

let rec take count values =
  if count <= 0 then []
  else
    match values with
    | [] -> []
    | value :: remaining -> value :: take (count - 1) remaining

let rec to_coq_item
    (materialize_requirement_type :
      (Name.t * Exp.assumption_requirement) list -> Type.t -> Type.t)
    (order_requirements :
      Name.t ->
      Exp.assumption_requirement list -> Exp.assumption_requirement list)
    contextual (signature_item : item) : SmartPrint.t =
  match signature_item with
  | Error message -> !^("(* " ^ message ^ " *)")
  | Documentation message -> !^("(** " ^ message ^ " *)")
  | Module (name, typ, requirements) ->
    let requirements = order_requirements name requirements in
      let requirements =
        add_contextual_item_requirements contextual typ requirements
      in
      let typ = contextualize_item_type contextual requirements typ in
      let named_requirements =
        materialize_named_requirements materialize_requirement_type requirements
      in
      let requirement_binders =
        named_requirements
        |> List.map (fun (binder, (kind, typ)) ->
            !^"`"
            ^-^ braces
                  (nest
                     (Name.to_coq binder
                     ^^ !^":"
                     ^^ Type.to_coq None None
                          (Exp.assumption_class_type (kind, typ)))))
      in
      let typ = materialize_requirement_type named_requirements typ in
      let rendered_type =
        match requirement_binders with
        | [] -> Type.to_coq None None typ
        | _ ->
            nest
              (!^"forall"
              ^^ separate space requirement_binders
              ^-^ !^"," ^^ Type.to_coq None None typ)
      in
      nest (Name.to_coq name ^^ !^":" ^^ rendered_type ^-^ !^";")
  | ModuleWithTypeParams (name, typ, _) ->
      nest (Name.to_coq name ^^ !^":" ^^ Type.to_coq None None typ ^-^ !^";")
  | ModuleWithSignature items ->
      separate newline
        (to_coq_items materialize_requirement_type order_requirements contextual
           items)
  | TypExistential name ->
      nest (Name.to_coq name ^^ !^":=" ^^ Name.to_coq name ^-^ !^";")
  | TypSynonym (name, typ) ->
      nest (Name.to_coq name ^^ !^":=" ^^ Type.to_coq None None typ ^-^ !^";")
  | Value (name, typ, requirements) ->
      let requirements = order_requirements name requirements in
      let requirements =
        add_contextual_item_requirements contextual typ requirements
      in
      let typ = contextualize_item_type contextual requirements typ in
      let rec collect_type_parameters parameters typ =
        match typ with
        | Type.ForallTyps (new_parameters, body) ->
            collect_type_parameters (parameters @ new_parameters) body
        | body -> (parameters, body)
      in
      let parameters, body = collect_type_parameters [] typ in
      let named_requirements =
        materialize_named_requirements materialize_requirement_type requirements
      in
      let requirement_binders =
        named_requirements
        |> List.map (fun (binder, (kind, typ)) ->
            !^"`"
            ^-^ braces
                  (nest
                     (Name.to_coq binder
                     ^^ !^":"
                     ^^ Type.to_coq None None
                          (Exp.assumption_class_type (kind, typ)))))
      in
      let body = materialize_requirement_type named_requirements body in
      let rendered_type =
        match (parameters, requirement_binders) with
        | [], [] -> Type.to_coq None None body
        | _ ->
            nest
              (!^"forall"
              ^^ (match parameters with
                | [] -> empty
                | _ -> Type.to_coq_grouped_typ_params Type.Braces parameters)
              ^^ separate space requirement_binders
              ^-^ !^"," ^^ Type.to_coq None None body)
      in
      nest (Name.to_coq name ^^ !^":" ^^ rendered_type ^-^ !^";")

and to_coq_items materialize_requirement_type order_requirements contextual
    (items : item list) : SmartPrint.t list =
  List.map
    (to_coq_item materialize_requirement_type order_requirements contextual)
    items

let rec item_has_field (item : item) : bool =
  match item with
  | Error _ | Documentation _ -> false
  | ModuleWithSignature items -> List.exists item_has_field items
  | Module _ | ModuleWithTypeParams _ | TypExistential _ | TypSynonym _
  | Value _ ->
      true

let to_coq_definition ?(dependency_free_vars : ModuleTyp.free_vars = [])
    ?(dependency_parameters : (Name.t * Type.t) list = [])
    ?(order_requirements = fun _ requirements -> requirements)
    ?(materialize_requirement_type = fun _ typ -> typ) (fargs : FArgs.t)
    (name : Name.t) (signature : t) : SmartPrint.t =
  let contextual = contextual_typ_params signature in
  let dependency_definition_binders =
    ModuleTyp.to_coq_grouped_free_vars dependency_free_vars
    ^^ group
         (separate space
            (dependency_parameters
            |> List.map (fun (name, typ) ->
                   nest
                     (braces
                        (Name.to_coq name ^^ !^":"
                       ^^ Type.to_coq None None typ)))))
  in
  let dependency_declaration_binders =
    ModuleTyp.to_coq_grouped_free_vars dependency_free_vars
    ^^ group
         (separate space
            (dependency_parameters
            |> List.map (fun (name, typ) ->
                   nest
                     (braces
                        (Name.to_coq name ^^ !^":"
                       ^^ Type.to_coq None None typ)))))
  in
  let dependency_arguments =
    List.map
      (fun { ModuleTyp.name; _ } -> Name.to_coq name)
      dependency_free_vars
    @ List.map (fun (name, _) -> Name.to_coq name) dependency_parameters
  in
  let declaration =
    if not (List.exists item_has_field signature.items) then
      nest
        (!^"Inductive" ^^ !^"signature" ^^ dependency_declaration_binders
        ^^ FArgs.to_coq fargs
        ^^ to_coq_signature_typ_params contextual signature.typ_params
        ^^ nest (!^":" ^^ !^"Type")
        ^^ !^":=" ^^ newline ^^ !^"|" ^^ !^"Build_signature" ^^ !^":"
        ^^ !^"signature" ^-^ !^".")
    else
      nest
        (!^"Record" ^^ !^"signature" ^^ dependency_declaration_binders
        ^^ FArgs.to_coq fargs
        ^^ to_coq_signature_typ_params contextual signature.typ_params
        ^^ nest (!^":" ^^ !^"Type")
        ^^ !^":=" ^^ !^"{" ^^ newline
        ^^ indent
             (separate newline
                (to_coq_items materialize_requirement_type order_requirements
                   contextual signature.items))
        ^^ newline ^^ !^"}" ^-^ !^".")
  in
  !^"Module" ^^ Name.to_coq name ^-^ !^"." ^^ newline ^^ indent declaration
  ^^ newline ^^ !^"End" ^^ Name.to_coq name ^-^ !^"." ^^ newline
  ^^ nest
       (!^"Definition" ^^ Name.to_coq name ^^ dependency_definition_binders
       ^^ FArgs.to_coq fargs ^^ !^":="
       ^^
       match (dependency_arguments, fargs) with
       | _ :: _, _ | [], Some _ ->
           separate space
             ((!^"@" ^-^ Name.to_coq name ^-^ !^"." ^-^ !^"signature")
             :: dependency_arguments @ FArgs.to_coq_underscores fargs)
           ^-^ !^"."
       | [], None ->
           (match signature.typ_params with [] -> empty | _ :: _ -> !^"@")
           ^-^ Name.to_coq name ^-^ !^"." ^-^ !^"signature" ^-^ !^".")
  ^^
  match (dependency_arguments, fargs, signature.typ_params) with
  | _ :: _, _, _ -> empty
  | [], None, [] -> empty
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
