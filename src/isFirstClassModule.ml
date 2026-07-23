open Monad.Notations
(** Utilities to check if a module is a first-class module and get the
    namespace of its signature definition. *)

(** Recursively get all the module type declarations inside a module declaration.
    We retreive the path and definition of each. *)
let rec get_modtype_declarations_of_module_declaration (env : Env.t)
    (module_declaration : Types.module_declaration) :
    (Ident.t list * Types.modtype_declaration) list =
  match Env.scrape_alias env module_declaration.md_type with
  | Mty_signature signature ->
      signature
      |> List.concat_map (function
           | Types.Sig_modtype (module_type_ident, module_type, _) ->
               [ ([ module_type_ident ], module_type) ]
           | Sig_module (ident, _, module_declaration, _, _) ->
               get_modtype_declarations_of_module_declaration env
                 module_declaration
               |> List.map (fun (idents, declaration) ->
                      (ident :: idents, declaration))
           | _ -> [])
  | _ -> []
  | exception _ -> []

let is_modtype_declaration_similar_to_shape (env : Env.t)
    (modtype_declaration : Types.modtype_declaration) (shape : SignatureShape.t)
    : bool =
  match Option.map (Env.scrape_alias env) modtype_declaration.mtd_type with
  | Some (Mty_signature signature) ->
      let shape' =
        SignatureShape.of_signature (Some modtype_declaration.mtd_attributes)
          signature
      in
      SignatureShape.are_equal shape shape'
  | _ -> false

let module_type_is_similar_to_shape (env : Env.t)
    (module_type : Types.module_type) (shape : SignatureShape.t) : bool =
  match Env.scrape_alias env module_type with
  | Mty_signature signature ->
      let candidate_shape = SignatureShape.of_signature None signature in
      SignatureShape.are_equal shape candidate_shape
  | _ -> false
  | exception _ -> false

let module_type_has_same_names_as_shape (env : Env.t)
    (module_type : Types.module_type) (shape : SignatureShape.t) : bool =
  match Env.scrape_alias env module_type with
  | Mty_signature signature ->
      let candidate_shape = SignatureShape.of_signature None signature in
      SignatureShape.have_same_names shape candidate_shape
  | _ -> false
  | exception _ -> false

let apply_idents_on_path (path : Path.t) (idents : Ident.t list) : Path.t =
  List.fold_left
    (fun path ident -> Path.Pdot (path, Ident.name ident))
    path idents

let merge_similar_paths (paths : Path.t list) : Path.t list Monad.t =
  paths |> Monad.List.sort_uniq PathName.compare_paths

let latest_path (paths : Path.t list) : Path.t option =
  paths
  |> List.sort (fun left right ->
         match Int.compare (Path.scope right) (Path.scope left) with
         | 0 -> Path.compare left right
         | ordering -> ordering)
  |> List.find_opt (fun _ -> true)

let module_type_fingerprint (env : Env.t) (module_typ : Types.module_type) :
    string =
  Printtyp.wrap_printing_env ~error:true env (fun () ->
      Format.asprintf "%a" Printtyp.modtype module_typ)

let module_types_are_equivalent (env : Env.t) (left : Types.module_type)
    (right : Types.module_type) : bool =
  module_type_fingerprint env left = module_type_fingerprint env right

let is_modtype_declaration_equivalent (env : Env.t)
    (module_typ : Types.module_type) (path : Path.t) : bool =
  match (Env.find_modtype path env).mtd_type with
  | Some candidate ->
      module_types_are_equivalent env module_typ
        (Env.scrape_alias env candidate)
  | None -> false
  | exception Not_found -> false

let copy_module_type (module_typ : Types.module_type) : Types.module_type =
  Subst.modtype Subst.Keep Subst.identity module_typ

(** Inclusion is checked on fresh copies because compiler-libs may instantiate
    type variables while comparing module types.  In particular, the result
    of [F (X)] commonly has type [S with type t = X.t]: it is not textually
    equal to [S], but it is represented by the same Rocq signature record with
    the associated type parameter instantiated. *)
let module_type_includes (env : Env.t) (implementation : Types.module_type)
    (specification : Types.module_type) : bool =
  try
    ignore
      (Includemod.modtypes ~loc:Location.none env ~mark:false
         (copy_module_type implementation)
         (copy_module_type specification));
    true
  with _ -> false

let is_modtype_declaration_included (env : Env.t)
    (module_typ : Types.module_type) (path : Path.t) : bool =
  match (Env.find_modtype path env).mtd_type with
  | Some candidate ->
      module_type_includes env module_typ (Env.scrape_alias env candidate)
  | None -> false
  | exception Not_found -> false

let signature_paths_are_equivalent (env : Env.t) (paths : Path.t list) : bool =
  match paths with
  | [] | [ _ ] -> true
  | first :: rest -> (
      match (Env.find_modtype first env).mtd_type with
      | None -> false
      | Some first_module_type ->
          let first_module_type = Env.scrape_alias env first_module_type in
          List.for_all
            (fun path ->
              match (Env.find_modtype path env).mtd_type with
              | Some module_type ->
                  module_types_are_equivalent env first_module_type
                    (Env.scrape_alias env module_type)
              | None -> false
              | exception Not_found -> false)
            rest
      | exception Not_found -> false)

let find_similar_signatures_with_shape (env : Env.t) (shape : SignatureShape.t)
    : (Path.t list * SignatureShape.t) Monad.t =
  (* We explore signatures in the current namespace. *)
  let similar_signature_paths =
    Env.fold_modtypes
      (fun _ signature_path modtype_declaration signature_paths ->
        if is_modtype_declaration_similar_to_shape env modtype_declaration shape
        then signature_path :: signature_paths
        else signature_paths)
      None env []
  in
  (* We explore signatures in modules in the current namespace. *)
  let similar_signature_paths_in_modules =
    (* We favor locally defined signatures. *)
    match similar_signature_paths with
    | _ :: _ -> []
    | [] ->
        Env.fold_modules
          (fun _ module_path module_declaration signature_paths ->
            let similar_modtype_declarations =
              get_modtype_declarations_of_module_declaration env
                module_declaration
              |> List.filter (fun (_, modtype_declaration) ->
                     is_modtype_declaration_similar_to_shape env
                       modtype_declaration shape)
              |> List.map (fun (idents, _) ->
                     apply_idents_on_path module_path idents)
            in
            similar_modtype_declarations @ signature_paths)
          None env []
  in
  merge_similar_paths
    (similar_signature_paths @ similar_signature_paths_in_modules)
  >>= fun paths ->
  let* paths =
    paths
    |> Monad.List.filter (fun path ->
           let* configuration = get_configuration in
           let is_in_black_list =
             Configuration.is_in_first_class_module_signature_backlist
               configuration path
           in
           return (not is_in_black_list))
  in
  return (paths, shape)

(** Find the [Path.t] of all the signature definitions which are found to be similar
    to [signature]. If the signature is the one of a module used as a namespace there
    should be none. If the signature is the one a first-class module there should be
    exactly one. There may be more than one result if two signatures have the same
    or similar definitions. In this case we will fail later with an explicit
    error message. *)
let find_similar_signatures ?(include_hidden_hints = false) (env : Env.t)
    (signature : Types.signature) :
    (Path.t list * SignatureShape.t) Monad.t =
  let shape = SignatureShape.of_signature None signature in
  if SignatureShape.is_empty shape then return ([], shape)
  else
    let module_typ = Types.Mty_signature signature in
    let* configuration = get_configuration in
    let* module_type_hints = get_module_type_hints in
    let module_type_hints =
      module_type_hints
      |> List.filter (fun (path, _) ->
             include_hidden_hints
             ||
             match Env.find_modtype path env with
             | _ -> true
             | exception Not_found -> false)
    in
    let eligible_hints =
      module_type_hints
      |> List.filter (fun (path, candidate) ->
             (not
                (Configuration.is_in_first_class_module_signature_backlist
                   configuration path))
             && module_type_has_same_names_as_shape env candidate shape)
    in
    let hinted_candidates =
      eligible_hints
      |> List.filter (fun (_, candidate) ->
             module_type_is_similar_to_shape env candidate shape)
    in
    let choose_hinted_path candidates =
      let* paths =
        candidates |> List.map fst |> merge_similar_paths
      in
      return (latest_path paths)
    in
    let equivalent_hints =
      eligible_hints
      |> List.filter (fun (_, candidate) ->
             module_types_are_equivalent env module_typ
               (Env.scrape_alias env candidate))
    in
    let included_hints =
      eligible_hints
      |> List.filter (fun (_, candidate) ->
             module_type_includes env module_typ
               (Env.scrape_alias env candidate))
    in
    let* hinted_path =
      match equivalent_hints with
      | _ :: _ -> choose_hinted_path equivalent_hints
      | [] -> (
          match included_hints with
          | _ :: _ -> choose_hinted_path included_hints
          | [] -> (
              match hinted_candidates with
              | [ candidate ] -> choose_hinted_path [ candidate ]
              | [] | _ :: _ :: _ -> return None))
    in
    match hinted_path with
    | Some path -> return ([ path ], shape)
    | None ->
    let* paths, shape = find_similar_signatures_with_shape env shape in
    let equivalent_paths =
      List.filter
        (is_modtype_declaration_equivalent env module_typ)
        paths
    in
    (* A shape deliberately omits most type information, so use it only to
       collect candidates.  When compiler-libs can identify one or more
       semantically equivalent module types, discard the merely same-shaped
       candidates.  Equivalent signatures may still have different OCaml
       names; their generated records are interchangeable through the
       translator's existing module-cast construction. *)
    match equivalent_paths with
    | [] ->
        let included_paths =
          List.filter
            (is_modtype_declaration_included env module_typ)
            paths
        in
        (match included_paths with
        | _ :: _ -> return (included_paths, shape)
        | [] -> (
            match paths with
            | [] | [ _ ] -> return (paths, shape)
            | _ :: _ :: _ -> return ([], shape)))
    | _ :: _ -> return (equivalent_paths, shape)

type maybe_found = Found of Path.t | Not_found of string

(** Get the path of the signature definition of the [module_typ]
    if it is a first-class module, [None] otherwise. Optionally, when given the path of the module we want to check for its signature, to verify if it is not
    in a blacklist. *)
let rec is_module_typ_first_class_aux
    ?(include_hidden_hints = false) (module_typ : Types.module_type)
    (module_path : Path.t option) : maybe_found Monad.t =
  let* env = get_env in
  let* configuration = get_configuration in
  let* is_in_black_list =
    match module_path with
    | None -> return false
    | Some module_path ->
        let is_in_configuration_black_list =
          Configuration.is_in_first_class_module_path_backlist configuration
            module_path
        in
        let* has_black_list_attribute =
          match Env.find_module module_path env with
          | { Types.md_attributes; _ } ->
              let* attributes = Attribute.of_attributes md_attributes in
              return (Attribute.has_plain_module attributes)
          | exception _ -> return false
        in
        return (is_in_configuration_black_list || has_black_list_attribute)
  in
  if is_in_black_list then return (Not_found "In blacklist")
  else
    let scraped_module_typ = Mtype.scrape env module_typ in
    match scraped_module_typ with
    | Mty_functor _ -> return (Not_found "This is a functor type")
    | _ ->
    let* signature_hint =
      match module_path with
      | None -> return None
      | Some module_path -> get_signature_hint module_path
    in
    let* signature_hint =
      match signature_hint with
      | Some path
        when Configuration.is_in_first_class_module_signature_backlist
               configuration path ->
          return None
      | signature_hint -> return signature_hint
    in
    match signature_hint with
    | Some path -> return (Found path)
    | None ->
    match scraped_module_typ with
    | Mty_alias path -> (
        match Env.find_module path env with
        | { Types.md_type; _ } ->
            is_module_typ_first_class_aux ~include_hidden_hints md_type
              module_path
        | exception Not_found ->
            let reason = "Module " ^ Path.name path ^ " not found" in
            return (Not_found reason))
    | Mty_ident path -> (
        match (Env.find_modtype path env).mtd_type with
        | Some module_typ ->
            is_module_typ_first_class_aux ~include_hidden_hints module_typ
              module_path
        | None ->
            return
              (Not_found
                 ("Module type " ^ Path.name path ^ " is abstract"))
        | exception Not_found ->
            let* hinted_module_type = get_module_type_hint path in
            (match hinted_module_type with
            | Some module_typ ->
                is_module_typ_first_class_aux ~include_hidden_hints module_typ
                  module_path
            | None ->
                return
                  (Not_found
                     ("Module type " ^ Path.name path ^ " not found"))))
    | Mty_signature signature -> (
        find_similar_signatures ~include_hidden_hints env signature
        >>= fun (signature_paths, shape) ->
        match signature_paths with
        | [] ->
            return
              (Not_found
                 ("Did not find a module signature name for the following shape:\n"
                 ^ Pp.to_string (SignatureShape.pretty_print shape)
                 ^ "\n"
                 ^ "(a shape is a list of names of values and sub-modules)\n\n"
                 ^ "We use the concept of shape to find the name of a \
                    signature for Rocq."))
        | [ signature_path ] -> return (Found signature_path)
        | signature_path :: _ :: _ ->
            if signature_paths_are_equivalent env signature_paths then
              (* A later visible declaration is often an alias introduced to
                 avoid shadowing an earlier signature name.  Equivalent
                 aliases denote the same generated Rocq record. *)
              return
                (Found
                   (Option.value (latest_path signature_paths)
                      ~default:signature_path))
            else
              raise (Found signature_path) Module
                ("It is unclear which name this signature has. At least two \
                  similar\n" ^ "signatures found, namely:\n\n"
                ^ String.concat "\n"
                    (signature_paths
                    |> List.map (fun path -> "* " ^ Path.name path))
                ^ "\n\n"
                ^ "We were looking for a module signature name for the \
                   following shape:\n"
                ^ Pp.to_string (SignatureShape.pretty_print shape)
                ^ "\n"
                ^ "(a shape is a list of names of values and sub-modules)\n\n"
                ^ "We use the concept of shape to find the name of a signature \
                   for Rocq."))
    | Mty_functor _ -> assert false
    | Mty_for_hole -> return (Not_found "Module type hole")

type hash_index = {
  include_hidden_hints : bool;
  module_typ : Types.module_type;
  module_path : string option;
}

(** A hash to optimize the execution of the [is_module_typ_first_class]
    function. *)
module Hash = Hashtbl.Make (struct
  type t = hash_index

  let equal left right =
    Bool.equal left.include_hidden_hints right.include_hidden_hints
    && left.module_typ == right.module_typ
    && left.module_path = right.module_path

  let hash { include_hidden_hints; module_typ; module_path } =
    Hashtbl.hash
      ( include_hidden_hints,
        Hashtbl.hash_param 1 1 module_typ,
        module_path )
end)

(** Large functor bodies repeatedly expose the same expanded module types.
    Cache successful discovery as well as misses so each signature does not
    rescan the complete typing environment on every use. *)
let module_typ_first_class_hash : maybe_found Hash.t = Hash.create 64

let is_module_typ_first_class ?(include_hidden_hints = false)
    (module_typ : Types.module_type) (module_path : Path.t option) :
    maybe_found Monad.t =
  let index =
    match module_typ with
    | Mty_signature _ ->
        Some
          {
            include_hidden_hints;
            module_typ;
            module_path = Option.map Path.name module_path;
          }
    | _ -> None
  in
  match index with
  | Some index -> (
      match Hash.find_opt module_typ_first_class_hash index with
      | Some result -> return result
      | None ->
          let* result =
            is_module_typ_first_class_aux ~include_hidden_hints module_typ
              module_path
          in
          Hash.replace module_typ_first_class_hash index result;
          return result)
  | _ ->
      is_module_typ_first_class_aux ~include_hidden_hints module_typ
        module_path
