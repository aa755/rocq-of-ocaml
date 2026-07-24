(** Paths for identifiers introduced by named module includes.

    A later declaration or include may make an earlier include unnecessary in
    the emitted Rocq namespace, but expressions between the two still refer to
    the earlier include's fresh typed identifiers.  Mapping those identifiers
    back to their originating module fields preserves the lexical binding even
    when the namespace declaration itself is omitted.

    OCaml can retain an identifier from a module-type declaration in the types
    of included values instead of using the fresh identifier introduced by the
    include.  Such aliases are scoped by source location: the same abstract
    module-type identifier can be instantiated by several different modules. *)

type alias = {
  ident : Ident.t;
  target : Path.t;
  scope_start : int;
  scope_end : int;
  available_from : int;
  allow_unscoped : bool;
  use_for_path : bool;
}

type t = alias list

let empty : t = []

let find_with (include_signature_only : bool) (ident : Ident.t)
    (location : Location.t) (aliases : t) : Path.t option =
  let position = location.loc_start.pos_cnum in
  let scoped_candidates =
    aliases
    |> List.filter (fun alias ->
           (include_signature_only || alias.use_for_path)
           && Ident.same ident alias.ident
           && alias.scope_start <= position
           && position <= alias.scope_end
           && alias.available_from <= position)
    |> List.sort (fun left right ->
           let scope_size alias = alias.scope_end - alias.scope_start in
           match Int.compare (scope_size left) (scope_size right) with
           | 0 -> Int.compare right.available_from left.available_from
           | ordering -> ordering)
  in
  match scoped_candidates with
  | alias :: _ -> Some alias.target
  | [] -> (
      let targets =
        aliases
        |> List.filter_map (fun alias ->
               if
                 (include_signature_only || alias.use_for_path)
                 && alias.allow_unscoped
                 && Ident.same ident alias.ident
               then
                 Some alias.target
               else None)
        |> List.sort_uniq Path.compare
      in
      match targets with [ target ] -> Some target | _ -> None)

let find = find_with false
let find_for_signature = find_with true

let rec contains_functor_application (path : Path.t) : bool =
  match path with
  | Path.Papply _ -> true
  | Path.Pdot (parent, _) | Path.Pextra_ty (parent, _) ->
      contains_functor_application parent
  | Path.Pident _ -> false

(** Names introduced by a structure item.  This mirrors the namespace
    shadowing calculation in [Structure.of_structure]. *)
let names_declared_by_structure_item (item : Typedtree.structure_item) :
    string list =
  match item.str_desc with
  | Tstr_value (_, bindings) ->
      bindings
      |> List.concat_map (fun (binding : Typedtree.value_binding) ->
             Typedtree.pat_bound_idents binding.vb_pat)
      |> List.map Ident.name
  | Tstr_primitive { val_id; _ } -> [ Ident.name val_id ]
  | Tstr_type (_, declarations) ->
      declarations
      |> List.map (fun (declaration : Typedtree.type_declaration) ->
             Ident.name declaration.typ_id)
  | Tstr_typext extension ->
      extension.tyext_constructors
      |> List.map (fun (constructor : Typedtree.extension_constructor) ->
             Ident.name constructor.ext_id)
  | Tstr_exception constructor ->
      [ Ident.name constructor.tyexn_constructor.ext_id ]
  | Tstr_module { mb_id = Some ident; _ }
  | Tstr_modtype { mtd_id = ident; _ } ->
      [ Ident.name ident ]
  | Tstr_recmodule bindings ->
      bindings
      |> List.filter_map (fun (binding : Typedtree.module_binding) ->
             Option.map Ident.name binding.mb_id)
  | Tstr_include { incl_type; _ } ->
      incl_type |> List.map Types.signature_item_id |> List.map Ident.name
  | _ -> []

let of_typedtree (typedtree : Merlin_kernel.Mtyper.typedtree) : t =
  let aliases = ref empty in
  let add_alias ?(use_for_path = true) scope_start scope_end available_from
      allow_unscoped ident target =
    aliases :=
      {
        ident;
        target;
        scope_start;
        scope_end;
        available_from;
        allow_unscoped;
        use_for_path;
      }
      :: !aliases
  in
  let add_shadowed_include_fields scope_start scope_end
      (shadowed_names : string list)
      (declaration : Typedtree.include_declaration) : unit =
    match ModulePathAliases.module_expr_path declaration.incl_mod with
    | None -> ()
    | Some module_path when contains_functor_application module_path -> ()
    | Some module_path ->
        let available_from = declaration.incl_loc.loc_start.pos_cnum in
        let env = declaration.incl_mod.mod_env in
        let rec type_ident_of_path (path : Path.t) : Ident.t option =
          match path with
          | Path.Pident ident -> Some ident
          | Path.Pdot (parent, field) -> (
              match Env.find_module parent env with
              | { Types.md_type; _ } -> (
                  match Mtype.scrape env md_type with
                  | Types.Mty_signature signature ->
                      signature
                      |> List.find_map (function
                           | Types.Sig_type (ident, _, _, _)
                             when Ident.name ident = field ->
                               Some ident
                           | _ -> None)
                  | _ -> None)
              | exception Not_found -> None)
          | Path.Pextra_ty (parent, _) -> type_ident_of_path parent
          | Path.Papply _ -> None
        in
        let rec module_ident_of_path (path : Path.t) : Ident.t option =
          match path with
          | Path.Pident ident -> Some ident
          | Path.Pdot (parent, field) -> (
              match Env.find_module parent env with
              | { Types.md_type; _ } -> (
                  match Mtype.scrape env md_type with
                  | Types.Mty_signature signature ->
                      signature
                      |> List.find_map (function
                           | Types.Sig_module (ident, _, _, _, _)
                             when Ident.name ident = field ->
                               Some ident
                           | _ -> None)
                  | _ -> None)
              | exception Not_found -> None)
          | Path.Pextra_ty (parent, _) ->
              module_ident_of_path parent
          | Path.Papply _ -> None
        in
        let add_manifest_path_for_target field target
            (typ : Types.type_expr) : unit =
          match Types.get_desc typ with
          | Tconstr (path, _, _) -> (
              match type_ident_of_path path with
              | Some ident when Ident.name ident = field ->
                  add_alias scope_start scope_end available_from false ident
                    target
              | _ -> ())
          | _ -> ()
        in
        let type_targets =
          declaration.incl_type
          |> List.filter_map (function
               | Types.Sig_type (ident, type_declaration, _, _) ->
                   let field = Ident.name ident in
                   let target = Path.Pdot (module_path, field) in
                   add_alias scope_start scope_end available_from true ident
                     target;
                   Option.iter
                     (add_manifest_path_for_target field target)
                     type_declaration.type_manifest;
                   Some (field, target)
               | _ -> None)
        in
        let add_type_paths (typ : Types.type_expr) : unit =
          let add_type_path typ =
            match Types.get_desc typ with
            | Tconstr (path, _, _) -> (
                match type_ident_of_path path with
                | Some ident -> (
                    match List.assoc_opt (Ident.name ident) type_targets with
                    | Some target ->
                        add_alias scope_start scope_end available_from false
                          ident target
                    | None -> ())
                | None -> ())
            | _ -> ()
          in
          add_type_path typ;
          Btype.iter_type_expr add_type_path typ
        in
        declaration.incl_type
        |> List.iter (fun signature_item ->
               let ident = Types.signature_item_id signature_item in
               let field = Ident.name ident in
               (match signature_item with
               | Types.Sig_module _ ->
                   let target = Path.Pdot (module_path, field) in
                   add_alias ~use_for_path:false scope_start scope_end
                     available_from true ident target;
                   Option.iter
                     (fun source_ident ->
                       add_alias ~use_for_path:false scope_start scope_end
                         available_from true source_ident target)
                     (module_ident_of_path target)
               | _ -> ());
               (match signature_item with
               | Types.Sig_value (_, { val_type; _ }, _) ->
                   add_type_paths val_type
               | _ -> ());
               let is_type =
                 match signature_item with Types.Sig_type _ -> true | _ -> false
               in
               if
                 (not is_type)
                 && List.mem field shadowed_names
               then
                 add_alias scope_start scope_end available_from true ident
                   (Path.Pdot (module_path, field)))
  in
  let add_structure (scope_location : Location.t option)
      (structure : Typedtree.structure) : unit =
    match structure.str_items with
    | [] -> ()
    | first :: _ ->
        let last = List.hd (List.rev structure.str_items) in
        let scope_start, scope_end =
          match scope_location with
          | Some location ->
              (location.loc_start.pos_cnum, location.loc_end.pos_cnum)
          | None ->
              (first.str_loc.loc_start.pos_cnum, last.str_loc.loc_end.pos_cnum)
        in
        ignore
          (List.fold_right
             (fun (item : Typedtree.structure_item) shadowed_names ->
               (match item.str_desc with
               | Tstr_include declaration ->
                   add_shadowed_include_fields scope_start scope_end
                     shadowed_names declaration
               | _ -> ());
               List.sort_uniq String.compare
                 (names_declared_by_structure_item item @ shadowed_names))
             structure.str_items [])
  in
  let open Tast_iterator in
  let iterator =
    {
      default_iterator with
      module_expr =
        (fun self module_expr ->
          (match module_expr.mod_desc with
          | Tmod_structure structure ->
              add_structure (Some module_expr.mod_loc) structure
          | _ -> ());
          default_iterator.module_expr self module_expr);
    }
  in
  (match typedtree with
  | `Implementation structure ->
      add_structure None structure;
      iterator.structure iterator structure
  | `Interface signature -> iterator.signature iterator signature);
  !aliases
