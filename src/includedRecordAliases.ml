(** Record projections for names imported from functor applications.

    A later declaration may shadow a name imported by [include].  The
    generated namespace must omit that imported declaration to avoid a Rocq
    name collision, but the later declaration's right-hand side can still
    refer to the old OCaml identifier.  When the include is a translated
    functor application, that old identifier lives in the generated result
    record rather than in a Rocq module namespace. *)

type alias = {
  ident : Ident.t;
  target : IncludedRecordAliasTarget.t;
  scope_start : int;
  scope_end : int;
  available_from : int;
}

type t = alias list

let empty : t = []

let find (ident : Ident.t) (location : Location.t) (aliases : t) :
    IncludedRecordAliasTarget.t option =
  let position = location.loc_start.pos_cnum in
  aliases
  |> List.filter (fun alias ->
         Ident.same ident alias.ident
         && alias.scope_start <= position
         && position <= alias.scope_end
         && alias.available_from <= position)
  |> List.sort (fun left right ->
         let scope_size alias = alias.scope_end - alias.scope_start in
         match Int.compare (scope_size left) (scope_size right) with
         | 0 -> Int.compare right.available_from left.available_from
         | ordering -> ordering)
  |> List.find_map (fun alias -> Some alias.target)

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

let of_typedtree (typedtree : Merlin_kernel.Mtyper.typedtree)
    (signature_hints : SignatureHints.t) : t =
  let aliases = ref empty in
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
               | Tstr_include declaration -> (
                   match applied_functor_path declaration.incl_mod with
                   | Some functor_path -> (
                       let signature_path =
                         match
                           SignatureHints.find_functor_result_signature
                             functor_path signature_hints
                         with
                         | Some signature_path -> signature_path
                         | None ->
                             Path.Pdot
                               ( functor_path,
                                 Path.last functor_path ^ "_result" )
                       in
                       declaration.incl_type
                       |> List.iter (fun signature_item ->
                              let ident =
                                Types.signature_item_id signature_item
                              in
                              let field = Ident.name ident in
                              if List.mem field shadowed_names then
                                aliases :=
                                  {
                                    ident;
                                    target =
                                      {
                                        functor_path;
                                        signature_path;
                                        fields = [ field ];
                                      };
                                    scope_start;
                                    scope_end;
                                    available_from =
                                      declaration.incl_loc.loc_start.pos_cnum;
                                  }
                                  :: !aliases))
                   | None -> ())
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
