(** Rocq declarations in one module cannot reuse a name, while OCaml permits a
    later value binding to shadow an earlier one.  Record deterministic,
    collision-free names for the hidden bindings, keyed by the compiler's
    [Ident.t], so declarations and references are renamed consistently. *)

module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

type t = string Ident.Map.t

let empty : t = Ident.Map.empty
let find (ident : Ident.t) (names : t) : string option =
  Ident.Map.find_opt ident names

let value_idents (structure : Typedtree.structure) : Ident.t list =
  structure.str_items
  |> List.concat_map (fun (item : Typedtree.structure_item) ->
         match item.str_desc with
         | Tstr_value (_, bindings) ->
             bindings
             |> List.concat_map (fun (binding : Typedtree.value_binding) ->
                    Typedtree.pat_bound_idents binding.vb_pat)
         | Tstr_primitive description -> [ description.val_id ]
         | _ -> [])

let structure_type_names (structure : Typedtree.structure) : StringSet.t =
  structure.str_items
  |> List.fold_left
       (fun names (item : Typedtree.structure_item) ->
         match item.str_desc with
         | Tstr_type (_, declarations) ->
             List.fold_left
               (fun names (declaration : Typedtree.type_declaration) ->
                 StringSet.add (Ident.name declaration.typ_id) names)
               names declarations
         | _ -> names)
       StringSet.empty

let signature_value_idents (signature : Typedtree.signature) : Ident.t list =
  signature.sig_items
  |> List.filter_map (fun (item : Typedtree.signature_item) ->
         match item.sig_desc with
         | Tsig_value description -> Some description.val_id
         | _ -> None)

let signature_type_names (signature : Typedtree.signature) : StringSet.t =
  signature.sig_items
  |> List.fold_left
       (fun names (item : Typedtree.signature_item) ->
         match item.sig_desc with
         | Tsig_type (_, declarations) | Tsig_typesubst declarations ->
             List.fold_left
               (fun names (declaration : Typedtree.type_declaration) ->
                 StringSet.add (Ident.name declaration.typ_id) names)
               names declarations
         | _ -> names)
       StringSet.empty

let counts (idents : Ident.t list) : int StringMap.t =
  List.fold_left
    (fun counts ident ->
      let name = Ident.name ident in
      let count = Option.value (StringMap.find_opt name counts) ~default:0 in
      StringMap.add name (count + 1) counts)
    StringMap.empty idents

let rec fresh_name (occupied : StringSet.t) (base : string) (index : int) :
    string =
  let candidate = base ^ "_shadow" ^ string_of_int index in
  if StringSet.mem candidate occupied then fresh_name occupied base (index + 1)
  else candidate

let rec fresh_value_name (occupied : StringSet.t) (base : string) (index : int) :
    string =
  let suffix = if index = 0 then "_value" else "_value" ^ string_of_int index in
  let candidate = base ^ suffix in
  if StringSet.mem candidate occupied then
    fresh_value_name occupied base (index + 1)
  else candidate

let rec fresh_parameter_name
    (occupied : StringSet.t) (base : string) (index : int) : string =
  let suffix =
    if index = 0 then "_parameter" else "_parameter" ^ string_of_int index
  in
  let candidate = base ^ suffix in
  if StringSet.mem candidate occupied then
    fresh_parameter_name occupied base (index + 1)
  else candidate

let rec type_variable_name (typ : Types.type_expr) : string option =
  match Types.get_desc typ with
  | Tvar (Some name) | Tunivar (Some name) -> Some name
  | Tlink typ | Tsubst (typ, _) -> type_variable_name typ
  | _ -> None

let pattern_ident :
    type kind. kind Typedtree.general_pattern -> Ident.t option =
 fun pattern ->
  match pattern.pat_desc with
  | Tpat_var (ident, _, _) -> Some ident
  | Tpat_alias (_, ident, _, _, _) -> Some ident
  | _ -> None

let add_declaration_scope (names : t) (idents : Ident.t list)
    (type_names : StringSet.t) : t =
  let remaining = ref (counts idents) in
  let indices = ref StringMap.empty in
  let occupied =
    ref
      (idents
      |> List.fold_left
           (fun names ident -> StringSet.add (Ident.name ident) names)
           type_names)
  in
  List.fold_left
    (fun names ident ->
      let original = Ident.name ident in
      let left = StringMap.find original !remaining in
      remaining := StringMap.add original (left - 1) !remaining;
      let collides_with_type = StringSet.mem original type_names in
      if left <= 1 && not collides_with_type then names
      else
        let renamed =
          if collides_with_type then fresh_value_name !occupied original 0
          else
            let index =
              Option.value (StringMap.find_opt original !indices) ~default:1
            in
            indices := StringMap.add original (index + 1) !indices;
            fresh_name !occupied original index
        in
        occupied := StringSet.add renamed !occupied;
        Ident.Map.add ident renamed names)
    names idents

let add_structure (names : t) (structure : Typedtree.structure) : t =
  add_declaration_scope names (value_idents structure)
    (structure_type_names structure)

let add_signature (names : t) (signature : Typedtree.signature) : t =
  add_declaration_scope names (signature_value_idents signature)
    (signature_type_names signature)

(** Reconstruct the deterministic value rename for a qualified [parent.field]
    path.  Compiler-libs retains only the field string in [Path.Pdot], so the
    original value [Ident.t] used by [find] is unavailable at reference sites. *)
let find_qualified (env : Env.t) (parent : Path.t) (field : string) :
    string option =
  let signature =
    match (Env.find_module parent env).Types.md_type with
    | module_type -> (
        match Env.scrape_alias env module_type with
        | Types.Mty_signature signature -> Some signature
        | _ -> None)
    | exception Not_found -> None
  in
  match signature with
  | None -> None
  | Some signature ->
      let value_names, type_names =
        List.fold_left
          (fun (value_names, type_names) item ->
            match item with
            | Types.Sig_value (ident, _, _) ->
                (StringSet.add (Ident.name ident) value_names, type_names)
            | Types.Sig_type (ident, _, _, _) ->
                (value_names, StringSet.add (Ident.name ident) type_names)
            | _ -> (value_names, type_names))
          (StringSet.empty, StringSet.empty) signature
      in
      if
        StringSet.mem field value_names
        && StringSet.mem field type_names
      then
        Some
          (fresh_value_name
             (StringSet.union value_names type_names)
             field 0)
      else
        None

(** Functor parameters become fields of the generated [FArgs] class.  That
    puts them in the same Rocq namespace as declarations in the functor body,
    although OCaml permits a body declaration to shadow a parameter:

    {[
      module F (Inner : S) = struct
        module Inner = Make (Inner)
      end
    ]}

    Return the names that the rest of a nested functor chain will declare in
    that shared generated namespace. *)
let rec generated_body_names (module_expr : Typedtree.module_expr) :
    string list =
  match module_expr.mod_desc with
  | Tmod_functor (Named (ident, _, _), body) ->
      Option.fold ~none:[] ~some:(fun ident -> [ Ident.name ident ]) ident
      @ generated_body_names body
  | Tmod_functor (Unit, body) -> generated_body_names body
  | Tmod_constraint (inner, _, _, _) -> generated_body_names inner
  | Tmod_structure structure ->
      structure.str_items
      |> List.concat_map (fun (item : Typedtree.structure_item) ->
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
                 incl_type
                 |> List.map Types.signature_item_id
                 |> List.map Ident.name
             | _ -> [])
  | Tmod_ident _
  | Tmod_apply _
  | Tmod_apply_unit _
  | Tmod_unpack _
  | Tmod_typed_hole ->
      []

let of_typedtree (typedtree : Merlin_kernel.Mtyper.typedtree) : t =
  let names = ref empty in
  let occupied = ref StringSet.empty in
  let open Tast_iterator in
  let collect_names =
    {
      default_iterator with
      module_binding =
        (fun self binding ->
          Option.iter
            (fun ident ->
              occupied := StringSet.add (Ident.name ident) !occupied)
            binding.mb_id;
          default_iterator.module_binding self binding);
      module_expr =
        (fun self module_expr ->
          (match module_expr.mod_desc with
          | Tmod_functor (Named (Some ident, _, _), _) ->
              occupied := StringSet.add (Ident.name ident) !occupied
          | _ -> ());
          default_iterator.module_expr self module_expr);
      pat =
        (fun (type kind) self
             (pattern : kind Typedtree.general_pattern) ->
          Typedtree.pat_bound_idents pattern
          |> List.iter (fun ident ->
                 occupied := StringSet.add (Ident.name ident) !occupied);
          default_iterator.pat self pattern);
    }
  in
  (match typedtree with
  | `Implementation structure ->
      collect_names.structure collect_names structure
  | `Interface signature -> collect_names.signature collect_names signature);
  let iterator =
    {
      default_iterator with
      structure =
        (fun self structure ->
          names := add_structure !names structure;
          default_iterator.structure self structure);
      signature =
        (fun self signature ->
          names := add_signature !names signature;
          default_iterator.signature self signature);
      module_expr =
        (fun self module_expr ->
          (match module_expr.mod_desc with
          | Tmod_functor (Named (Some ident, _, _), body)
            when List.mem (Ident.name ident) (generated_body_names body) ->
              let renamed =
                fresh_parameter_name !occupied (Ident.name ident) 0
              in
              occupied := StringSet.add renamed !occupied;
              names := Ident.Map.add ident renamed !names
          | _ -> ());
          default_iterator.module_expr self module_expr);
      pat =
        (fun (type kind) self
             (pattern : kind Typedtree.general_pattern) ->
          (match (pattern_ident pattern, type_variable_name pattern.pat_type) with
          | Some ident, Some type_name
            when String.equal (Ident.name ident) type_name
                 && not (Ident.Map.mem ident !names) ->
              let renamed = fresh_value_name !occupied type_name 0 in
              occupied := StringSet.add renamed !occupied;
              names := Ident.Map.add ident renamed !names
          | _ -> ());
          default_iterator.pat self pattern);
    }
  in
  (match typedtree with
  | `Implementation structure -> iterator.structure iterator structure
  | `Interface signature -> iterator.signature iterator signature);
  !names
