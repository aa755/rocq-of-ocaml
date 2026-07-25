open Typedtree
(** A structure represents the contents of a ".ml" file. *)

open SmartPrint
open Monad.Notations

(** A value is a toplevel definition made with a "let". *)
module Value = struct
  type t = {
    use_unsafe_fixpoints : bool;
    definition : Exp.t option Exp.Definition.t;
  }

  let concrete_assumptions ({ definition; _ } : t) =
    definition.Exp.Definition.cases
    |> List.concat_map (fun (_, body) ->
           match body with
           | None -> []
           | Some body -> Exp.concrete_assumption_requirements body)
    |> Exp.sort_uniq_assumptions

  let to_coq_typ_vars (header : Exp.Header.t) : SmartPrint.t =
    let { Exp.Header.typ_vars; _ } = header in
    Type.typ_vars_to_coq braces empty empty typ_vars

  let to_coq_args (header : Exp.Header.t) : SmartPrint.t =
    let { Exp.Header.args; _ } = header in
    group
      (Exp.Header.to_coq_instance_args header
      ^^ separate space
         (args
         |> List.map (fun (x, t) ->
                parens
                @@ nest (Name.to_coq x ^^ !^":" ^^ Type.to_coq None None t))))

  let to_coq_notation_synonym (name : Name.t) (typ_vars : VarEnv.t) :
      SmartPrint.t =
    nest
      (!^"let" ^^ Name.to_coq name
      ^^ Name.to_coq_list_or_empty (List.map fst typ_vars) braces
      ^^ !^":=" ^^ !^"'" ^-^ Name.to_coq name
      ^^ separate space (List.map Name.to_coq (List.map fst typ_vars))
      ^^ !^"in" ^^ newline)

  (** Pretty-print a value definition to Rocq. *)
  let to_coq (fargs : FArgs.t) (value : t) : SmartPrint.t =
    let { use_unsafe_fixpoints; definition } = value in
    match definition.Exp.Definition.cases with
    | [] -> empty
    | _ :: _ ->
        let axiom_cases, notation_cases, cases =
          List.fold_right
            (fun case (axiom_cases, notation_cases, cases) ->
              match case with
              | header, None -> (header :: axiom_cases, notation_cases, cases)
              | header, Some e ->
                  if header.Exp.Header.is_notation then
                    (axiom_cases, (header, e) :: notation_cases, cases)
                  else (axiom_cases, notation_cases, (header, e) :: cases))
            definition.Exp.Definition.cases ([], [], [])
        in
        let concrete_assumptions = concrete_assumptions value in
        let definition_name =
          match definition.Exp.Definition.cases with
          | (header, _) :: _ -> Name.to_string header.Exp.Header.name
          | [] -> "value"
        in
        let use_assumption_section =
          concrete_assumptions <> [] && Option.is_some fargs
        in
        let definition_fargs =
          if use_assumption_section then None else fargs
        in
        let definition_type typ =
          if use_assumption_section then
            !^"RocqOfOCaml.Basics.with_context" ^^ !^"_fargs"
            ^^ parens (Type.to_coq None None typ)
          else Type.to_coq None None typ
        in
        let assumption_declarations =
          concrete_assumptions
          |> List.mapi (fun index requirement ->
                 let instance_name =
                   Printf.sprintf "_rocq_assumption_%s_%d" definition_name
                     index
                 in
                 nest
                   (!^"#[local] Instance" ^^ !^instance_name
                  ^^ FArgs.to_coq definition_fargs ^^ !^":"
                  ^^ Type.to_coq None None
                       (Exp.assumption_class_type requirement)
                  ^-^ !^"." ^^ newline ^^ !^"Admitted."))
        in
        let rendered_definitions =
          ((* The axiomatized definitions *)
           (axiom_cases
           |> List.map (fun header ->
                  let { Exp.Header.name; typ_vars; typ; _ } = header in
                  nest
                    (!^"Axiom" ^^ Name.to_coq name ^^ !^":"
                    ^^ (match definition_fargs with
                       | Some _ ->
                           !^"forall" ^^ FArgs.to_coq definition_fargs
                           ^-^ !^","
                       | None -> empty)
                    ^^ Type.typ_vars_to_coq braces !^"forall" !^"," typ_vars
                    ^^ definition_type typ ^-^ !^".")))
          (* Reserve the notation keywords *)
          @ (match notation_cases with
            | [] -> []
            | _ :: _ ->
                [
                  separate newline
                    (notation_cases
                    |> List.map (fun (header, _) ->
                           let { Exp.Header.name; _ } = header in
                           nest
                             (!^"Reserved Notation"
                             ^^ double_quotes (!^"'" ^-^ Name.to_coq name)
                             ^-^ !^".")));
                ])
          (* The definitions *)
          @ (cases
            |> List.mapi (fun index (header, e) ->
                   let first_case = index = 0 in
                   let last_case =
                     if not definition.Exp.Definition.is_rec then true
                     else
                       match notation_cases with
                       | [] -> index = List.length cases - 1
                       | _ :: _ -> false
                   in
                   let free_vars_of_e = Exp.get_free_vars e in
                   nest
                     ((if not definition.Exp.Definition.is_rec then
                       !^"Definition"
                      else if first_case then
                       (if use_unsafe_fixpoints then
                        !^"#[bypass_check(guard)]" ^^ newline
                       else empty)
                       ^^
                       if definition.Exp.Definition.is_rec then !^"Fixpoint"
                       else !^"Definition"
                      else !^"with")
                     ^^
                     let { Exp.Header.name; typ; _ } = header in
                     Name.to_coq name ^^ FArgs.to_coq definition_fargs
                     ^^ to_coq_typ_vars header ^^ to_coq_args header
                     ^^ Exp.Header.to_coq_structs header
                     ^^ !^": " ^-^ definition_type typ ^-^ !^" :="
                     ^^ group
                          (separate space
                             (notation_cases
                             |> List.map (fun (header, _) ->
                                    let { Exp.Header.name; typ_vars; _ } =
                                      header
                                    in
                                    if Name.Set.mem name free_vars_of_e then
                                      to_coq_notation_synonym name typ_vars
                                    else empty))
                          ^^ Exp.to_coq false e)
                     ^-^ if last_case then !^"." else empty)))
          (* Define the notations *)
          @ snd
              (List.fold_left
                 (fun ((index, previous_notations), definitions) (header, e) ->
                   let first_case = index = 0 in
                   let last_case = index = List.length notation_cases - 1 in
                   let { Exp.Header.name; typ_vars; structs; typ; _ } =
                     header
                   in
                   let free_vars_of_e = Exp.get_free_vars e in
                   let definition =
                     nest
                       ((if first_case then !^"where" else !^"and")
                       ^^ double_quotes (!^"'" ^-^ Name.to_coq name)
                       ^^ !^":="
                       ^^ parens
                            (nest
                               (nest
                                  (Type.typ_vars_to_coq parens !^"fun" !^" => "
                                     typ_vars
                                  ^-^ (match structs with
                                      | [] -> !^"fun"
                                      | _ :: _ -> !^"fix" ^^ Name.to_coq name)
                                  ^^ to_coq_args header
                                  ^^ (match structs with
                                     | [] -> !^"=>"
                                     | _ :: _ ->
                                         Exp.Header.to_coq_structs header
                                         ^^ !^": " ^-^ definition_type typ
                                         ^-^ !^" :=")
                                  ^^ group
                                       (separate space
                                          (previous_notations
                                          |> List.map (fun (name, typ_vars) ->
                                                 if
                                                   Name.Set.mem name
                                                     free_vars_of_e
                                                 then
                                                   to_coq_notation_synonym name
                                                     typ_vars
                                                 else empty))
                                       ^^ Exp.to_coq false e))))
                       ^-^ if last_case then !^"." else empty)
                   in
                   ( (index + 1, previous_notations @ [ (name, typ_vars) ]),
                     definitions @ [ definition ] ))
                 ((0, []), [])
                 notation_cases)
          @
          (* Wrap the notations into definitions *)
          match notation_cases with
          | [] -> []
          | _ :: _ ->
              [
                separate newline
                  (notation_cases
                  |> List.map (fun (header, _) ->
                         let { Exp.Header.name; typ_vars; _ } = header in
                         nest
                           (!^"Definition" ^^ Name.to_coq name
                           ^^ Type.typ_vars_to_coq braces empty empty typ_vars
                           ^^ !^":="
                           ^^ separate space
                                ((!^"'" ^-^ Name.to_coq name)
                                :: List.map Name.to_coq (List.map fst typ_vars)
                                )
                           ^-^ !^".")));
              ])
        in
        let rendered =
          separate (newline ^^ newline)
            (assumption_declarations @ rendered_definitions)
        in
        if not use_assumption_section then rendered
        else
          let section_name =
            "_rocq_assumptions_" ^ definition_name
          in
          !^"Section" ^^ !^section_name ^-^ !^"." ^^ newline
          ^^ indent
               (nest
                  (!^"Context" ^^ FArgs.to_coq fargs ^-^ !^".")
               ^^ newline ^^ newline ^^ rendered)
          ^^ newline ^^ !^"End" ^^ !^section_name ^-^ !^"."
end

type functor_parameters =
  ModuleTyp.free_vars
  * (Name.t * Type.t) list
  * (Name.t * Signature.t) list

type module_include_item_kind =
  | IncludeValue
  | IncludeProjectedValue
  | IncludeType

(** A structure. *)
type t =
  | Value of Value.t
  | AbstractValue of Name.t * Name.t list * Type.t
  | TypeDefinition of TypeDefinition.t
  | Module of
      Name.t * functor_parameters * t list * (Exp.t * Type.t option) option
  | ModuleExpression of
      Name.t
      * Type.t option
      * (Name.t * Exp.t) option
      * Exp.t
  | ModuleInclude of PathName.t
  | ModuleIncludeItem of
      module_include_item_kind
      * Name.t
      * Name.t list
      * Type.t option
      * MixedPath.t
      * Exp.assumption_requirement list
  | TypeSynonym of Name.t * Type.t
  | ModuleSynonym of Name.t * PathName.t * bool
  | Signature of Name.t * Signature.t
  | SignatureSynonym of Name.t * PathName.t * int
  | Documentation of string * t list
  | Error of string
  | ErrorMessage of string * t

let value_defines (name : Name.t) ({ Value.definition; _ } : Value.t) : bool =
  definition.Exp.Definition.cases
  |> List.exists (fun (header, _) ->
         Name.equal header.Exp.Header.name name)

let module_include_assumptions kind typ_vars typ mixed_path =
  match (kind, typ) with
  | (IncludeValue | IncludeProjectedValue), Some typ
    when
      Exp.is_partial_operation_name (MixedPath.to_string mixed_path)
      || Exp.is_partial_operation_field_name
           (MixedPath.to_string mixed_path) ->
      [ (Exp.Unreachable, Type.arrow_result typ) ]
  | (IncludeValue | IncludeProjectedValue), Some typ
    when
      Exp.is_generated_map_of_yojson_name
        (MixedPath.to_string mixed_path) ->
      let element_requirement =
        match typ_vars with
        | element :: _ ->
            [ (Exp.Unreachable, Type.Variable element) ]
        | [] -> []
      in
      element_requirement
      @ [ (Exp.Unreachable, Type.arrow_result typ) ]
      |> Exp.sort_uniq_assumptions
  | _ -> []

(** Propagate generated assumption parameters through calls between values in
    the same OCaml structure.  The pass reaches a fixed point because adding a
    requirement to one value may make its callers require the same
    type-specific class. *)
let propagate_assumption_calls (definitions : t list) : t list =
  let merge_specs left right =
    Name.Map.union (fun _ _ right -> Some right) left right
  in
  let rec specs_of_definitions definitions =
    definitions
    |> List.fold_left
         (fun specs definition ->
           match definition with
           | Value { Value.definition; _ } ->
               merge_specs specs
                 (Exp.assumption_call_specs_of_definition definition)
           | ModuleIncludeItem
               (kind, name, typ_vars, typ, mixed_path, stored_requirements) -> (
               let requirements =
                 match stored_requirements with
                 | _ :: _ -> stored_requirements
                 | [] ->
                     module_include_assumptions kind typ_vars typ mixed_path
               in
               match requirements with
               | [] -> specs
               | (_, first_required_type) :: _ ->
                   let result_typ =
                     match typ with
                     | Some typ -> Type.arrow_result typ
                     | None -> first_required_type
                   in
                   Name.Map.add name
                     {
                       Exp.result_typ;
                       requirements;
                     }
                     specs)
           | Signature (_, signature) ->
               merge_specs specs
                 (Signature.assumption_call_specs signature)
           | Module (module_name, _, nested, _) ->
               let nested_specs = specs_of_definitions nested in
               Name.Map.fold
                 (fun nested_name spec specs ->
                   Name.Map.add
                     (Name.of_string_raw
                        (Name.to_string module_name ^ "_"
                       ^ Name.to_string nested_name))
                     spec specs)
                 nested_specs specs
           | Documentation (_, nested)
           | ErrorMessage (_, Documentation (_, nested)) ->
               merge_specs specs (specs_of_definitions nested)
           | ErrorMessage (_, nested) ->
               merge_specs specs (specs_of_definitions [ nested ])
           | _ -> specs)
         Name.Map.empty
  in
  let rec transform specs definition =
    match definition with
    | Value value ->
        Value
          {
            value with
            Value.definition =
              Exp.propagate_definition_call_assumptions specs
                value.Value.definition;
          }
    | Module (name, parameters, nested, expression) ->
        Module
          ( name,
            parameters,
            fixed_point nested,
            expression )
    | Documentation (text, nested) ->
        Documentation (text, List.map (transform specs) nested)
    | ErrorMessage (message, nested) ->
        ErrorMessage (message, transform specs nested)
    | definition -> definition
  and fixed_point definitions =
    let before = specs_of_definitions definitions in
    let transformed = List.map (transform before) definitions in
    let after = specs_of_definitions transformed in
    if
      Name.Map.equal
        (fun left right -> compare left right = 0)
        before after
    then transformed
    else fixed_point transformed
  in
  let rec update_signatures_scope definitions =
    let specs = specs_of_definitions definitions in
    List.map (update_signature_definition specs) definitions
  and update_signature_definition specs = function
    | Module (name, parameters, nested, expression) ->
        Module
          ( name,
            parameters,
            update_signatures_scope nested,
            expression )
    | Signature (name, signature) ->
        Signature
          (name, Signature.add_assumption_requirements specs signature)
    | Documentation (text, nested) ->
        Documentation
          (text, List.map (update_signature_definition specs) nested)
    | ErrorMessage (message, nested) ->
        ErrorMessage
          (message, update_signature_definition specs nested)
    | definition -> definition
  in
  let normalize_projection_path path =
    path |> String.to_seq
    |> Seq.filter (fun character -> character <> '(' && character <> ')')
    |> String.of_seq
  in
  let qualified_path_contains value substring =
    let value_length = String.length value in
    let substring_length = String.length substring in
    let rec search index =
      if index + substring_length > value_length then false
      else
        let preceding_boundary =
          index = 0 || value.[index - 1] = '.'
        in
        let end_index = index + substring_length in
        let following_boundary =
          end_index = value_length || value.[end_index] = '.'
        in
        if
          preceding_boundary
          && following_boundary
          && String.sub value index substring_length = substring
        then true
        else search (index + 1)
    in
    substring_length = 0 || search 0
  in
  let rec qualified_signature_specs prefix definitions =
    definitions
    |> List.concat_map (function
         | Module (name, _, nested, _) ->
             qualified_signature_specs
               (prefix @ [ Name.to_string name ])
               nested
         | Signature (name, signature) ->
             Signature.assumption_call_specs signature
             |> Name.Map.bindings
             |> List.map (fun (field, spec) ->
                    ( String.concat "."
                        (prefix
                        @ [ Name.to_string name; Name.to_string field ]),
                      spec ))
         | Documentation (_, nested) ->
             qualified_signature_specs prefix nested
         | ErrorMessage (_, nested) ->
             qualified_signature_specs prefix [ nested ]
         | _ -> [])
  in
  let find_projected_spec qualified_specs mixed_path =
    let target =
      normalize_projection_path (MixedPath.to_string mixed_path)
    in
    let generated_signature_suffix path =
      match List.rev (String.split_on_char '.' path) with
      | field :: signature :: _
        when String.ends_with ~suffix:"_signature" signature ->
          Some (signature ^ "." ^ field)
      | _ -> None
    in
    qualified_specs
    |> List.filter_map (fun (path, spec) ->
           if qualified_path_contains target path then
             Some (2, String.length path, spec)
           else
             match generated_signature_suffix path with
             | Some suffix
               when qualified_path_contains target suffix ->
                 Some (1, String.length suffix, spec)
             | Some _ | None -> None)
    |> List.sort (fun (left_kind, left_length, _)
                         (right_kind, right_length, _) ->
           match Int.compare right_kind left_kind with
           | 0 -> Int.compare right_length left_length
           | comparison -> comparison)
    |> List.find_map (fun (_, _, spec) -> Some spec)
  in
  let instantiate_requirements typ
      ({ Exp.result_typ = declared_result; requirements } :
        Exp.assumption_call_spec) =
    match typ with
    | None -> requirements
    | Some typ ->
        let actual_result = Type.arrow_result typ in
        let substitutions =
          match
            Type.match_variables ~relaxed_constructors:true
              declared_result actual_result
          with
          | Some substitutions -> substitutions
          | None -> []
        in
        requirements
        |> List.map (fun (kind, required_typ) ->
               ( kind,
                 if compare required_typ declared_result = 0 then
                   actual_result
                 else
                   Type.subst_variables substitutions required_typ ))
        |> Exp.sort_uniq_assumptions
  in
  let rec annotate_projected_requirements qualified_specs definitions =
    definitions
    |> List.map (function
         | ModuleIncludeItem
             (kind, name, typ_vars, typ, mixed_path, []) ->
             let requirements =
               match find_projected_spec qualified_specs mixed_path with
               | None -> []
               | Some spec -> instantiate_requirements typ spec
             in
             ModuleIncludeItem
               (kind, name, typ_vars, typ, mixed_path, requirements)
         | Module (name, parameters, nested, expression) ->
             Module
               ( name,
                 parameters,
                 annotate_projected_requirements qualified_specs nested,
                 expression )
         | Documentation (text, nested) ->
             Documentation
               ( text,
                 annotate_projected_requirements qualified_specs nested )
         | ErrorMessage (message, nested) ->
             let nested =
               match
                 annotate_projected_requirements qualified_specs [ nested ]
               with
               | nested :: _ -> nested
               | [] -> nested
             in
             ErrorMessage (message, nested)
         | definition -> definition)
  in
  let rec close_assumptions definitions =
    let updated =
      definitions |> fixed_point |> update_signatures_scope
    in
    let qualified_specs = qualified_signature_specs [] updated in
    let updated =
      annotate_projected_requirements qualified_specs updated
    in
    if compare definitions updated = 0 then updated
    else close_assumptions updated
  in
  let rec finalize_scope definitions =
    let specs = specs_of_definitions definitions in
    List.map (finalize_definition specs) definitions
  and finalize_definition specs definition =
    match definition with
    | Value value ->
        let definition =
          {
            value.Value.definition with
            Exp.Definition.cases =
              value.Value.definition.Exp.Definition.cases
              |> List.map (fun (header, body) ->
                     ( header,
                       Option.map
                         (Exp.add_root_record_field_assumption_arities specs)
                         body ));
          }
        in
        Value { value with Value.definition }
    | Module (name, parameters, nested, expression) ->
        let nested = finalize_scope nested in
        let nested_specs = specs_of_definitions nested in
        let expression =
          Option.map
            (fun (body, typ) ->
              ( Exp.add_root_record_field_assumption_arities nested_specs body,
                typ ))
            expression
        in
        Module (name, parameters, nested, expression)
    | ModuleExpression (name, typ, fargs, expression) ->
        ModuleExpression
          ( name,
            typ,
            fargs,
            Exp.add_root_record_field_assumption_arities specs expression )
    | Documentation (text, nested) ->
        Documentation
          (text, List.map (finalize_definition specs) nested)
    | ErrorMessage (message, nested) ->
        ErrorMessage (message, finalize_definition specs nested)
    | definition -> definition
  in
  definitions |> close_assumptions |> finalize_scope

(** Whether the definition reached by a local access is printed with the
    enclosing functor's [_fargs] parameter. *)
let local_access_uses_fargs (definitions : t list) (access : Name.t list) :
    bool =
  let rec search definitions access =
    match access with
    | [] -> false
    | name :: fields ->
        let rec search_definitions = function
          | [] -> false
          | Documentation (_, definitions) :: remaining
          | ErrorMessage (_, Documentation (_, definitions)) :: remaining ->
              if search definitions access then true
              else search_definitions remaining
          | ErrorMessage (_, definition) :: remaining ->
              if search [ definition ] access then true
              else search_definitions remaining
          | Value value :: _
            when fields = [] && value_defines name value ->
              true
          | ModuleIncludeItem (_, field, _, _, _, _) :: _
            when fields = [] && Name.equal name field ->
              true
          | ModuleExpression (module_name, _, _, _) :: _
            when Name.equal name module_name ->
              true
          | Module (module_name, _, definitions, expression) :: _
            when Name.equal name module_name ->
              if fields = [] then Option.is_some expression
              else search definitions fields
          | _ :: remaining -> search_definitions remaining
        in
        search_definitions definitions
  in
  match access with
  | [ _ ] -> true
  | _ -> search definitions access

let error_message (structure : t) (category : Error.Category.t)
    (message : string) : t list Monad.t =
  raise [ ErrorMessage (message, structure) ] category message

let wrap_documentation (items : t list Monad.t) : t list Monad.t =
  let* documentation = get_documentation in
  match documentation with
  | None -> items
  | Some documentation ->
      let* items = items in
      return [ Documentation (documentation, items) ]

let top_level_evaluation (e : expression) : t list Monad.t =
  push_env
    (let* e = Exp.of_expression Name.Map.empty e in
     let header =
       {
         Exp.Header.name = Name.of_string_raw "init_module";
         typ_vars = [];
         args = [];
         instance_args = [];
         structs = [];
         typ = Type.Apply (MixedPath.of_name (Name.of_string_raw "unit"), []);
         is_notation = false;
       }
     in
     let definition =
       Exp.add_assumption_instance_args
         { Exp.Definition.is_rec = false; cases = [ (header, Some e) ] }
     in
     let documentation = "Init function; without side-effects in Rocq" in
     return
       [
         Documentation
           ( documentation,
             [
               Value
                 {
                   use_unsafe_fixpoints = false;
                   definition;
                 };
             ] );
       ])

let typ_definitions_of_typ_extension_raw (typ_extension : extension_constructor)
    : TypeDefinition.t list Monad.t =
  let { ext_id; ext_type = { ext_args; _ }; _ } = typ_extension in
  let* name = Name.of_ident false ext_id in
  match ext_args with
  | Types.Cstr_tuple _ -> return []
  | Cstr_record labels ->
      let* fields =
        labels
        |> Monad.List.map (fun { Types.ld_id; ld_type; _ } ->
               let* name = Name.of_ident false ld_id in
               let* typ = Type.of_type_expr_without_free_vars ld_type in
               return (name, typ))
      in
      return [ TypeDefinition.Record (name, [], fields, true) ]

let typ_definitions_of_typ_extension (typ_extension : extension_constructor) :
    t list Monad.t =
  let* typ_definitions = typ_definitions_of_typ_extension_raw typ_extension in
  return
    (typ_definitions
    |> List.map (fun typ_definition -> TypeDefinition typ_definition))

let rec kind_of_signature (module_typ : Typedtree.module_type) : string =
  match module_typ.mty_desc with
  | Tmty_alias _ -> "alias"
  | Tmty_ident _ -> "ident"
  | Tmty_signature _ -> "signature"
  | Tmty_functor _ -> "functor"
  | Tmty_with (module_typ, _) -> kind_of_signature module_typ
  | Tmty_typeof _ -> "typeof"

let rec applied_functor_root_path (module_expr : Typedtree.module_expr) :
    Path.t option =
  match module_expr.mod_desc with
  | Tmod_ident (path, _) -> Some path
  | Tmod_apply (functor_expr, _, _)
  | Tmod_apply_unit functor_expr
  | Tmod_constraint (functor_expr, _, _, _) ->
      applied_functor_root_path functor_expr
  | Tmod_structure _
  | Tmod_functor _
  | Tmod_unpack _
  | Tmod_typed_hole ->
      None

let applicative_include_alias (module_expr : Typedtree.module_expr) :
    (Path.t * Path.t) option Monad.t =
  match ModulePathAliases.module_expr_path module_expr with
  | Some (Path.Papply _ as source_path) ->
      let* include_name = Exp.get_include_name module_expr in
      let target_path =
        Path.Pident (Ident.create_local (Name.to_string include_name))
      in
      return (Some (source_path, target_path))
  | _ -> return None

let has_raw_attribute (name : string) (attributes : Parsetree.attributes) :
    bool =
  List.exists
    (fun ({ Parsetree.attr_name = { txt; _ }; _ } : Parsetree.attribute) ->
      String.equal txt name)
    attributes

let rec explicit_module_type (module_expr : Typedtree.module_expr) :
    Typedtree.module_type option =
  match module_expr.mod_desc with
  | Tmod_constraint (_, _, Tmodtype_explicit module_type, _) ->
      Some module_type
  | Tmod_constraint (module_expr, _, Tmodtype_implicit, _) ->
      explicit_module_type module_expr
  | _ -> None

let tuple_type (types : Type.t list) : Type.t =
  match types with
  | [ typ ] -> typ
  | _ -> Type.Tuple types

let tuple_expression (expressions : Exp.t list) : Exp.t =
  match expressions with
  | [ expression ] -> expression
  | _ -> Exp.Tuple expressions

let apply_projection (projection : MixedPath.t) (expression : Exp.t) : Exp.t =
  Exp.Apply (Exp.Variable (projection, []), [ Some expression ])

let rec tuple_projection (index : int) (count : int) (tuple : Exp.t) : Exp.t =
  if count <= 1 then tuple
  else if index = 0 then
    apply_projection
      (MixedPath.of_name (Name.of_string_raw "fst"))
      tuple
  else
    tuple_projection (index - 1) (count - 1)
      (apply_projection
         (MixedPath.of_name (Name.of_string_raw "snd"))
         tuple)

(** Translate an OCaml recursive-module group as one reducible tuple fixed
    point.  The local names bound while constructing the tuple make each module
    expression refer to the other components of the same knot. *)
let recursive_module_definitions
    (bindings : Typedtree.module_binding list) : t list Monad.t =
  let* bindings =
    bindings
    |> Monad.List.map (fun binding ->
           let* name = Name.of_optional_ident false binding.mb_id in
           let* module_type =
             match explicit_module_type binding.mb_expr with
             | Some module_type -> ModuleTyp.of_ocaml module_type
             | None -> ModuleTyp.of_types binding.mb_expr.mod_type
           in
           let* _, typ =
             ModuleTyp.to_typ [] (Name.to_string name) true module_type
           in
           let* expression =
             Exp.of_module_expr Name.Map.empty binding.mb_expr
               (Some binding.mb_expr.mod_type)
           in
           return (name, typ, expression))
  in
  match bindings with
  | [] -> return []
  | _ :: _ ->
      let names, types, expressions =
        List.fold_right
          (fun (name, typ, expression) (names, types, expressions) ->
            (name :: names, typ :: types, expression :: expressions))
          bindings ([], [], [])
      in
      let knot_name =
        Name.of_string_raw
          ("_recursive_modules_"
          ^ String.concat "_" (List.map Name.to_string names))
      in
      let knot_parameter = Name.of_string_raw "_recursive_modules" in
      let knot_variable =
        Exp.Variable (MixedPath.of_name knot_parameter, [])
      in
      let count = List.length bindings in
      let recursive_values =
        List.mapi
          (fun index name ->
            (name, tuple_projection index count knot_variable))
          names
      in
      let body =
        List.fold_right
          (fun (name, value) body ->
            Exp.LetVar (None, name, [], value, body))
          recursive_values (tuple_expression expressions)
      in
      let knot_typ = tuple_type types in
      let knot_function = Exp.Function (knot_parameter, Some knot_typ, body) in
      let knot_expression =
        Exp.Apply
          ( Exp.Variable
              ( MixedPath.of_name
                  (Name.of_string_raw "recursive_module_fix"),
                [] ),
            [ Some knot_function ] )
      in
      let knot_definition =
        ModuleExpression
          (knot_name, Some knot_typ, None, knot_expression)
      in
      let knot_value = Exp.Variable (MixedPath.of_name knot_name, []) in
      let module_definitions =
        List.mapi
          (fun index (name, typ, _) ->
            ModuleExpression
              ( name,
                Some typ,
                None,
                tuple_projection index count knot_value ))
          bindings
      in
      return (knot_definition :: module_definitions)

(** Names declared after an [include] shadow imported names in OCaml.  Rocq's
    [Include] instead rejects a later declaration with the same name, so the
    translation must omit those names from a namespace include. *)
let names_declared_by_structure_item (item : structure_item) : string list =
  match item.str_desc with
  | Tstr_value (_, bindings) ->
      bindings
      |> List.concat_map (fun binding ->
             Typedtree.pat_bound_idents binding.vb_pat)
      |> List.map Ident.name
  | Tstr_primitive { val_id; _ } -> [ Ident.name val_id ]
  | Tstr_type (_, declarations) ->
      declarations |> List.map (fun declaration -> Ident.name declaration.typ_id)
  | Tstr_typext extension ->
      extension.tyext_constructors
      |> List.map (fun constructor -> Ident.name constructor.ext_id)
  | Tstr_exception constructor -> [ Ident.name constructor.tyexn_constructor.ext_id ]
  | Tstr_module { mb_id = Some ident; _ }
  | Tstr_modtype { mtd_id = ident; _ } ->
      [ Ident.name ident ]
  | Tstr_recmodule bindings ->
      bindings
      |> List.filter_map (fun binding ->
             Option.map Ident.name binding.mb_id)
  | Tstr_include { incl_type; _ } ->
      incl_type |> List.map Types.signature_item_id |> List.map Ident.name
  | _ -> []

(** A synthesized result signature may record a nested field signature using a
    path local to the owning functor.  Qualify that path before emitting record
    projections unless it already resolves independently. *)
let qualify_result_field_signature (env : Env.t) (result_signature : Path.t)
    (field_signature : Path.t) : Path.t =
  let rec append_path prefix = function
    | Path.Pident ident -> Path.Pdot (prefix, Ident.name ident)
    | Path.Pdot (parent, field) ->
        Path.Pdot (append_path prefix parent, field)
    | Path.Pextra_ty (parent, extra) ->
        Path.Pextra_ty (append_path prefix parent, extra)
    | Path.Papply _ as path -> path
  in
  let head = Path.head field_signature in
  let head_is_resolvable =
    match Env.find_module (Path.Pident head) env with
    | _ -> true
    | exception Not_found -> false
  in
  if Ident.global head || Ident.is_predef head || head_is_resolvable then
    field_signature
  else
    match result_signature with
    | Path.Pdot (owner, result_name)
      when String.ends_with ~suffix:"_result" result_name ->
        append_path owner field_signature
    | _ -> field_signature

let signature_item_named (name : string) (signature : Types.signature) :
    Types.signature_item option =
  signature
  |> List.find_opt (fun item ->
         String.equal (Ident.name (Types.signature_item_id item)) name)

let rec path_head_ident (path : Path.t) : Ident.t =
  match path with
  | Path.Pident ident -> ident
  | Path.Pdot (parent, _) | Path.Pextra_ty (parent, _) ->
      path_head_ident parent
  | Path.Papply (functor_path, _) -> path_head_ident functor_path

(** Recover a stable, qualified constructor path when the type checker retained
    only a local identifier introduced by an include. *)
let normalize_type_path (env : Env.t) (path : Path.t) : Path.t =
  try
    match path with
    | Path.Pdot (module_path, field) ->
        Path.Pdot
          (Env.normalize_module_path None env module_path, field)
    | _ -> Env.normalize_type_path None env path
  with _ -> path

(** Match a generic functor-result type with its specialized application type.
    The returned candidates identify only specialized constructor nodes whose
    generic counterparts denote one of [origin_type_paths]. *)
let constructor_override_candidates_from_origin
    (origin_type_paths : (Path.t * MixedPath.t) list)
    (origin_typ : Types.type_expr) (specialized_typ : Types.type_expr) :
    (int * Path.t * MixedPath.t) list =
  let seen = Hashtbl.create 17 in
  let immediate_children typ =
    let children = ref [] in
    Btype.iter_type_expr (fun child -> children := child :: !children) typ;
    List.rev !children
  in
  let repr typ =
    typ |> Types.Transient_expr.repr |> Types.Transient_expr.type_expr
  in
  let rec collect overrides origin_typ specialized_typ =
    let origin_typ = repr origin_typ in
    let specialized_typ = repr specialized_typ in
    let key = (Types.get_id origin_typ, Types.get_id specialized_typ) in
    if Hashtbl.mem seen key then overrides
    else (
      Hashtbl.add seen key ();
      let overrides =
        match
          (Types.get_desc origin_typ, Types.get_desc specialized_typ)
        with
        | Tconstr (origin_path, _, _), Tconstr (specialized_path, _, _) -> (
            match
              List.find_map
                (fun (candidate, target) ->
                  if Path.same origin_path candidate then Some target else None)
                origin_type_paths
            with
            | Some target ->
                (Types.get_id specialized_typ, specialized_path, target)
                :: overrides
            | None -> overrides)
        | _ -> overrides
      in
      let origin_children = immediate_children origin_typ in
      let specialized_children = immediate_children specialized_typ in
      if List.length origin_children = List.length specialized_children then
        List.fold_left2 collect overrides origin_children specialized_children
      else overrides)
  in
  collect [] origin_typ specialized_typ

(** Import an OCaml structure. *)
let rec of_structure ?(has_functor_parameters = false)
    (structure : structure) : t list Monad.t =
  let get_record_include_items
      (alias : IncludedRecordAliasTarget.t)
      (mod_type : Types.module_type) (exclude_list : string list) :
      t list Monad.t =
    let* env = get_env in
    let rec items_of_signature (alias : IncludedRecordAliasTarget.t)
        (exclude : string list) (signature : Types.signature) :
        t list Monad.t =
      signature
      |> Monad.List.concat_map (fun signature_item ->
             let ident = Types.signature_item_id signature_item in
             let source_name = Ident.name ident in
             if List.mem source_name exclude then return []
             else
               match signature_item with
               | Types.Sig_value (ident, { val_type; _ }, _) ->
                   let* name = Name.of_ident true ident in
                   let* typ, _, new_typ_vars =
                     Type.of_typ_expr true Name.Map.empty val_type
                   in
                   let* access =
                     MixedPath.of_included_record_alias true alias
                       [ source_name ]
                   in
                   return
                     [
                       ModuleIncludeItem
                         ( IncludeValue,
                           name,
                           List.map fst new_typ_vars,
                           Some typ,
                           access,
                           [] );
                     ]
               | Types.Sig_type (ident, { type_params; _ }, _, _) ->
                   let* name = Name.of_ident false ident in
                   let* _, _, typ_vars =
                     Type.of_typs_exprs true type_params Name.Map.empty
                   in
                   let* access =
                     MixedPath.of_included_record_alias false alias
                       [ source_name ]
                   in
                   return
                     [
                       ModuleIncludeItem
                         ( IncludeType,
                           name,
                           List.map fst typ_vars,
                           None,
                           access,
                           [] );
                     ]
               | Types.Sig_module
                   (ident, _, { md_type; _ }, _, _) -> (
                   match Mtype.scrape env md_type with
                   | Mty_signature nested_signature ->
                       let* name = Name.of_ident false ident in
                       let nested_alias =
                         {
                           alias with
                           IncludedRecordAliasTarget.fields =
                             alias.fields @ [ source_name ];
                         }
                       in
                       let* nested_items =
                         items_of_signature nested_alias [] nested_signature
                       in
                       return
                         [
                           Module
                             (name, ([], [], []), nested_items, None);
                         ]
                   | _ -> return [])
               | Types.Sig_typext _
               | Types.Sig_modtype _
               | Types.Sig_class _
               | Types.Sig_class_type _ ->
                   return [])
    in
    match Mtype.scrape env mod_type with
    | Mty_signature signature ->
        let* items =
          items_of_signature alias exclude_list signature
        in
        return
          [
            Documentation
              ("Inclusion from a translated functor-result record", items);
          ]
    | _ ->
        error_message (Error "record_include_without_signature")
          Unexpected
          "A translated functor-result include has no concrete signature."
  in
  let get_include_items (module_path : Path.t option)
      (fallback_signature_path : Path.t option) (reference : PathName.t)
      (mod_type : Types.module_type) (exclude_list : string list) : t list Monad.t
      =
    let field_reference (name : Name.t) : PathName.t =
      {
        PathName.path = reference.path @ [ reference.base ];
        base = name;
      }
    in
    let namespace_item (kind : module_include_item_kind) (name : Name.t)
        (typ_vars : Name.t list) (typ : Type.t option) : t =
      ModuleIncludeItem
        ( kind,
          name,
          typ_vars,
          typ,
          MixedPath.PathName (field_reference name),
          [] )
    in
    let* is_first_class =
      IsFirstClassModule.is_module_typ_first_class mod_type module_path
    in
    let is_first_class =
      match (is_first_class, fallback_signature_path) with
      | IsFirstClassModule.Not_found _, Some signature_path ->
          IsFirstClassModule.Found signature_path
      | result, _ -> result
    in
    match is_first_class with
    | IsFirstClassModule.Found mod_type_path -> (
        get_env >>= fun env ->
        match Mtype.scrape env mod_type with
        | Mty_ident path | Mty_alias path ->
            error_message (Error "include_module_with_abstract_module_type")
              NotSupported
              ("Cannot get the fields of the abstract module type `"
             ^ Path.name path ^ "` to handle the include.")
        | Mty_for_hole ->
            error_message (Error "mty_hole")
              NotSupported
              "Holes not supported"
        | Mty_signature signature ->
            let rec items_of_signature
                (record_fields : PathName.t list)
                (signature_path : Path.t) (prefix : string list)
                (inherited_type_substitutions :
                  (Name.t list * MixedPath.t) list)
                (inherited_origin_type_paths : (Path.t * MixedPath.t) list)
                (origin_signature : Types.signature option)
                (exclude : string list) (signature : Types.signature) :
                t list Monad.t =
              let mixed_path_names = function
                | MixedPath.PathName { path; base } -> path @ [ base ]
                | MixedPath.Access ({ path; base }, fields)
                | MixedPath.AppliedAccess ({ path; base }, _, fields) ->
                    path @ [ base ]
                    @ List.map
                        (fun field -> field.PathName.base)
                        fields
              in
              let source_is_shadowed_by_signature_type source =
                match source with
                | Path.Pident source_ident ->
                    signature
                    |> List.exists (function
                         | Types.Sig_type (local_ident, _, _, _) ->
                             String.equal
                               (Ident.name source_ident)
                               (Ident.name local_ident)
                             && not (Ident.same source_ident local_ident)
                         | _ -> false)
                | Path.Pdot _ | Path.Papply _ | Path.Pextra_ty _ -> false
              in
              (* Give constructor aliases an exact compiler path before
                 translating the manifest and value types when their printed
                 names are otherwise ambiguous.  This is needed both for
                 applicative results such as [Map.Make(Ord).t] and when an
                 outer [t] is shadowed by a nested signature's own [t].
                 Delaying either case until [Type.t] loses the compiler
                 identity and can rewrite the wrong constructor. *)
              let* manifest_path_aliases =
                signature
                |> Monad.List.filter_map (function
                     | Types.Sig_type
                         ( ident,
                           {
                             type_manifest = Some manifest;
                             type_params;
                             _;
                           },
                           _,
                           _ ) -> (
                         match Types.get_desc manifest with
                         | Tconstr (source, arguments, _)
                           when
                             (Type.path_contains_functor_application source
                             || source_is_shadowed_by_signature_type source)
                             && List.length type_params =
                               List.length arguments
                             &&
                             (try
                                Ctype.equal env false type_params arguments;
                                true
                              with _ -> false) ->
                             let* target_name =
                               Name.of_strings false
                                 (prefix @ [ Ident.name ident ])
                             in
                             let target =
                               Path.Pident
                                 (Ident.create_local
                                    (Name.to_string target_name))
                             in
                             return (Some (source, target))
                         | _ -> return None)
                     | _ -> return None)
              in
              let translate_signature =
              let* manifest_type_substitutions =
                signature
                |> List.mapi (fun index item -> (index, item))
                |> Monad.List.filter_map (function
                     | index, Types.Sig_type
                         ( ident,
                           {
                             type_manifest = Some manifest;
                             type_params;
                             _;
                           },
                           _,
                           _ ) ->
                         let source_name = Ident.name ident in
                         let* parameters =
                           Monad.List.map Type.of_type_expr_variable
                             type_params
                         in
                         let* manifest =
                           Type.of_type_expr_without_free_vars manifest
                         in
                         let manifest =
                           match parameters with
                           | [] -> manifest
                           | _ :: _ -> Type.FunTyps (parameters, manifest)
                         in
                         (match Type.direct_constructor_path manifest with
                         | Some source ->
                             let* target_name =
                               Name.of_strings false
                                 (prefix @ [ source_name ])
                             in
                             let target =
                               MixedPath.PathName
                                 (PathName.of_name [] target_name)
                             in
                             if
                               String.equal
                                 (MixedPath.to_string source)
                                 (MixedPath.to_string target)
                             then
                               return None
                             else
                               return
                                 (Some
                                    ( index,
                                      (mixed_path_names source, target) ))
                         | None -> return None)
                     | _ -> return None)
              in
              let* local_type_substitutions =
                signature
                |> Monad.List.filter_map (fun signature_item ->
                       match signature_item with
                       | Types.Sig_type (ident, _, _, _)
                         when List.mem (Ident.name ident) exclude ->
                           let source_name = Ident.name ident in
                           let* name = Name.of_ident false ident in
                           let* flattened_name =
                             Name.of_strings false (prefix @ [ source_name ])
                           in
                           let* field =
                             PathName.of_path_and_name_with_convert
                               signature_path flattened_name
                           in
                           return
                             (Some
                                ( [ name ],
                                  MixedPath.Access
                                    (reference, record_fields @ [ field ]) ))
                       | _ -> return None)
              in
              (* Non-record nested modules are flattened in a functor-result
                 record: [Option.t] becomes the sibling field [Option_t].
                 Scraped result signatures can consequently mention the bare
                 flattened constructor in value types.  Rebind it to the
                 corresponding record projection before emitting the nested
                 namespace; no local [Option_t] definition exists there. *)
              let* namespace_type_substitutions =
                match prefix with
                | [] -> return []
                | _ :: _ ->
                    signature
                    |> Monad.List.filter_map (function
                         | Types.Sig_type (ident, _, _, _) ->
                             let source_name = Ident.name ident in
                             let* flattened_name =
                               Name.of_strings false
                                 (prefix @ [ source_name ])
                             in
                             let* field =
                               PathName.of_path_and_name_with_convert
                                 signature_path flattened_name
                             in
                             return
                               (Some
                                  ( [ flattened_name ],
                                    MixedPath.Access
                                      (reference, record_fields @ [ field ]) ))
                         | _ -> return None)
              in
              (* Manifest aliases describe equalities within this signature.
                 Propagating them into a nested module is unsound: an outer
                 [type t = int] must not turn an unrelated nested result such
                 as [cardinal : set -> int] into [set -> t].  Substitutions for
                 excluded (shadowed) fields do cross module boundaries because
                 nested fields may still refer to the excluded outer field. *)
              let nested_type_substitutions =
                namespace_type_substitutions
                @ local_type_substitutions
                @ inherited_type_substitutions
              in
              let origin_item name =
                match origin_signature with
                | Some signature -> signature_item_named name signature
                | None -> None
              in
              (* The specialized result signature may replace a parent
                 associated type such as [M.t] with its concrete argument type.
                 Keep the generic result signature as provenance: only
                 constructor occurrences that were [M.t] are redirected to the
                 parent result-record field.  This remains precise when the
                 concrete type also occurs independently in a nested module. *)
              let* descendant_origin_type_paths =
                signature
                |> Monad.List.concat_map (function
                     | Types.Sig_type (ident, _, _, _) -> (
                         let source_name = Ident.name ident in
                         match origin_item source_name with
                         | Some
                             (Types.Sig_type
                               ( origin_ident,
                                 {
                                   type_manifest;
                                   type_params;
                                   _;
                                 },
                                 _,
                                 _ )) ->
                             let* flattened_name =
                               Name.of_strings false (prefix @ [ source_name ])
                             in
                             let* field =
                               PathName.of_path_and_name_with_convert
                                 signature_path flattened_name
                             in
                             let target =
                               if has_functor_parameters then
                                 MixedPath.AppliedAccess
                                   ( reference,
                                     [ ("_fargs", "_fargs") ],
                                     record_fields @ [ field ] )
                               else
                                 MixedPath.Access
                                   (reference, record_fields @ [ field ])
                             in
                             let manifest_paths =
                               match type_manifest with
                               | Some manifest -> (
                                   match Types.get_desc manifest with
                                   | Tconstr (source, arguments, _)
                                     when
                                       List.length type_params =
                                         List.length arguments
                                       &&
                                       (try
                                          Ctype.equal env false type_params
                                            arguments;
                                          true
                                        with _ -> false)
                                       &&
                                       let head = path_head_ident source in
                                       (not (Ident.global head))
                                       && not (Ident.is_predef head) ->
                                       [ source ]
                                   | _ -> [])
                               | None -> []
                             in
                             return
                               (List.map
                                  (fun source -> (source, target))
                                  (Path.Pident origin_ident :: manifest_paths))
                         | _ -> return [])
                     | _ -> return [])
              in
              let descendant_origin_type_paths =
                descendant_origin_type_paths @ inherited_origin_type_paths
              in
              let qualify_shadowed_types item_index typ =
                let manifest_type_substitutions =
                  manifest_type_substitutions
                  |> List.filter_map
                       (fun (declaration_index, substitution) ->
                         if declaration_index < item_index then
                           Some substitution
                         else None)
                in
                List.fold_left
                  (fun typ (source, target) ->
                    Type.subst_constructor_path source target typ)
                  typ
                  (manifest_type_substitutions @ nested_type_substitutions)
              in
              signature
              |> List.mapi (fun index item -> (index, item))
              |> Monad.List.concat_map (fun (item_index, signature_item) ->
                     let ident = Types.signature_item_id signature_item in
                     let source_name = Ident.name ident in
                     if List.mem source_name exclude then return []
                     else
                       match signature_item with
                       | Types.Sig_value
                           (ident, { val_type; _ }, _) ->
                           let* name = Name.of_ident true ident in
                           let* flattened_name =
                             Name.of_strings true (prefix @ [ source_name ])
                           in
                           let* field =
                             PathName.of_path_and_name_with_convert
                               signature_path flattened_name
                           in
                           let* constructor_overrides =
                             match origin_item source_name with
                             | Some
                                 (Types.Sig_value
                                   (_, { val_type = origin_type; _ }, _)) ->
                                 constructor_override_candidates_from_origin
                                   inherited_origin_type_paths origin_type
                                   val_type
                                 |> Monad.List.map
                                      (fun
                                        ( node_id,
                                          specialized_path,
                                          fallback )
                                      ->
                                        let normalized_path =
                                          normalize_type_path env
                                            specialized_path
                                        in
                                        match specialized_path with
                                        | Path.Pident ident
                                          when
                                            (not (Ident.global ident))
                                            && not (Ident.is_predef ident)
                                            && Path.same normalized_path
                                                 specialized_path ->
                                            return (node_id, fallback)
                                        | _ ->
                                            let* target =
                                              MixedPath.of_path false
                                                normalized_path
                                            in
                                            return (node_id, target))
                             | _ -> return []
                           in
                           let* typ, _, new_typ_vars =
                             Type.of_typ_expr ~constructor_overrides true
                               Name.Map.empty val_type
                           in
                           let typ = qualify_shadowed_types item_index typ in
                           return
                             [
                               ModuleIncludeItem
                                 ( IncludeValue,
                                   name,
                                   List.map fst new_typ_vars,
                                   Some typ,
                                   MixedPath.Access
                                     (reference, record_fields @ [ field ]),
                                   [] );
                             ]
                       | Types.Sig_type
                           (ident, { type_params; _ }, _, _) ->
                           let* name = Name.of_ident false ident in
                           let* flattened_name =
                             Name.of_strings false (prefix @ [ source_name ])
                           in
                           let* field =
                             PathName.of_path_and_name_with_convert
                               signature_path flattened_name
                           in
                           let* _, _, typ_vars =
                             Type.of_typs_exprs true type_params Name.Map.empty
                           in
                           return
                             [
                               ModuleIncludeItem
                                 ( IncludeType,
                                   name,
                                   List.map fst typ_vars,
                                   None,
                                   MixedPath.Access
                                     (reference, record_fields @ [ field ]),
                                   [] );
                             ]
                       | Types.Sig_module
                           (ident, _, { md_type; _ }, _, _) -> (
                           match Env.scrape_alias env md_type with
                           | Mty_signature nested_signature ->
                               let* name = Name.of_ident false ident in
                               let origin_nested_signature =
                                 match origin_item source_name with
                                 | Some
                                     (Types.Sig_module
                                       (_, _, { md_type; _ }, _, _)) -> (
                                     match Mtype.scrape env md_type with
                                     | Mty_signature signature ->
                                         Some signature
                                     | _ -> None)
                                 | _ -> None
                               in
                               let* nested_kind =
                                 let* field_signature =
                                   get_result_module_field signature_path
                                     source_name
                                 in
                                 match field_signature with
                                 | Some field_signature ->
                                     return
                                       (IsFirstClassModule.Found
                                          field_signature)
                                 | None ->
                                     IsFirstClassModule
                                     .is_module_typ_first_class md_type
                                       (Some (Path.Pident ident))
                               in
                               let* nested_items, module_alias =
                                 match nested_kind with
                                 | IsFirstClassModule.Found
                                     nested_signature_path ->
                                     let nested_signature_path =
                                       qualify_result_field_signature
                                         env signature_path
                                         nested_signature_path
                                     in
                                     let* field =
                                       PathName
                                       .of_path_and_name_with_convert
                                         signature_path name
                                     in
                                     let record_fields =
                                       record_fields @ [ field ]
                                     in
                                     let* nested_items =
                                       items_of_signature record_fields
                                         nested_signature_path []
                                         nested_type_substitutions
                                         descendant_origin_type_paths
                                         origin_nested_signature []
                                         nested_signature
                                     in
                                     let alias =
                                       ModuleIncludeItem
                                         ( IncludeValue,
                                           name,
                                           [],
                                           None,
                                           MixedPath.Access
                                             (reference, record_fields),
                                           [] )
                                     in
                                     return (nested_items, Some alias)
                                 | IsFirstClassModule.Not_found _ ->
                                     let* nested_items =
                                       items_of_signature record_fields
                                         signature_path
                                         (prefix @ [ source_name ])
                                         nested_type_substitutions
                                         descendant_origin_type_paths
                                         origin_nested_signature []
                                         nested_signature
                                     in
                                     return (nested_items, None)
                               in
                               let module_namespace =
                                 Module
                                   (name, ([], [], []), nested_items, None)
                               in
                               return
                                 (module_namespace
                                 :: Option.to_list module_alias)
                           | _ -> return [])
                       | Types.Sig_typext _
                       | Types.Sig_modtype _
                       | Types.Sig_class _
                       | Types.Sig_class_type _ ->
                           return [])
              in
              List.fold_right
                (fun (source, target) translation ->
                  set_module_path_alias source target translation)
                manifest_path_aliases translate_signature
            in
            let* origin_signature =
              let* origin_module_type = get_module_type_hint mod_type_path in
              match origin_module_type with
              | Some module_type -> (
                  match Mtype.scrape env module_type with
                  | Mty_signature signature -> return (Some signature)
                  | _ -> return None)
              | None -> return None
            in
            let* items =
              items_of_signature [] mod_type_path [] [] [] origin_signature
                exclude_list signature
            in
            let documentation =
              "Inclusion of the module [" ^ PathName.to_string reference ^ "]"
            in
            return [ Documentation (documentation, items) ]
        | Mty_functor _ ->
            error_message (Error "include_functor") Unexpected
              "Unexpected include of functor."
      )
    | _ -> (
        match exclude_list with
        | [] -> return [ ModuleInclude reference ]
        | _ :: _ -> (
            let* env = get_env in
            match Mtype.scrape env mod_type with
            | Mty_signature signature ->
                signature
                |> Monad.List.concat_map (fun signature_item ->
                       match signature_item with
                       | Types.Sig_modtype
                           (ident, modtype_declaration, _)
                         when not
                                (List.mem (Ident.name ident) exclude_list) -> (
                           match modtype_declaration.mtd_type with
                           | None ->
                               error_message
                                 (Error "abstract_in_partial_namespace_include")
                                 NotSupported
                                 "An abstract module type cannot be copied \
                                  from a partially shadowed namespace include."
                           | Some _ ->
                               let* name = Name.of_ident false ident in
                               let field_reference =
                                 {
                                   PathName.path =
                                     reference.path @ [ reference.base ];
                                   base = name;
                                 }
                               in
                               let* typ_params =
                                 ModuleTypParams
                                 .get_module_typ_declaration_typ_params_arity
                                   modtype_declaration
                               in
                               let nb_typ_params =
                                 List.length (Tree.flatten typ_params)
                               in
                               return
                                 [
                                   SignatureSynonym
                                     (name, field_reference, nb_typ_params);
                                 ])
                       | Types.Sig_modtype _ -> return []
                       | Types.Sig_value (ident, { val_type; _ }, _)
                         when not
                                (List.mem (Ident.name ident) exclude_list) ->
                           let* name = Name.of_ident true ident in
                           let* typ, _, typ_vars =
                             Type.of_typ_expr true Name.Map.empty val_type
                           in
                           return
                             [
                               namespace_item IncludeValue name
                                 (List.map fst typ_vars) (Some typ);
                             ]
                       | Types.Sig_type
                           (ident, { type_params; _ }, _, _)
                         when not
                                (List.mem (Ident.name ident) exclude_list) ->
                           let* name = Name.of_ident false ident in
                           let* _, _, typ_vars =
                             Type.of_typs_exprs true type_params Name.Map.empty
                           in
                           return
                             [
                               namespace_item IncludeType name
                                 (List.map fst typ_vars) None;
                             ]
                       | Types.Sig_module
                           (ident, _, { md_type; _ }, _, _)
                         when not
                                (List.mem (Ident.name ident) exclude_list) ->
                           let source_name = Ident.name ident in
                           let* name = Name.of_ident false ident in
                           let module_reference = field_reference name in
                           let nested_module_path =
                             Option.map
                               (fun parent ->
                                 Path.Pdot (parent, source_name))
                               module_path
                           in
                           let* module_kind =
                             IsFirstClassModule.is_module_typ_first_class
                               md_type nested_module_path
                           in
                           let aliases =
                             match module_kind with
                             | IsFirstClassModule.Found _ ->
                                 [
                                   namespace_item IncludeValue name [] None;
                                 ]
                             | IsFirstClassModule.Not_found _ ->
                                 [
                                   ModuleSynonym
                                     (name, module_reference, false);
                                 ]
                           in
                           return aliases
                       | signature_item ->
                           let ident = Types.signature_item_id signature_item in
                           if List.mem (Ident.name ident) exclude_list then
                             return []
                           else
                             error_message
                               (Error
                                  "unsupported_partial_namespace_include_item")
                               NotSupported
                               ("Cannot yet copy `" ^ Ident.name ident
                              ^ "` from a partially shadowed namespace \
                                 include."))
            | _ ->
                error_message (Error "partial_non_namespace_include")
                  NotSupported
                  "A partially shadowed include must expose a namespace \
                   signature."))
  in
  let of_structure_item (item : structure_item) (final_env : Env.t)
      (shadowed_names : string list) : t list Monad.t =
    let is_top_level_evaluation = function
      | [
        {
          vb_pat =
            {
              pat_desc =
                Tpat_construct
                  ( _,
                    { cstr_res;
                      _;
                    },
                    _, _ );
              _;
            };
          _;
        };
      ] ->
        begin match Types.get_desc cstr_res with
          | Tconstr (path, _, _) -> PathName.is_unit path
          | _ -> false
        end
      | _ -> false
    in
    set_env item.str_env
      (set_loc item.str_loc
         (wrap_documentation
            (match item.str_desc with
            | Tstr_value
                ( _,
                  ([
                    {
                      vb_attributes;
                      vb_expr;
                      _;
                    };
                  ] as vbs) )
              when is_top_level_evaluation vbs ->
                let* attributes = Attribute.of_attributes vb_attributes in
                if Attribute.has_axiom_with_reason attributes then return []
                else top_level_evaluation vb_expr
            | Tstr_eval (e, _) -> top_level_evaluation e
            | Tstr_value (is_rec, cases) ->
                push_env
                  (let* use_unsafe_fixpoints, definition =
                   retrieve_unsafe_fixpoints
                       (Exp.import_let_fun Name.Map.empty true is_rec cases)
                   in
                   let definition =
                     Exp.add_assumption_instance_args definition
                   in
                   return [ Value { use_unsafe_fixpoints; definition } ])
            | Tstr_type (_, typs) ->
                (* Because types may be recursive, so we need the types to already be in
                   the environment. This is useful for example for the detection of
                   phantom types. *)
                set_env final_env
                  (let* defs = TypeDefinition.of_ocaml typs in
                   return (List.map (fun def -> TypeDefinition def) defs))
            | Tstr_exception { tyexn_constructor; _ } ->
                typ_definitions_of_typ_extension tyexn_constructor
            | Tstr_open _ -> return []
            | Tstr_module { mb_id = Some ident; _ }
              when Ident.name ident = "Internal_for_tests" ->
                return []
            | Tstr_module { mb_id; mb_expr; mb_attributes; _ } ->
                let* name = Name.of_optional_ident false mb_id in
                let binding_path =
                  Option.map (fun ident -> Path.Pident ident) mb_id
                in
                let* has_plain_module_attribute =
                  let* attributes = Attribute.of_attributes mb_attributes in
                  return (Attribute.has_plain_module attributes)
                in
                let* module_definition =
                  of_module ?binding_path
                    ~has_enclosing_fargs:has_functor_parameters name
                    ([], [], []) mb_expr has_plain_module_attribute
                in
                return [ module_definition ]
            | Tstr_modtype { mtd_type = None; _ } ->
                error_message (Error "abstract_module_type") NotSupported
                  "Abstract module types not handled."
            | Tstr_modtype { mtd_id; mtd_type = Some module_typ; _ } -> (
                let* name = Name.of_ident false mtd_id in
                match module_typ.mty_desc with
                | Tmty_signature signature ->
                    Signature.of_signature signature >>= fun signature ->
                    return [ Signature (name, signature) ]
                | Tmty_ident (path, _) ->
                    let* reference =
                      PathName.of_path_with_convert false path
                    in
                    let* env = get_env in
                    let declaration = Env.find_modtype path env in
                    let* typ_params =
                      ModuleTypParams
                      .get_module_typ_declaration_typ_params_arity declaration
                    in
                    let nb_typ_params = List.length (Tree.flatten typ_params) in
                    return
                      [ SignatureSynonym (name, reference, nb_typ_params) ]
                | _ ->
                    let signature_kind = kind_of_signature module_typ in
                    error_message (Error "unhandled_module_type") NotSupported
                      ("This kind of signature (" ^ signature_kind
                     ^ ") is not handled."))
            | Tstr_primitive { val_id; val_val = { val_type; _ }; _ } ->
                let* name = Name.of_ident true val_id in
                Type.of_typ_expr true Name.Map.empty val_type
                >>= fun (typ, _, free_typ_vars) ->
                return [ AbstractValue (name, List.map fst free_typ_vars, typ) ]
            | Tstr_typext { tyext_constructors; _ } ->
                Monad.List.concat_map typ_definitions_of_typ_extension
                  tyext_constructors
            | Tstr_recmodule bindings ->
                recursive_module_definitions bindings
            | Tstr_class _ ->
                error_message (Error "class") NotSupported
                  "Structure item `class` not handled."
            | Tstr_class_type _ ->
                error_message (Error "class_type") NotSupported
                  "Structure item `class_type` not handled."
            | Tstr_include { incl_attributes; incl_type; _ }
              when has_raw_attribute "merlin.hide" incl_attributes ->
                incl_type
                |> Monad.List.filter_map (function
                     | Types.Sig_value
                         (ident, { Types.val_type; _ }, _)
                       when not (String.equal (Ident.name ident) "_") ->
                         let* name = Name.of_ident true ident in
                         let* typ, _, free_typ_vars =
                           Type.of_typ_expr true Name.Map.empty val_type
                         in
                         return
                           (Some
                              (AbstractValue
                                 ( name,
                                   List.map fst free_typ_vars,
                                   typ )))
                     | _ -> return None)
            | Tstr_include
                {
                  incl_attributes;
                  incl_mod = { mod_desc = Tmod_ident (path, _); mod_type; _ };
                  _;
                }
            | Tstr_include
                {
                  incl_attributes;
                  incl_mod =
                    {
                      mod_desc =
                        Tmod_constraint
                          ({ mod_desc = Tmod_ident (path, _); _ }, _, _, _);
                      mod_type;
                      _;
                    };
                  _;
                } ->
                let* attributes = Attribute.of_attributes incl_attributes in
                let exclude_list =
                  List.sort_uniq String.compare
                    (Attribute.get_include_without attributes @ shadowed_names)
                in
                let* record_alias =
                  match path with
                  | Path.Pident ident ->
                      get_included_record_alias ident
                  | _ -> return None
                in
                (match record_alias with
                | Some alias ->
                    get_record_include_items alias mod_type exclude_list
                | None ->
                    let* reference =
                      PathName.of_path_with_convert false path
                    in
                    get_include_items (Some path) None reference mod_type
                      exclude_list)
            | Tstr_include { incl_attributes; incl_mod; _ } ->
                let* include_name = Exp.get_include_name incl_mod in
                let reference = PathName.of_name [] include_name in
                let* attributes = Attribute.of_attributes incl_attributes in
                let exclude_list =
                  List.sort_uniq String.compare
                    (Attribute.get_include_without attributes @ shadowed_names)
                in
                let module_path =
                  ModulePathAliases.module_expr_path incl_mod
                in
                let translate_include =
                  let* module_definition =
                    of_module
                      ~has_enclosing_fargs:has_functor_parameters include_name
                      ([], [], []) incl_mod false
                  in
                  let* fallback_signature_path =
                    match applied_functor_root_path incl_mod with
                    | Some functor_path ->
                        let* known_result =
                          get_functor_result_signature functor_path
                        in
                        (match known_result with
                        | Some _ as result -> return result
                        | None ->
                            return
                              (Some
                                 (Path.Pdot
                                    ( functor_path,
                                      Path.last functor_path ^ "_result" ))))
                    | None -> (
                        match module_path with
                        | Some (Path.Papply (functor_path, _)) ->
                            return
                              (Some
                                 (Path.Pdot
                                    ( functor_path,
                                      Path.last functor_path ^ "_result" )))
                        | _ -> return None)
                  in
                  let* include_items =
                    get_include_items module_path fallback_signature_path
                      reference incl_mod.mod_type exclude_list
                  in
                  return (module_definition :: include_items)
                in
                let* include_alias =
                  applicative_include_alias incl_mod
                in
                (match include_alias with
                | Some (source_path, target_path) ->
                    set_module_path_alias source_path target_path
                      translate_include
                | None -> translate_include)
            (* We ignore attribute fields. *)
            | Tstr_attribute _ -> return [])))
  in
  Monad.List.fold_right
    (fun structure_item (structure, final_env, shadowed_names) ->
      let env = structure_item.str_env in
      of_structure_item structure_item final_env shadowed_names
      >>= fun translated_item ->
      let shadowed_names =
        List.sort_uniq String.compare
          (names_declared_by_structure_item structure_item @ shadowed_names)
      in
      return (translated_item @ structure, env, shadowed_names))
    structure.str_items
    ([], structure.str_final_env, [])
  >>= fun (structure, _, _) -> return structure

and of_module ?binding_path ?(has_enclosing_fargs = false) (name : Name.t)
    (functor_parameters : functor_parameters)
    (module_expr : module_expr) (has_plain_module_attribute : bool) : t Monad.t
    =
  let include_aliases : (Path.t * Path.t) list Monad.t =
    let rec final_structure (module_expr : module_expr) =
      match module_expr.mod_desc with
      | Tmod_structure structure -> Some structure
      | Tmod_functor (_, body)
      | Tmod_constraint (body, _, _, _) ->
          final_structure body
      | Tmod_ident _
      | Tmod_apply _
      | Tmod_apply_unit _
      | Tmod_unpack _
      | Tmod_typed_hole ->
          None
    in
    match final_structure module_expr with
    | None -> return []
    | Some structure ->
        structure.str_items
        |> Monad.List.filter_map
             (fun item ->
               match item.str_desc with
               | Tstr_include { incl_mod; _ } ->
                   applicative_include_alias incl_mod
               | _ -> return None)
  in
  let translate_module () =
    let path =
      match binding_path with
      | Some _ as path -> path
      | None -> (
          match module_expr.mod_desc with
          | Tmod_ident (path, _)
          | Tmod_constraint
              ({ mod_desc = Tmod_ident (path, _); _ }, _, _, _) ->
              Some path
          | _ -> None)
    in
  let* is_first_class =
    IsFirstClassModule.is_module_typ_first_class module_expr.mod_type path
  in
  let explicit_signature_path =
    SignatureHints.module_expr_annotation module_expr
  in
  let anonymous_signature =
    SignatureHints.module_expr_anonymous_annotation module_expr
  in
  let* as_expression, synthetic_signature =
    match (anonymous_signature, has_plain_module_attribute) with
    | Some module_type, false ->
        let synthetic_name =
          Name.of_string_raw (Name.to_string name ^ "_signature")
        in
        let synthetic_path =
          Path.Pident
            (Ident.create_local (Name.to_string synthetic_name))
        in
        let signature_hint_path =
          match binding_path with
          | Some module_path ->
              Path.Pdot
                (module_path, Name.to_string synthetic_name)
          | None -> synthetic_path
        in
        let* signature =
          match module_type.mty_desc with
          | Tmty_signature source_signature ->
              set_env module_type.mty_env
                (Signature.of_types_signature
                   ~abstract_functor_applications:true
                   ~expand_aliases:true
                   ~signature_path:signature_hint_path
                   source_signature.sig_type)
          | _ ->
              raise { Signature.items = []; typ_params = [] } Unexpected
                "An anonymous module annotation lost its signature"
        in
        let synthetic_typ_params = signature.Signature.typ_params in
        return
          ( Some
              ( module_type.mty_type,
                synthetic_path,
                Some synthetic_typ_params ),
            Some (synthetic_name, synthetic_path, signature) )
    | _ -> (
        match
          (explicit_signature_path, is_first_class,
           has_plain_module_attribute)
        with
        | Some module_type_path, _, false ->
            return
              (Some (module_expr.mod_type, module_type_path, None), None)
        | None, Found module_type_path, false ->
            return
              (Some (module_expr.mod_type, module_type_path, None), None)
        | None, Not_found _, false -> (
          match (functor_parameters, module_expr.mod_type) with
          | (_, _ :: _, _), Types.Mty_signature signature ->
            let synthetic_name =
              Name.of_string_raw (Name.to_string name ^ "_result")
            in
            let synthetic_ident =
              Ident.create_local (Name.to_string synthetic_name)
            in
            let synthetic_path = Path.Pident synthetic_ident in
            let signature_hint_path =
              match binding_path with
              | Some module_path ->
                  Path.Pdot
                    (module_path, Name.to_string synthetic_name)
              | None -> synthetic_path
            in
            let result_env =
              match module_expr.mod_desc with
              | Tmod_structure structure -> structure.str_final_env
              | _ -> module_expr.mod_env
            in
            let result_location =
              {
                module_expr.mod_loc with
                loc_start = module_expr.mod_loc.loc_end;
              }
            in
            let* signature =
              set_loc result_location
                (set_env result_env
                   (Signature.of_types_signature
                      ~abstract_functor_applications:true ~expand_aliases:true
                      ~signature_path:signature_hint_path
                      signature))
            in
            let synthetic_typ_params = signature.Signature.typ_params in
            return
              ( Some
                  ( module_expr.mod_type,
                    synthetic_path,
                    Some synthetic_typ_params ),
                Some (synthetic_name, synthetic_path, signature) )
          | _ -> return (None, None))
        | _, _, _ -> return (None, None))
  in
  let module_definition =
    of_module_expr ?binding_path ~has_enclosing_fargs name
      functor_parameters as_expression None module_expr
  in
  let module_definition =
    match (binding_path, synthetic_signature) with
    | Some module_path, Some (_, signature_path, _) ->
        set_signature_hint module_path signature_path module_definition
    | _ -> module_definition
  in
  let* module_definition = module_definition
  in
  match (synthetic_signature, module_definition) with
  | None, _ -> return module_definition
  | ( Some (signature_name, _, signature),
      Module (name, functor_parameters, definitions, expression) ) ->
      return
        (Module
           ( name,
             functor_parameters,
             definitions @ [ Signature (signature_name, signature) ],
             expression ))
  | Some _, _ ->
      raise module_definition Unexpected
        "A synthesized functor result signature requires a module body"
  in
  let* include_aliases = set_env module_expr.mod_env include_aliases in
  List.fold_right
    (fun (source, target) body ->
      set_module_path_alias source target body)
    include_aliases (translate_module ())

and of_module_expr ?binding_path ?(has_enclosing_fargs = false)
    (name : Name.t)
    (functor_parameters : functor_parameters)
    (as_expression :
      (Types.module_type * Path.t * (Name.t * int) list option) option)
    (module_type_annotation : Typedtree.module_type option)
    (module_expr : module_expr) : t Monad.t =
  let instantiate_local_signature_types (typ : Type.t) : Type.t =
    match typ with
    | Type.Signature (path, parameters) ->
        Type.Signature
          ( path,
            parameters
            |> List.map (fun (name, typ) ->
                   ( name,
                     match typ with
                     | Some _ -> typ
                     | None -> Some (Type.Variable name) )) )
    | typ -> typ
  in
  let* module_typ =
    match module_type_annotation with
    | Some module_typ ->
        let* module_typ = ModuleTyp.of_ocaml module_typ in
        let functor_parameter_names =
          let _, parameters, _ = functor_parameters in
          parameters |> List.map (fun (name, _) -> name)
        in
        let* _, module_typ =
          ModuleTyp.to_typ functor_parameter_names (Name.to_string name) true
            module_typ
        in
        return (Some module_typ)
    | None -> return None
  in
  let module_typ =
    match (module_expr.mod_desc, module_typ) with
    | Tmod_structure _, Some typ ->
        Some (instantiate_local_signature_types typ)
    | _ -> module_typ
  in
  match module_expr.mod_desc with
  | Tmod_structure source_structure ->
      let translate_structure () =
      let _, parameters, _ = functor_parameters in
      let has_functor_parameters =
        has_enclosing_fargs || parameters <> []
      in
      let* structure =
        of_structure ~has_functor_parameters source_structure
      in
      let* local_module_bindings =
        source_structure.str_items
        |> Monad.List.concat_map
             (fun (item : Typedtree.structure_item) ->
               match item.str_desc with
               | Tstr_module { mb_id = Some ident; mb_expr; _ } ->
                   let* name = Name.of_ident false ident in
                   let* target_access =
                     let rec contains_application path =
                       match path with
                       | Path.Papply _ -> return true
                       | Path.Pdot (prefix, _)
                       | Path.Pextra_ty (prefix, _) ->
                           let* prefix_contains_application =
                             contains_application prefix
                           in
                           if prefix_contains_application then return true
                           else
                             let* module_alias =
                               get_module_path_alias path
                             in
                             (match module_alias with
                             | Some alias -> contains_application alias
                             | None -> return false)
                       | Path.Pident ident ->
                           let* module_alias = get_module_path_alias path in
                           (match module_alias with
                           | Some alias -> contains_application alias
                           | None ->
                               let* included_alias =
                                 get_included_path_alias ident
                               in
                               (match included_alias with
                               | Some alias -> contains_application alias
                               | None -> return false))
                     in
                     match ModulePathAliases.module_expr_path mb_expr with
                     | Some path ->
                         let has_global_head =
                           match Path.head path with
                           | ident -> Ident.global ident
                           | exception _ -> false
                         in
                         let* contains_application =
                           contains_application path
                         in
                         if
                           contains_application
                           || not has_global_head
                         then return None
                         else
                           let* { PathName.path; base } =
                             PathName.of_path_without_convert false path
                           in
                           return (Some (path @ [ base ]))
                     | None -> return None
                   in
                   return
                     [
                       ( name,
                         ident,
                         SignatureHints.module_expr_annotation mb_expr,
                         target_access );
                     ]
               | Tstr_recmodule bindings ->
                   bindings
                   |> Monad.List.filter_map
                        (fun binding ->
                          match binding.mb_id with
                          | None -> return None
                          | Some ident ->
                              let* name = Name.of_ident false ident in
                          let signature_path =
                            Option.bind
                              (explicit_module_type binding.mb_expr)
                              ModuleTyp.get_module_typ_path_name
                          in
                          return (Some (name, ident, signature_path, None)))
               | _ -> return [])
      in
      let* e =
        match as_expression with
        | Some
            (module_type, module_type_path, synthetic_typ_params) ->
            let typ_vars = Name.Map.empty in
            let* module_typ_params_arity =
              ModuleTypParams.get_module_typ_typ_params_arity module_type
            in
            let* values =
              Exp.ModuleTypValues.get
                ~skip_functors:(Option.is_some synthetic_typ_params)
                typ_vars module_type
            in
            let _, parameters, _ = functor_parameters in
            let local_mixed_path (access : Name.t list)
                (path_name : PathName.t) : MixedPath.t =
              if
                parameters = []
                || not (local_access_uses_fargs structure access)
              then
                MixedPath.PathName path_name
              else
                MixedPath.AppliedAccess
                  (path_name, [ ("_fargs", "_fargs") ], [])
            in
            let flattened_local_access (outer_field : Name.t) :
                Name.t list option Monad.t =
              let candidate access =
                let component_variants component =
                  let stripped_reserved =
                    if
                      String.length component > 1
                      && Char.equal component.[0] '_'
                    then
                      [
                        String.sub component 1
                          (String.length component - 1);
                      ]
                    else []
                  in
                  let value_suffix = "_value" in
                  let stripped_value =
                    if String.ends_with ~suffix:value_suffix component then
                      [
                        String.sub component 0
                          (String.length component
                          - String.length value_suffix);
                      ]
                    else []
                  in
                  List.sort_uniq String.compare
                    (component :: stripped_reserved @ stripped_value)
                in
                let rec combinations = function
                  | [] -> [ [] ]
                  | variants :: remaining ->
                      let remaining = combinations remaining in
                      variants
                      |> List.concat_map (fun variant ->
                             remaining
                             |> List.map (fun suffix ->
                                    variant :: suffix))
                in
                let flattened_name components =
                  match List.rev components with
                  | leaf :: reversed_modules
                    when String.starts_with ~prefix:"op_" leaf ->
                      let operator =
                        String.sub leaf 3 (String.length leaf - 3)
                      in
                      "op_"
                      ^ String.concat "_"
                          (List.rev reversed_modules @ [ operator ])
                  | _ -> String.concat "_" components
                in
                let outer_field = Name.to_string outer_field in
                let matches =
                  access
                  |> List.map (fun name ->
                         component_variants (Name.to_string name))
                  |> combinations
                  |> List.exists (fun components ->
                         String.equal
                           (flattened_name components)
                           outer_field)
                in
                return (if matches then Some access else None)
              in
              let rec first_some f = function
                | [] -> return None
                | item :: remaining ->
                    let* result = f item in
                    (match result with
                    | Some _ -> return result
                    | None -> first_some f remaining)
              in
              let rec search prefix = function
                | [] -> return None
                | definition :: remaining ->
                    let* result =
                      match definition with
                      | Value value ->
                          value.Value.definition.Exp.Definition.cases
                          |> List.map (fun (header, _) ->
                                 header.Exp.Header.name)
                          |> first_some (fun name ->
                                 candidate (prefix @ [ name ]))
                      | AbstractValue (name, _, _)
                      | ModuleIncludeItem (_, name, _, _, _, _)
                      | TypeSynonym (name, _)
                      | ModuleExpression (name, _, _, _)
                      | ModuleSynonym (name, _, _)
                      | SignatureSynonym (name, _, _) ->
                          candidate (prefix @ [ name ])
                      | Module (name, _, definitions, _) ->
                          let path = prefix @ [ name ] in
                          let* nested = search path definitions in
                          (match nested with
                          | Some _ -> return nested
                          | None -> candidate path)
                      | Documentation (_, definitions) ->
                          search prefix definitions
                      | ErrorMessage (_, definition) ->
                          search prefix [ definition ]
                      | TypeDefinition _
                      | ModuleInclude _
                      | Signature _
                      | Error _ ->
                          return None
                    in
                    (match result with
                    | Some _ -> return result
                    | None -> search prefix remaining)
              in
              search [] structure
            in
            let mixed_path_of_value_or_typ (outer_field : Name.t)
                (access : Name.t list) : MixedPath.t Monad.t =
              let rec remove_prefix prefix path =
                match (prefix, path) with
                | [], path -> Some path
                | prefix_name :: prefix, path_name :: path
                  when Name.equal prefix_name path_name ->
                    remove_prefix prefix path
                | _ -> None
              in
              let access =
                match access with
                | root :: _ when
                    List.exists
                      (fun (name, _, _, _) -> Name.equal name root)
                      local_module_bindings ->
                    access
                | _ ->
                    local_module_bindings
                    |> List.find_map
                         (fun (name, _, _, target_access) ->
                           match target_access with
                           | Some target_access -> (
                               match remove_prefix target_access access with
                               | Some (_ :: _ as fields) ->
                                   Some (name :: fields)
                               | Some [] | None -> None)
                           | None -> None)
                    |> Option.value ~default:access
              in
              let* local_access =
                flattened_local_access outer_field
              in
              match local_access with
              | Some access ->
                  let base = List.hd (List.rev access) in
                  let path =
                    List.rev (List.tl (List.rev access))
                  in
                  return
                    (local_mixed_path access
                       (PathName.of_name path base))
              | None -> (
              match access with
              | root :: fields when fields <> [] -> (
                  match
                    local_module_bindings
                    |> List.find_opt (fun (name, _, _, _) ->
                           Name.equal name root)
                  with
                  | Some (_, ident, declared_signature, _) ->
                      let module_path = Path.Pident ident in
                      let* signature_hint =
                        match declared_signature with
                        | Some _ as signature -> return signature
                        | None -> get_signature_hint module_path
                      in
                      (match signature_hint with
                      | Some signature_path ->
                          let* base =
                            PathName.of_path_with_convert false module_path
                          in
                          let strip_flattened_prefix outer_field prefix =
                            let prefix = Name.to_string prefix ^ "_" in
                            let operator_prefix = "op_" ^ prefix in
                            if
                              String.starts_with ~prefix:operator_prefix
                                outer_field
                            then
                              "op_"
                              ^ String.sub outer_field
                                  (String.length operator_prefix)
                                  (String.length outer_field
                                  - String.length operator_prefix)
                            else if
                              String.starts_with ~prefix outer_field
                            then
                              String.sub outer_field
                                (String.length prefix)
                                (String.length outer_field
                                - String.length prefix)
                            else outer_field
                          in
                          let rec nested_projection_fields signature_path
                              flattened_field = function
                            | [] -> return (Some [])
                            | [ field ] ->
                                let* field =
                                  PathName.of_path_and_name_with_convert
                                    signature_path field
                                in
                                return (Some [ field ])
                            | module_field :: remaining ->
                                let* field =
                                  PathName.of_path_and_name_with_convert
                                    signature_path module_field
                                in
                                let* child_signature =
                                  get_result_module_field signature_path
                                    (Name.to_string module_field)
                                in
                                (match child_signature with
                                | None ->
                                    let field =
                                      Name.of_string_raw flattened_field
                                    in
                                    let* field =
                                      PathName.of_path_and_name_with_convert
                                        signature_path field
                                    in
                                    return (Some [ field ])
                                | Some child_signature ->
                                    let* env = get_env in
                                    let child_signature =
                                      qualify_result_field_signature env
                                        signature_path child_signature
                                    in
                                    let* remaining =
                                      nested_projection_fields
                                        child_signature
                                        (strip_flattened_prefix
                                           flattened_field module_field)
                                        remaining
                                    in
                                    return
                                      (Option.map
                                         (fun remaining -> field :: remaining)
                                         remaining))
                          in
                          let* nested_projection_fields =
                            nested_projection_fields signature_path
                              (strip_flattened_prefix
                                 (Name.to_string outer_field)
                                 root)
                              fields
                          in
                          (match nested_projection_fields with
                          | Some projection_fields ->
                              if parameters = [] then
                                return
                                  (MixedPath.Access
                                     (base, projection_fields))
                              else
                                return
                                  (MixedPath.AppliedAccess
                                     ( base,
                                       [ ("_fargs", "_fargs") ],
                                       projection_fields ))
                          | None ->
                              let root_prefix = Name.to_string root ^ "_" in
                              let operator_root_prefix =
                                "op_" ^ root_prefix
                              in
                              let outer_field = Name.to_string outer_field in
                              let inner_field =
                                if List.length fields = 1 then
                                  String.concat "_"
                                    (List.map Name.to_string fields)
                                else if
                                  String.starts_with
                                    ~prefix:operator_root_prefix outer_field
                                then
                                  "op_"
                                  ^ String.sub outer_field
                                      (String.length operator_root_prefix)
                                      (String.length outer_field
                                      - String.length operator_root_prefix)
                                else if
                                  String.starts_with ~prefix:root_prefix
                                    outer_field
                                then
                                  String.sub outer_field
                                    (String.length root_prefix)
                                    (String.length outer_field
                                    - String.length root_prefix)
                                else outer_field
                              in
                              let field = Name.of_string_raw inner_field in
                              let* field =
                                PathName.of_path_and_name_with_convert
                                  signature_path field
                              in
                              if parameters = [] then
                                return (MixedPath.Access (base, [ field ]))
                              else
                                return
                                  (MixedPath.AppliedAccess
                                     ( base,
                                       [ ("_fargs", "_fargs") ],
                                       [ field ] )))
                      | None ->
                          let base = List.hd (List.rev access) in
                          let path =
                            List.rev (List.tl (List.rev access))
                          in
                          let* path_name =
                            PathName.convert (PathName.of_name path base)
                          in
                          return (local_mixed_path access path_name))
                  | None ->
                      let base = List.hd (List.rev access) in
                      let path = List.rev (List.tl (List.rev access)) in
                      let* path_name =
                        PathName.convert (PathName.of_name path base)
                      in
                      return (local_mixed_path access path_name))
              | _ -> (
              match List.rev access with
              | [] ->
                  raise
                    (MixedPath.of_name
                       (Name.of_string_raw "missing_access"))
                    Unexpected
                    "A module field has an empty local access path"
              | base :: rev_path ->
                  let* path_name =
                    PathName.convert
                      (PathName.of_name (List.rev rev_path) base)
                  in
                  return (local_mixed_path access path_name)))
            in
            let* e =
              Exp.build_module module_typ_params_arity values module_type_path
                mixed_path_of_value_or_typ
            in
            let* module_typ =
              match module_typ with
              | Some module_typ -> return (Some module_typ)
              | None ->
                  (match synthetic_typ_params with
                  | Some typ_params ->
                      let* signature_path =
                        PathName.of_path_with_convert false
                          module_type_path
                      in
                      return
                        (Some
                           (Type.Signature
                              ( signature_path,
                                List.map
                                  (fun (name, _) -> (name, None))
                                  typ_params )))
                  | None ->
                      let* translated_module_type =
                        ModuleTyp.of_types
                          ~abstract_functor_applications:true
                          ~result_signature_path:module_type_path
                          module_type
                      in
                      let _, parameters, _ = functor_parameters in
                      let functor_parameter_names =
                        List.map fst parameters
                      in
                      let* _, module_type =
                        ModuleTyp.to_typ functor_parameter_names
                          (Name.to_string name) true
                          translated_module_type
                      in
                      return
                        (Some
                           (instantiate_local_signature_types
                              module_type)))
            in
            return (Some (e, module_typ))
        | None -> return None
      in
      return (Module (name, functor_parameters, structure, e))
      in
      set_env source_structure.str_final_env (translate_structure ())
  | Tmod_ident (path, _) -> (
      match as_expression with
      | Some (module_type, _, _) ->
          let* module_exp =
            Exp.of_module_expr Name.Map.empty module_expr (Some module_type)
          in
          return (ModuleExpression (name, module_typ, None, module_exp))
      | None ->
          let rec root_and_fields path fields =
            match path with
            | Path.Pdot (prefix, field) ->
                root_and_fields prefix (field :: fields)
            | Path.Pextra_ty (prefix, Path.Pext_ty) ->
                root_and_fields prefix fields
            | Path.Pextra_ty (prefix, Path.Pcstr_ty field) ->
                root_and_fields prefix (field :: fields)
            | (Path.Pident _ | Path.Papply _) as root ->
                (root, fields)
          in
          let root_path, source_fields = root_and_fields path [] in
          let* root_signature = get_signature_hint root_path in
          let* flattened_namespace =
            match (root_signature, source_fields) with
            | Some root_signature, _ :: _
              when String.ends_with ~suffix:"_result"
                     (Path.last root_signature) ->
                let* reference =
                  PathName.of_path_with_convert false root_path
                in
                let* namespace_include =
                  get_result_namespace_include root_signature
                    (String.concat "_" source_fields)
                in
                let* included_record =
                  match namespace_include with
                  | None -> return None
                  | Some included_field ->
                      let* included_signature =
                        get_result_module_field root_signature
                          included_field
                      in
                      (match included_signature with
                      | None -> return None
                      | Some included_signature ->
                          let* included_name =
                            Name.of_string false included_field
                          in
                          let* field =
                            PathName.of_path_and_name_with_convert
                              root_signature included_name
                          in
                          return
                            (Some ([ field ], included_signature)))
                in
                let rec resolve_result_module_path signature_path
                    record_fields = function
                  | [] ->
                      return (Some (record_fields, signature_path))
                  | source_field :: remaining ->
                      let* field_signature =
                        get_result_module_field signature_path source_field
                      in
                      (match field_signature with
                      | Some field_signature ->
                          let* field_name =
                            Name.of_string false source_field
                          in
                          let* field =
                            PathName.of_path_and_name_with_convert
                              signature_path field_name
                          in
                          resolve_result_module_path field_signature
                            (record_fields @ [ field ]) remaining
                      | None -> return None)
                in
                let* result_module_path =
                  match included_record with
                  | Some _ -> return None
                  | None ->
                      resolve_result_module_path root_signature []
                        source_fields
                in
                let rec items_of_signature record_fields signature_path
                    flattened_prefix included_record signature =
                  let* translated_signature_path =
                    PathName.of_path_with_convert false signature_path
                  in
                  let signature_is_type_only =
                    String.equal
                      (PathName.to_string translated_signature_path)
                      "RocqOfOCaml.OCamlHashtbl.S"
                  in
                  signature
                  |> Monad.List.concat_map (fun signature_item ->
                         let ident =
                           Types.signature_item_id signature_item
                         in
                         let source_name = Ident.name ident in
                         match signature_item with
                         | Types.Sig_value
                             (_, { Types.val_type; _ }, _)
                           when not signature_is_type_only ->
                             let* name = Name.of_ident true ident in
                             let* typ, _, typ_vars =
                               Type.of_typ_expr true Name.Map.empty
                                 val_type
                             in
                             let* flattened_name =
                               Name.of_strings true
                                 (flattened_prefix @ [ source_name ])
                             in
                             let* field =
                               PathName.of_path_and_name_with_convert
                                 signature_path flattened_name
                             in
                             return
                               [
                                 ModuleIncludeItem
                                   ( IncludeProjectedValue,
                                     name,
                                     List.map fst typ_vars,
                                     Some typ,
                                     MixedPath.Access
                                       (reference, record_fields @ [ field ]),
                                     [] );
                               ]
                         | Types.Sig_value _ -> return []
                         | Types.Sig_type
                             ( ident,
                               { type_manifest; type_params; _ },
                               _,
                               _ ) ->
                             let* name = Name.of_ident false ident in
                             let manifest_contains_application =
                               match type_manifest with
                               | Some manifest ->
                                   Type
                                   .constructor_path_contains_functor_application
                                     manifest
                               | None -> false
                             in
                             let* concrete_manifest =
                               match (type_manifest, type_params) with
                               | Some _, _
                                 when Option.is_some included_record ->
                                   return None
                               | Some manifest, [] ->
                                   let* env = get_env in
                                   if
                                     manifest_contains_application
                                   then
                                     return
                                       (Signature
                                        .concrete_manifest_declaration env
                                          manifest)
                                   else return (Some manifest)
                               | (Some _, _) | (None, _) -> return None
                             in
                             (match concrete_manifest with
                             | Some manifest ->
                                 let* typ =
                                   Type.of_type_expr_without_free_vars
                                     manifest
                                 in
                                 return [ TypeSynonym (name, typ) ]
                             | None ->
                                 let projection_fields,
                                     projection_signature,
                                     projection_name =
                                   match included_record with
                                   | Some
                                       ( included_fields,
                                         included_signature ) ->
                                       ( included_fields,
                                         included_signature,
                                         [ source_name ] )
                                   | None ->
                                       ( record_fields,
                                         signature_path,
                                         flattened_prefix
                                         @ [ source_name ] )
                                 in
                                 let* flattened_name =
                                   Name.of_strings false projection_name
                                 in
                                 let* field =
                                   PathName.of_path_and_name_with_convert
                                     projection_signature flattened_name
                                 in
                                 let* _, _, typ_vars =
                                   Type.of_typs_exprs true type_params
                                     Name.Map.empty
                                 in
                                 return
                                   [
                                     ModuleIncludeItem
                                       ( IncludeType,
                                         name,
                                         List.map fst typ_vars,
                                         None,
                                         MixedPath.Access
                                           ( reference,
                                             projection_fields @ [ field ] ),
                                         [] );
                                   ])
                         | Types.Sig_module
                             (ident, _, { Types.md_type; _ }, _, _) -> (
                             let* nested_signature =
                               match
                                 Env.scrape_alias module_expr.mod_env
                                   md_type
                               with
                               | Mty_signature signature ->
                                   return (Some signature)
                               | _ -> return None
                               | exception _ -> return None
                             in
                             match nested_signature with
                             | None -> return []
                             | Some nested_signature ->
                                 let* module_name =
                                   Name.of_ident false ident
                                 in
                                 let flattened_module_name =
                                   String.concat "_"
                                     (flattened_prefix
                                     @ [ source_name ])
                                 in
                                 let* recorded_signature =
                                   get_result_module_field signature_path
                                     flattened_module_name
                                 in
                                 let rec functor_root_of_path path =
                                   match path with
                                   | Path.Papply
                                       (functor_path, _argument_path) ->
                                       functor_root_of_path functor_path
                                   | Path.Pdot _
                                   | Path.Pextra_ty _
                                   | Path.Pident _ ->
                                       path
                                 in
                                 let rec applied_functor_of_path path =
                                   match path with
                                   | Path.Papply _ ->
                                       Some (functor_root_of_path path)
                                   | Path.Pdot (prefix, _)
                                   | Path.Pextra_ty (prefix, _) ->
                                       applied_functor_of_path prefix
                                   | Path.Pident _ -> None
                                 in
                                 let rec applied_functor_of_type typ =
                                   match Types.get_desc typ with
                                   | Types.Tconstr (path, arguments, _) -> (
                                       match applied_functor_of_path path with
                                       | Some _ as functor_path ->
                                           functor_path
                                       | None ->
                                           arguments
                                           |> List.find_map
                                                applied_functor_of_type)
                                   | Types.Tarrow (_, left, right, _) -> (
                                       match applied_functor_of_type left with
                                       | Some _ as functor_path ->
                                           functor_path
                                       | None ->
                                           applied_functor_of_type right)
                                   | Types.Ttuple fields ->
                                       fields
                                       |> List.find_map (fun (_, typ) ->
                                              applied_functor_of_type typ)
                                   | Types.Tlink typ
                                   | Types.Tsubst (typ, _)
                                   | Types.Tpoly (typ, _) ->
                                       applied_functor_of_type typ
                                   | _ -> None
                                 in
                                 let rec applied_functor_of_module_type
                                     module_type =
                                   match
                                     Env.scrape_alias module_expr.mod_env
                                       module_type
                                   with
                                   | Mty_signature signature ->
                                       signature
                                       |> List.find_map (function
                                            | Types.Sig_type
                                                ( _,
                                                  {
                                                    Types.type_manifest =
                                                      Some manifest;
                                                    _;
                                                  },
                                                  _,
                                                  _ ) ->
                                                applied_functor_of_type
                                                  manifest
                                            | Types.Sig_value
                                                (_, { Types.val_type; _ }, _)
                                              ->
                                                applied_functor_of_type
                                                  val_type
                                            | Types.Sig_module
                                                ( _,
                                                  _,
                                                  {
                                                    Types.md_type;
                                                    _;
                                                  },
                                                  _,
                                                  _ ) ->
                                                applied_functor_of_module_type
                                                  md_type
                                            | _ -> None)
                                   | _ -> None
                                   | exception _ -> None
                                 in
                                 let* discovered_signature =
                                   match
                                     applied_functor_of_module_type md_type
                                   with
                                   | Some functor_path ->
                                       let* result_signature =
                                         get_functor_result_signature
                                           functor_path
                                       in
                                       (match result_signature with
                                       | None -> return None
                                       | Some result_signature ->
                                           let* result_module_type =
                                             get_module_type_hint
                                               result_signature
                                           in
                                           let nested_shape =
                                             match
                                               Env.scrape_alias
                                                 module_expr.mod_env md_type
                                             with
                                             | Mty_signature signature ->
                                                 Some
                                                   (SignatureShape
                                                    .of_signature None
                                                      signature)
                                             | _ -> None
                                             | exception _ -> None
                                           in
                                           (match
                                              ( result_module_type,
                                                nested_shape )
                                            with
                                           | Some result_module_type, Some shape
                                             when
                                               IsFirstClassModule
                                               .module_type_has_same_names_as_shape
                                                 module_expr.mod_env
                                                 result_module_type shape ->
                                               return
                                                 (Some result_signature)
                                           | _ -> return None))
                                   | None -> return None
                                 in
                                 let* module_kind =
                                   let* direct =
                                     IsFirstClassModule
                                     .is_module_typ_first_class
                                       ~include_hidden_hints:
                                         (record_fields <> []
                                         && Option.is_none
                                              result_module_path)
                                       md_type
                                       (Some (Path.Pident ident))
                                   in
                                   match
                                     ( direct,
                                       recorded_signature,
                                       discovered_signature )
                                   with
                                   | IsFirstClassModule.Found _, _, _ ->
                                       return direct
                                   | ( IsFirstClassModule.Not_found _,
                                       Some signature,
                                       _ )
                                   | ( IsFirstClassModule.Not_found _,
                                       None,
                                       Some signature ) ->
                                       return
                                         (IsFirstClassModule.Found
                                            signature)
                                   | ( IsFirstClassModule.Not_found _,
                                       None,
                                       None ) ->
                                       return direct
                                 in
                                 let* nested_items, module_value =
                                   match module_kind with
                                   | IsFirstClassModule.Found
                                       nested_signature_path ->
                                       let* flattened_name =
                                         Name.of_strings false
                                           (flattened_prefix
                                           @ [ source_name ])
                                       in
                                       let* field =
                                         PathName
                                         .of_path_and_name_with_convert
                                           signature_path flattened_name
                                       in
                                       let record_fields =
                                         record_fields @ [ field ]
                                       in
                                       let* nested_items =
                                         items_of_signature record_fields
                                           nested_signature_path []
                                           (Some
                                              ( record_fields,
                                                nested_signature_path ))
                                           nested_signature
                                       in
                                       return
                                         ( nested_items,
                                           Some
                                             (ModuleIncludeItem
                                                ( IncludeValue,
                                                  module_name,
                                                  [],
                                                  None,
                                                  MixedPath.Access
                                                    ( reference,
                                                      record_fields ),
                                                  [] )) )
                                   | IsFirstClassModule.Not_found _ ->
                                       let* nested_included_record =
                                         match
                                           ( result_module_path,
                                             included_record )
                                         with
                                         | Some _, _ -> return None
                                         | None, None -> return None
                                         | None, Some
                                             ( included_fields,
                                               included_signature ) ->
                                             let* hinted_signature =
                                               get_result_module_field
                                                 included_signature
                                                 source_name
                                             in
                                             let* nested_signature_path =
                                               match hinted_signature with
                                               | Some _ as signature ->
                                                   return signature
                                               | None ->
                                                   let* hidden =
                                                     IsFirstClassModule
                                                     .is_module_typ_first_class
                                                       ~include_hidden_hints:
                                                         true md_type
                                                       (Some
                                                          (Path.Pident
                                                             ident))
                                                   in
                                                   (match hidden with
                                                   | IsFirstClassModule.Found
                                                       signature ->
                                                       return
                                                         (Some signature)
                                                   | IsFirstClassModule
                                                     .Not_found _ ->
                                                       return None)
                                             in
                                             (match nested_signature_path with
                                             | None -> return None
                                             | Some nested_signature_path ->
                                                 let* field_name =
                                                   Name.of_string false
                                                     source_name
                                                 in
                                                 let* field =
                                                   PathName
                                                   .of_path_and_name_with_convert
                                                     included_signature
                                                     field_name
                                                 in
                                                 return
                                                   (Some
                                                      ( included_fields
                                                        @ [ field ],
                                                        nested_signature_path )))
                                       in
                                       let* nested_items =
                                         match nested_included_record with
                                         | Some
                                             ( included_fields,
                                               included_signature ) ->
                                             items_of_signature
                                               included_fields
                                               included_signature []
                                               nested_included_record
                                               nested_signature
                                         | None ->
                                             items_of_signature
                                               record_fields
                                               signature_path
                                               (flattened_prefix
                                               @ [ source_name ])
                                               None nested_signature
                                       in
                                       let module_value =
                                         Option.map
                                           (fun (fields, _) ->
                                             ModuleIncludeItem
                                               ( IncludeValue,
                                                 module_name,
                                                 [],
                                                 None,
                                                 MixedPath.Access
                                                   (reference, fields),
                                                 [] ))
                                           nested_included_record
                                       in
                                       return (nested_items, module_value)
                                 in
                                 return
                                   (Module
                                      ( module_name,
                                        ([], [], []),
                                        nested_items,
                                        None )
                                   :: Option.to_list module_value))
                         | Types.Sig_typext _
                         | Types.Sig_modtype _
                         | Types.Sig_class _
                         | Types.Sig_class_type _ ->
                             return [])
                in
                (match
                   Env.scrape_alias module_expr.mod_env
                     module_expr.mod_type
                 with
                | Mty_signature signature ->
                    let record_fields, signature_path, flattened_prefix,
                        included_record =
                      match result_module_path with
                      | Some (record_fields, signature_path) ->
                          ( record_fields,
                            signature_path,
                            [],
                            Some (record_fields, signature_path) )
                      | None ->
                          ( [],
                            root_signature,
                            source_fields,
                            included_record )
                    in
                    let* items =
                      items_of_signature record_fields signature_path
                        flattened_prefix
                        included_record signature
                    in
                    return (Some items)
                | _ -> return None
                | exception _ -> return None)
            | Some _, _ | None, _ -> return None
          in
          (match flattened_namespace with
          | Some structure ->
              return
                (Module (name, functor_parameters, structure, None))
          | None ->
              let* reference =
                PathName.of_path_with_convert false path
              in
              let is_functor =
                match
                  Env.scrape_alias module_expr.mod_env
                    module_expr.mod_type
                with
                | Mty_functor _ -> true
                | _ -> false
                | exception _ -> false
              in
              if
                (not is_functor)
                && source_fields = []
                && Option.is_some root_signature
              then
                let* module_exp =
                  Exp.of_module_expr Name.Map.empty module_expr None
                in
                let* application_fargs =
                  match root_signature with
                  | Some signature
                    when
                      String.ends_with ~suffix:"_result"
                        (Path.last signature) ->
                      let fargs_name =
                        Name.of_string_raw
                          (Name.to_string name ^ "_fargs")
                      in
                      let* target =
                        PathName.of_path_with_convert false path
                      in
                      let target =
                        {
                          target with
                          PathName.base =
                            Name.of_string_raw
                              (Name.to_string target.base ^ "_fargs");
                        }
                      in
                      return
                        (Some
                           ( fargs_name,
                             Exp.Variable
                               (MixedPath.PathName target, []) ))
                  | Some _ | None -> return None
                in
                return
                  (ModuleExpression
                     ( name,
                       module_typ,
                       application_fargs,
                       module_exp ))
              else
                return
                  (ModuleSynonym (name, reference, is_functor))))
  | Tmod_apply _ | Tmod_apply_unit _ ->
      let module_type_annotation =
        match module_type_annotation with
        | None -> None
        | Some module_type_annotation -> Some module_type_annotation.mty_type
      in
      let* module_exp =
        Exp.of_module_expr Name.Map.empty module_expr module_type_annotation
      in
      let rec root_functor_path (module_expr : Typedtree.module_expr) :
          Path.t option =
        match module_expr.mod_desc with
        | Tmod_ident (path, _) -> Some path
        | Tmod_apply (functor_expr, _, _)
        | Tmod_apply_unit functor_expr
        | Tmod_constraint (functor_expr, _, _, _) ->
            root_functor_path functor_expr
        | Tmod_structure _
        | Tmod_functor _
        | Tmod_unpack _
        | Tmod_typed_hole ->
            None
      in
      let rec application_arguments (e : Exp.t) : Exp.t list =
        match e with
        | Exp.Apply (f, arguments) ->
            application_arguments f @ List.filter_map Fun.id arguments
        | Exp.TypAnnotation (e, _) -> application_arguments e
        | _ -> []
      in
      let* application_fargs, module_typ =
        match root_functor_path module_expr with
        | None -> return (None, module_typ)
        | Some functor_path ->
            let* applied_child =
              get_applied_functor_child functor_path
            in
            let effective_functor_path =
              match applied_child with
              | Some (target, _) -> target
              | None -> functor_path
            in
            let* result_signature =
              get_functor_result_signature functor_path
            in
            (match result_signature with
            | None -> return (None, module_typ)
            | Some result_signature
              when not
                     (String.ends_with ~suffix:"_result"
                        (Path.last result_signature)) ->
                return (None, module_typ)
            | Some result_signature ->
                let* functor_name =
                  PathName.of_path_with_convert false
                    effective_functor_path
                in
                let build_fargs_path =
                  {
                    PathName.path =
                      functor_name.path @ [ functor_name.base ];
                    base = Name.of_string_raw "Build_FArgs";
                  }
                in
                let fargs_name =
                  Name.of_string_raw
                    (Name.to_string name ^ "_fargs")
                in
                let* build_fargs =
                  match applied_child with
                  | None ->
                      return
                        (MixedPath.PathName build_fargs_path)
                  | Some (_, parent_application) ->
                      let* parent_name =
                        PathName.of_path_with_convert false
                          parent_application
                        >>= PathName.to_name false
                      in
                      let parent_fargs =
                        Name.to_string parent_name ^ "_fargs"
                      in
                      return
                        (MixedPath.AppliedAccess
                           ( build_fargs_path,
                             [ ("_fargs", parent_fargs) ],
                             [] ))
                in
                let fargs_value =
                  Exp.Apply
                    ( Exp.Variable
                        (build_fargs, []),
                      application_arguments module_exp
                      |> List.map Option.some )
                in
                let* result_signature =
                  PathName.of_path_with_convert false result_signature
                in
                let result_typ =
                  Type.Signature
                    ( result_signature,
                      [
                        ( Name.of_string_raw "_fargs",
                          Some (Type.Variable fargs_name) );
                      ] )
                in
                return
                  ( Some (fargs_name, fargs_value),
                    Some result_typ ))
      in
      return
        (ModuleExpression
           (name, module_typ, application_fargs, module_exp))
  | Tmod_functor (parameter, module_expr) ->
      let* functor_parameters, parameter_signature_hint =
        match parameter with
        | Unit -> return (functor_parameters, None)
        | Named (ident, _, module_type_arg) ->
            let* x = Name.of_optional_ident false ident in
            let id = Name.string_of_optional_ident ident in
            let synthetic_signature_name =
              Name.to_string name ^ "_" ^ id ^ "_signature"
            in
            let* reusable_signature_hint =
              match binding_path with
              | Some functor_path ->
                  get_anonymous_functor_parameter functor_path id
              | None -> return None
            in
            let* named_signature, uses_reusable_signature =
              match reusable_signature_hint with
              | Some signature_path
                when
                  not
                    (String.equal (Path.last signature_path)
                       synthetic_signature_name) ->
                  return (IsFirstClassModule.Found signature_path, true)
              | Some _ | None ->
                  let* named_signature =
                    IsFirstClassModule.is_module_typ_first_class
                      module_type_arg.mty_type None
                  in
                  return (named_signature, false)
            in
            let* module_type_arg, parameter_signature, signature_hint =
              match (module_type_arg.mty_desc, named_signature) with
              | _, IsFirstClassModule.Found signature_path ->
                  let* module_type_arg =
                    if uses_reusable_signature then
                      let* module_type_arg =
                        ModuleTyp.of_ocaml_module_with_substitutions
                          signature_path []
                      in
                      return ([], module_type_arg)
                    else
                      ModuleTyp.of_ocaml module_type_arg
                  in
                  return (module_type_arg, None, Some signature_path)
              | Tmty_signature signature, IsFirstClassModule.Not_found _ ->
                  let* signature_name =
                    Name.of_string false
                      (Name.to_string name ^ "_" ^ id ^ "_signature")
                  in
                  let* signature =
                    set_env module_type_arg.mty_env
                      (Signature.of_types_signature signature.sig_type)
                  in
                  let signature_path_name =
                    PathName.of_name [] signature_name
                  in
                  let typ_values =
                    signature.Signature.typ_params
                    |> List.map (fun (typ_name, arity) ->
                           Tree.Item
                             ( Name.to_string typ_name,
                               Type.Arity arity ))
                  in
                  let parameter_paths =
                    signature.Signature.typ_params
                    |> List.map (fun (typ_name, _) ->
                           [ Name.to_string typ_name ])
                  in
                  let synthetic_ident =
                    Ident.create_local (Name.to_string signature_name)
                  in
                  return
                    ( ( [],
                        ModuleTyp.Module.With
                          ( signature_path_name,
                            typ_values,
                            parameter_paths,
                            [] ) ),
                      Some (signature_name, signature),
                      Some (Path.Pident synthetic_ident) )
              | _, IsFirstClassModule.Not_found _ ->
                  let* module_type_arg = ModuleTyp.of_ocaml module_type_arg in
                  return (module_type_arg, None, None)
            in
            let* (_, _, free_vars_arg), typ_arg =
              ModuleTyp.to_typ [] id false module_type_arg
            in
            let free_vars_params, params, parameter_signatures =
              functor_parameters
            in
            let parameter_signatures =
              match parameter_signature with
              | Some parameter_signature ->
                  parameter_signatures @ [ parameter_signature ]
              | None -> parameter_signatures
            in
            return
              ( ( free_vars_params @ free_vars_arg,
                  params @ [ (x, typ_arg) ],
                  parameter_signatures ),
                signature_hint )
      in
      let body =
        of_module ?binding_path ~has_enclosing_fargs name
          functor_parameters module_expr false
      in
      (match (parameter, parameter_signature_hint) with
      | Named (Some ident, _, _), Some signature_path ->
          set_signature_hint (Path.Pident ident) signature_path body
      | Named (Some _, _, _), None
      | Named (None, _, _), _
      | Unit, _ ->
          body)
  | Tmod_constraint (module_expr, _, annotation, _) ->
      let module_type_annotation =
        match as_expression with
        | Some _ -> None
        | None -> (
            match annotation with
            | Tmodtype_explicit module_type -> Some module_type
            | Tmodtype_implicit -> module_type_annotation)
      in
      of_module_expr ?binding_path ~has_enclosing_fargs name
        functor_parameters as_expression module_type_annotation module_expr
  | Tmod_unpack _ ->
      return
        (Error
           "Cannot unpack first-class modules at top-level due to a universe \
            inconsistency")
  | Tmod_typed_hole ->
    return
      (Error
         "Holes not supported")

(** Pretty-print a structure to Rocq. *)
let rec to_coq (fargs : FArgs.t) (defs : t list) : SmartPrint.t =
  let rec to_coq_one (def : t) : SmartPrint.t =
    match def with
    | Value value -> Value.to_coq fargs value
    | AbstractValue (name, typ_vars, typ) ->
        nest
          (!^"Parameter" ^^ Name.to_coq name ^^ !^":"
          ^^ Name.to_coq_list_or_empty typ_vars (fun typ_vars ->
                 !^"forall"
                 ^^ nest (parens (typ_vars ^^ !^":" ^^ Pp.set))
                 ^-^ !^",")
          ^^ Type.to_coq None None typ ^-^ !^".")
    | TypeDefinition typ_def -> TypeDefinition.to_coq fargs typ_def
    | Module
        ( name,
          (free_vars_params, params, parameter_signatures),
          defs,
          e ) ->
        let is_functor = match params with [] -> false | _ :: _ -> true in
        let fargs_instance =
          nest
            (Name.to_coq name ^-^ !^"." ^-^ !^"Build_FArgs"
            ^^ separate space
                 (params |> List.map (fun (name, _) -> Name.to_coq name)))
        in
        let explicit_functor_args =
          FArgs.to_coq_underscores fargs
          @ List.map
              (fun { ModuleTyp.name; _ } -> Name.to_coq name)
              free_vars_params
          @ [ parens fargs_instance ]
        in
        let nb_new_fargs_typ_params = List.length free_vars_params in
        let nb_fargs_typ_params =
          match fargs with
          | None -> nb_new_fargs_typ_params
          | Some fargs -> 1 + fargs + nb_new_fargs_typ_params
        in
        let inner_fargs =
          if is_functor then
            match fargs with
            | None -> Some nb_new_fargs_typ_params
            | Some fargs ->
                Some (fargs + 1 + nb_new_fargs_typ_params)
          else fargs
        in
        let result_signature_dependencies =
          FArgs.to_coq_underscores fargs
          @ List.map
              (fun { ModuleTyp.name; _ } -> Name.to_coq name)
              free_vars_params
        in
        let result_field_implicits =
          List.map
            (fun { ModuleTyp.name; _ } -> (name, Name.to_coq name))
            free_vars_params
          @
          match inner_fargs with
          | Some _ ->
              let fargs_name = Name.of_string_raw "_fargs" in
              [ (fargs_name, Name.to_coq fargs_name) ]
          | None -> []
        in
        let to_coq_result_type (typ : Type.t) : SmartPrint.t =
          match (inner_fargs, typ) with
          | ( Some _,
              Type.Signature (path, []) )
            when String.ends_with
                   ~suffix:"_result"
                   (Name.to_string path.PathName.base) ->
              nest
                (separate space
                   ((!^"@" ^-^ PathName.to_coq path)
                   :: result_signature_dependencies
                   @ [ !^"_fargs" ]))
          | _ -> Type.to_coq None None typ
        in
        let to_coq_result_value (e : Exp.t) (typ : Type.t option) :
            SmartPrint.t =
          match (inner_fargs, typ) with
          | ( Some _,
              Some (Type.Signature (path, []) as typ) )
            when String.ends_with
                   ~suffix:"_result"
                   (Name.to_string path.PathName.base) ->
              parens
                (nest
                   (Exp.to_coq_record_with_field_implicits
                      result_field_implicits e
                  ^^ !^":"
                  ^^ to_coq_result_type typ))
          | _ -> Exp.to_coq false e
        in
        let final_item_name = if is_functor then !^"functor" else !^"module" in
        let parameter_signature_definitions =
          parameter_signatures
          |> List.map (fun (signature_name, signature) ->
                 Signature.to_coq_definition fargs signature_name signature)
        in
        (match parameter_signature_definitions with
        | [] -> empty
        | _ :: _ ->
            separate (newline ^^ newline) parameter_signature_definitions
            ^^ newline ^^ newline)
        ^^ nest
          (!^"Module" ^^ Name.to_coq name ^-^ !^"." ^^ newline
          ^^ indent
               ((if is_functor then
                 nest
                   (!^"Class" ^^ !^"FArgs" ^^ FArgs.to_coq fargs
                   ^^ ModuleTyp.to_coq_grouped_free_vars free_vars_params
                   ^^ !^":=" ^^ !^"{" ^^ newline
                   ^^ indent
                        (separate empty
                           (params
                           |> List.map (fun (name, typ) ->
                                  nest
                                    (Name.to_coq name ^^ !^":"
                                   ^^ Type.to_coq None None typ ^-^ !^";"
                                   ^^ newline))))
                   ^^ !^"}" ^-^ !^"." ^^ newline
                   ^^ (if nb_fargs_typ_params = 0 then empty
                      else
                        !^"Arguments" ^^ !^"Build_FArgs"
                        ^^ braces
                             (nest
                                (separate space
                                   (Pp.n_underscores nb_fargs_typ_params)))
                        ^-^ !^"." ^^ newline)
                   ^^ newline)
                else empty)
               ^^ to_coq inner_fargs defs
               ^^
               match e with
               | Some (e, typ_annotation) ->
                   newline ^^ newline
                   ^^ nest (!^"(*" ^^ Name.to_coq name ^^ !^"*)")
                   ^^ newline
                   ^^ nest
                        (!^"Definition" ^^ final_item_name
                        ^^ (if is_functor then FArgs.to_coq inner_fargs
                           else FArgs.to_coq fargs)
                        ^^ (match typ_annotation with
                           | Some typ_annotation ->
                               !^":" ^-^ to_coq_result_type typ_annotation
                           | None -> empty)
                        ^^ !^":=" ^^ to_coq_result_value e typ_annotation
                        ^-^ !^".")
               | None -> empty)
          ^^ newline ^^ !^"End" ^^ Name.to_coq name ^-^ !^"."
          ^^
          match e with
          | Some (_, _) ->
              newline
              ^^ nest
                   (!^"Definition" ^^ Name.to_coq name ^^ FArgs.to_coq fargs
                   ^^ ModuleTyp.to_coq_functor_parameters_modules
                        free_vars_params params
                   ^^ !^":="
                   ^^ nest
                        ((if is_functor then
                          nest
                            (separate space
                               ((!^"@"
                                 ^-^ Name.to_coq name
                                 ^-^ !^"."
                                 ^-^ final_item_name)
                               :: explicit_functor_args))
                         else
                           Name.to_coq name
                           ^-^ !^"."
                           ^-^ final_item_name)
                        ^-^ !^"."))
          | None -> empty)
    | ModuleExpression (name, typ, application_fargs, e) ->
        (match application_fargs with
        | None -> empty
        | Some (fargs_name, fargs_value) ->
            nest
              (!^"Definition" ^^ Name.to_coq fargs_name
              ^^ FArgs.to_coq fargs
              ^^ !^":=" ^^ Exp.to_coq false fargs_value ^-^ !^".")
            ^^ newline ^^ newline)
        ^^ nest
             (!^"Definition" ^^ Name.to_coq name ^^ FArgs.to_coq fargs
             ^^ (match typ with
                | None -> empty
                | Some typ -> !^":" ^^ Type.to_coq None None typ)
             ^^ !^":=" ^^ Exp.to_coq false e ^-^ !^".")
    | ModuleInclude reference ->
        nest (!^"Include" ^^ PathName.to_coq reference ^-^ !^".")
    | ModuleIncludeItem
        (kind, name, typ_vars, typ, mixed_path, stored_requirements) ->
        let requirements =
          match stored_requirements with
          | _ :: _ -> stored_requirements
          | [] ->
              module_include_assumptions kind typ_vars typ mixed_path
        in
        let assumption_arguments =
          requirements
          |> List.mapi (fun index requirement ->
                 !^"`"
                 ^-^ braces
                      (nest
                         (!^(Printf.sprintf "_rocq_assumption_%d" index)
                         ^^ !^":"
                         ^^ Type.to_coq None None
                              (Exp.assumption_class_type requirement))))
          |> separate space
        in
        nest
          (!^"Definition" ^^ Name.to_coq name ^^ FArgs.to_coq fargs
          ^^ Name.to_coq_list_or_empty typ_vars (fun typ_vars ->
                 let binder = typ_vars ^^ !^":" ^^ Pp.set in
                 match kind with
                 | IncludeValue | IncludeProjectedValue ->
                     nest (braces binder)
                 | IncludeType -> nest (parens binder))
          ^^ assumption_arguments
          ^^
          (match (kind, typ) with
          | IncludeValue, Some typ -> !^":" ^^ Type.to_coq None None typ
          | (IncludeValue | IncludeProjectedValue), None
          | IncludeProjectedValue, Some _
          | IncludeType, _ ->
              empty)
          ^^ !^":="
          ^^ nest
               (match kind with
               | IncludeValue -> MixedPath.to_coq mixed_path
               | IncludeProjectedValue ->
                   separate space
                     (MixedPath.to_coq mixed_path
                     :: List.map
                          (fun typ_var ->
                            parens
                              (Name.to_coq typ_var ^^ !^":="
                              ^^ Name.to_coq typ_var))
                          typ_vars)
               | IncludeType ->
                   separate space
                     (MixedPath.to_coq mixed_path
                     :: List.map Name.to_coq typ_vars))
          ^-^ !^".")
    | TypeSynonym (name, typ) ->
        nest
          (!^"Definition" ^^ Name.to_coq name ^^ !^":="
          ^^ Type.to_coq None None typ ^-^ !^".")
    | ModuleSynonym (name, reference, is_functor) ->
        nest
          (!^"Module" ^^ Name.to_coq name ^^ !^":=" ^^ PathName.to_coq reference
          ^-^ !^"."
          ^^
          if is_functor then
            newline
            ^^ !^"Definition" ^^ Name.to_coq name ^^ !^":="
            ^^ !^"@" ^-^ PathName.to_coq reference ^-^ !^"." ^^ newline
            ^^ !^"Arguments" ^^ Name.to_coq name
            ^^ !^": default implicits."
          else empty)
    | Signature (name, signature) ->
        Signature.to_coq_definition fargs name signature
    | SignatureSynonym (name, reference, nb_typ_params) ->
        nest
          (!^"Module" ^^ Name.to_coq name ^^ !^":="
          ^^ PathName.to_coq reference ^-^ !^"." ^^ newline
          ^^ !^"Definition" ^^ Name.to_coq name ^^ !^":="
          ^^ !^"@" ^-^ Name.to_coq name ^-^ !^"." ^-^ !^"signature" ^-^ !^"."
          ^^
          if nb_typ_params = 0 && fargs = None then empty
          else
            newline
            ^^ nest
                 (!^"Arguments" ^^ Name.to_coq name
                 ^^ braces
                      (separate space
                         (FArgs.to_coq_underscores fargs
                         @ Pp.n_underscores nb_typ_params))
                 ^-^ !^"."))
    | Documentation (message, defs) ->
        nest (!^("(** " ^ message ^ " *)") ^^ newline ^^ to_coq fargs defs)
    | Error message -> !^("(* " ^ message ^ " *)")
    | ErrorMessage (message, def) ->
        nest (Error.to_comment message ^^ newline ^^ to_coq_one def)
  in
  separate (newline ^^ newline) (defs |> List.map to_coq_one)
