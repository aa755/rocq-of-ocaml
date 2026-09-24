(** Preserve the source owner of value declarations through local functor
    applications and aliases. Printed Rocq projections can omit enclosing
    modules; the compiler's declaration UID still identifies the source. *)

type origin = {
  source : string option;
  definition : string list;
  partial_attribute : bool;
  parameters : string option list;
}
type t = origin Types.Uid.Map.t

let find uid origins = Types.Uid.Map.find_opt uid origins

let source_configuration (configuration : Configuration.t) (origin : origin) =
  match origin.source with
  | Some source -> { configuration with file_name = source }
  | None -> configuration

let parameter_names (expression : Typedtree.expression) : string option list =
  match expression.exp_desc with
  | Texp_function (parameters, _) ->
      List.map
        (fun parameter ->
          let pattern =
            match parameter.Typedtree.fp_kind with
            | Tparam_pat pattern | Tparam_optional_default (pattern, _) ->
                pattern
          in
          match pattern.pat_desc with
          | Tpat_var (ident, _, _) | Tpat_alias (_, ident, _, _, _) ->
              Some (Ident.name ident)
          | _ -> None)
        parameters
  | _ -> []

let partial_parameter_indices (configuration : Configuration.t)
    (definition : string list) (parameters : string option list) : int list =
  parameters
  |> List.mapi (fun index parameter ->
         match parameter with
         | Some name
           when Configuration.is_partial_value configuration
                  (definition @ [ name ]) ->
             Some index
         | _ -> None)
  |> List.filter_map Fun.id

let of_typedtree ?source (typedtree : Merlin_kernel.Mtyper.typedtree) : t =
  let origins = ref Types.Uid.Map.empty in
  let path = ref [] in
  let partial_attribute = ref false in
  let scoped name f =
    let previous = !path in
    path := previous @ [ name ];
    f ();
    path := previous
  in
  let open Tast_iterator in
  let iterator =
    {
      default_iterator with
      module_binding =
        (fun self binding ->
          match binding.Typedtree.mb_id with
          | Some ident ->
              scoped (Ident.name ident) (fun () ->
                  default_iterator.module_binding self binding)
          | None -> default_iterator.module_binding self binding);
      value_binding =
        (fun self binding ->
          partial_attribute :=
            List.exists
              (fun attribute ->
                let name = attribute.Parsetree.attr_name.txt in
                name = "rocq.partial" || name = "rocq_partial")
              binding.Typedtree.vb_attributes;
          self.pat self binding.vb_pat;
          partial_attribute := false;
          match binding.vb_pat.pat_desc with
          | Tpat_var (ident, _, uid) | Tpat_alias (_, ident, _, uid, _) ->
              origins :=
                Types.Uid.Map.update uid
                  (Option.map (fun origin ->
                       { origin with
                         parameters = parameter_names binding.vb_expr }))
                  !origins;
              scoped (Ident.name ident) (fun () ->
                  self.expr self binding.vb_expr)
          | _ -> self.expr self binding.vb_expr);
      pat =
        (fun (type kind) self
             (pattern : kind Typedtree.general_pattern) ->
          (match pattern.pat_desc with
          | Tpat_var (ident, _, uid) | Tpat_alias (_, ident, _, uid, _) ->
              origins :=
                Types.Uid.Map.add uid
                  { source;
                    definition = !path @ [ Ident.name ident ];
                    partial_attribute = !partial_attribute;
                    parameters = [] }
                  !origins
          | _ -> ());
          default_iterator.pat self pattern);
      expr =
        (fun self expression ->
          match expression.Typedtree.exp_desc with
          | Texp_letmodule (Some ident, _, _, module_expr, body) ->
              scoped (Ident.name ident) (fun () ->
                  self.module_expr self module_expr);
              self.expr self body
          | _ -> default_iterator.expr self expression);
    }
  in
  (match typedtree with
  | `Implementation structure -> iterator.structure iterator structure
  | `Interface signature -> iterator.signature iterator signature);
  !origins
