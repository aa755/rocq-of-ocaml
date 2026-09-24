(** Preserve the source owner of value declarations through local functor
    applications and aliases. Printed Rocq projections can omit enclosing
    modules; the compiler's declaration UID still identifies the source. *)

type origin = { definition : string list; partial_attribute : bool }
type t = origin Types.Uid.Map.t

let find uid origins = Types.Uid.Map.find_opt uid origins

let of_typedtree (typedtree : Merlin_kernel.Mtyper.typedtree) : t =
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
          | Tpat_var (ident, _, _) | Tpat_alias (_, ident, _, _, _) ->
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
                  { definition = !path @ [ Ident.name ident ];
                    partial_attribute = !partial_attribute }
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
