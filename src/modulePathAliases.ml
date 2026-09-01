(** Local names for applicative functor paths recovered from the typed tree.

    OCaml strengthens the result of [module M = F (X)] with paths rooted at
    [F(X)].  Rocq-of-ocaml emits the result once, under the local name [M], so
    later references to [F(X).t] must use [M.t] in the generated Gallina.

    Source module aliases are also useful when Rocq's namespace rules would
    shadow an earlier module inside a same-named module body.  Their source
    positions ensure that an alias is used only after its declaration, never
    as a forward reference or while translating its own right-hand side.

    This prepass records the compiler paths themselves rather than comparing
    printed names.  Consequently, lexical scoping and shadowing continue to be
    determined by OCaml's type checker. *)

type alias = {
  source : Path.t;
  target : Path.t;
  available_after : int;
  scope_start : int;
  scope_end : int;
}

type t = alias list

let empty : t = []

let find (path : Path.t) (location : Location.t) (aliases : t) : Path.t option =
  let current_position = location.loc_start.pos_cnum in
  aliases
  |> List.filter (fun alias ->
         alias.available_after <= current_position
         && alias.scope_start <= current_position
         && current_position <= alias.scope_end
         && Path.same path alias.source)
  |> List.sort (fun left right ->
         let left_size = left.scope_end - left.scope_start in
         let right_size = right.scope_end - right.scope_start in
         match Int.compare left_size right_size with
         | 0 -> Int.compare right.available_after left.available_after
         | ordering -> ordering)
  |> List.find_map (fun alias -> Some alias.target)

(** Recover the source of an alias from its generated local target.  This is
    used to carry module-signature information across bindings such as
    [module Alias = Parameter], where the parameter is represented by a Rocq
    record and field accesses must remain record projections. *)
let find_source (path : Path.t) (location : Location.t) (aliases : t) :
    Path.t option =
  let current_position = location.loc_start.pos_cnum in
  aliases
  |> List.filter (fun alias ->
         alias.available_after <= current_position
         && alias.scope_start <= current_position
         && current_position <= alias.scope_end
         && Path.same path alias.target)
  |> List.sort (fun left right ->
         let left_size = left.scope_end - left.scope_start in
         let right_size = right.scope_end - right.scope_start in
         match Int.compare left_size right_size with
         | 0 -> Int.compare right.available_after left.available_after
         | ordering -> ordering)
  |> List.find_map (fun alias -> Some alias.source)

let rec module_expr_path (module_expr : Typedtree.module_expr) : Path.t option =
  let normalize path =
    Env.normalize_module_path None module_expr.mod_env path
  in
  match module_expr.mod_desc with
  | Tmod_ident (path, _) -> Some (normalize path)
  | Tmod_apply (functor_expr, argument_expr, _) -> (
      match
        (module_expr_path functor_expr, module_expr_path argument_expr)
      with
      | Some functor_path, Some argument_path ->
          Some (normalize (Path.Papply (functor_path, argument_path)))
      | _ -> None)
  | Tmod_constraint (inner, _, _, _) -> module_expr_path inner
  | Tmod_structure _
  | Tmod_functor _
  | Tmod_apply_unit _
  | Tmod_unpack _
  | Tmod_typed_hole ->
      None

let of_typedtree (typedtree : Merlin_kernel.Mtyper.typedtree) : t =
  let aliases = ref empty in
  let scope_stack = ref [] in
  let structure_scope (structure : Typedtree.structure) :
      (int * int) option =
    match structure.str_items with
    | [] -> None
    | first :: _ ->
        let last = List.hd (List.rev structure.str_items) in
        Some
          ( first.str_loc.loc_start.pos_cnum,
            last.str_loc.loc_end.pos_cnum )
  in
  let add (scope_start, scope_end) (ident : Ident.t option)
      (module_expr : Typedtree.module_expr) : unit =
    match (ident, module_expr_path module_expr) with
    | Some ident, Some source ->
        let is_source_alias =
          match module_expr.mod_desc with
          | Tmod_ident _
          | Tmod_constraint ({ mod_desc = Tmod_ident _; _ }, _, _, _) ->
              true
          | _ -> false
        in
        if is_source_alias || match source with Path.Papply _ -> true | _ -> false
        then
          aliases :=
            {
              source;
              target = Path.Pident ident;
              available_after = module_expr.mod_loc.loc_end.pos_cnum;
              scope_start;
              scope_end;
            }
            :: !aliases
    | _ -> ()
  in
  let open Tast_iterator in
  let iterator =
    {
      default_iterator with
      structure =
        (fun self structure ->
          let previous = !scope_stack in
          scope_stack :=
            Option.fold ~none:previous
              ~some:(fun scope -> scope :: previous)
              (structure_scope structure);
          default_iterator.structure self structure;
          scope_stack := previous);
      module_binding =
        (fun self binding ->
          Option.iter
            (fun scope -> add scope binding.mb_id binding.mb_expr)
            (List.find_opt (fun _ -> true) !scope_stack);
          default_iterator.module_binding self binding);
      expr =
        (fun self expression ->
          (match expression.exp_desc with
          | Texp_letmodule (ident, _, _, module_expr, body) ->
              add
                ( body.exp_loc.loc_start.pos_cnum,
                  body.exp_loc.loc_end.pos_cnum )
                ident module_expr
          | _ -> ());
          default_iterator.expr self expression);
    }
  in
  (match typedtree with
  | `Implementation structure -> iterator.structure iterator structure
  | `Interface signature -> iterator.signature iterator signature);
  List.rev !aliases
