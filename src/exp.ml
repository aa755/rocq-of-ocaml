open Typedtree
(** An expression. *)

open SmartPrint
open Monad.Notations

module Header = struct
  type t = {
    name : Name.t;
    typ_vars : VarEnv.t;
    args : (Name.t * Type.t) list;
    instance_args : (Name.t * Type.t) list;
    structs : string list;
    typ : Type.t;
    is_notation : bool;
  }

  let to_coq_structs (header : t) : SmartPrint.t =
    match header.structs with
    | [] -> empty
    | _ :: _ ->
        let structs = separate space (List.map (fun s -> !^s) header.structs) in
        braces (nest (!^"struct" ^^ structs))

  let to_coq_instance_args (header : t) : SmartPrint.t =
    header.instance_args
    |> List.map (fun (name, typ) ->
           !^"`"
           ^-^ braces
                (nest
                   (Name.to_coq name ^^ !^":"
                   ^^ Type.to_coq None None typ)))
    |> separate space
end

module Definition = struct
  type partial_recursion =
    | MayDiverge
    | StructurallyTerminates
    | WellFoundedTerminates of string

  type partial_details = {
    definition_name : string;
    partial_definitions : string list;
    recursion : partial_recursion;
  }

  type recursion_strategy =
    | Structural
    | WellFounded of string
    | Partial of partial_details
    | Convergent of string

  type 'a t = {
    is_rec : Recursivity.t;
    recursion_strategy : recursion_strategy;
    term_environment : Name.t list;
    cases : (Header.t * 'a) list;
  }
end

type match_existential_cast = {
  new_typ_vars : VarEnv.t;
  bound_vars : (Name.t * Type.t) list;
  return_typ : Type.t;
  use_axioms : bool;
  cast_result : bool;
  enable : bool;
}

type dependent_pattern_match = {
  cast : Type.t;
  motive : Type.t;
  args : Type.t list;
}

type assumption_kind = Unreachable | Unimplemented

let partial_operation_names =
  [
    "List.hd";
    "List.tl";
    "List.nth";
    "List.nth_opt";
    "List.init";
    "List.map2";
    "List.rev_map2";
    "List.iter2";
    "List.fold_left2";
    "List.fold_right2";
    "List.for_all2";
    "List.exists2";
    "List._exists2";
    "List.assoc";
    "List.assq";
    "List.find";
    "List.combine";
    "Seq.init";
    "Seq.take";
    "Seq.drop";
    "Seq.once";
    "Hashtbl.find";
  ]

let string_ends_with (value : string) (suffix : string) : bool =
  let value_length = String.length value in
  let suffix_length = String.length suffix in
  value_length >= suffix_length
  && String.sub value (value_length - suffix_length) suffix_length = suffix

let rec drop_closing_parentheses path =
  let length = String.length path in
  if length > 0 && path.[length - 1] = ')' then
    drop_closing_parentheses (String.sub path 0 (length - 1))
  else path

let target_partial_operation_name (name : string) : string =
  let replace_prefix source target value =
    let source_length = String.length source in
    if
      String.length value >= source_length
      && String.sub value 0 source_length = source
    then
      target
      ^ String.sub value source_length (String.length value - source_length)
    else value
  in
  name
  |> replace_prefix "List." "OCamlList."
  |> replace_prefix "Seq." "OCamlSeq."
  |> replace_prefix "Hashtbl." "OCamlHashtbl."

let is_partial_operation_name (path : string) : bool =
  let path = drop_closing_parentheses path in
  List.exists
    (fun name ->
      let target_name = target_partial_operation_name name in
      let target_signature_name =
        match String.rindex_opt target_name '.' with
        | None -> target_name
        | Some separator ->
            String.sub target_name 0 separator
            ^ ".S"
            ^ String.sub target_name separator
                (String.length target_name - separator)
      in
      path = name
      || path = "Stdlib." ^ name
      || string_ends_with path ("." ^ name)
      || path = target_name
      || string_ends_with path ("." ^ target_name)
      || path = target_signature_name
      || string_ends_with path ("." ^ target_signature_name))
    partial_operation_names

let is_partial_operation_field_name (path : string) : bool =
  let path = drop_closing_parentheses path in
  List.exists
    (fun name ->
      let flattened =
        String.map (function '.' -> '_' | character -> character) name
      in
      path = flattened
      || string_ends_with path ("." ^ flattened)
      || string_ends_with path ("_" ^ flattened))
    partial_operation_names

let is_generated_map_of_yojson_name (path : string) : bool =
  let path = drop_closing_parentheses path in
  path = "Map_signature.of_yojson"
  || string_ends_with path ".Map_signature.of_yojson"

let is_partial_operation_path (path : Path.t) : bool =
  is_partial_operation_name (Path.name path)

(** The simplified OCaml AST we use. We do not use a mutualy recursive type to
    simplify the importation in Rocq. *)
type t =
  | Constant of Constant.t
  | Variable of MixedPath.t * (string * string) list
  | Tuple of t list  (** A tuple of expressions. *)
  | Constructor of PathName.t * (string * string) list * t list
      (** A constructor name, some implicits, and a list of arguments. *)
  | ConstructorExtensible of string * Type.t * t
      (** A constructor of an extensible type, with a tag and a payload. *)
  | ConstructorVariant of string * (Type.t * t) option
      (** A constructor of polymorphic variant, with a tag and a payload. *)
  | Apply of t * t option list  (** An application. *)
  | SourceApply of t * t option list * Type.t
      (** An application from the typed OCaml tree, retaining its result type
          for propagation of generated type-class requirements. *)
  | Return of string * t  (** Application specialized for a return operation. *)
  | InfixOperator of string * t * t
      (** Application specialized for an infix operator.
        An argument name, an optional type and a body. *)
  | Function of Name.t * Type.t option * t
  | Functions of Name.t list * t  (** An argument names and a body. *)
  | LetVar of string option * Name.t * Name.t list * t * t
      (** The let of a variable, with optionally a list of polymorphic variables.
        We optionally specify the symbol of the let operator as it may be
        non-standard for monadic binds. *)
  | LetFun of t option Definition.t * t
  | LetTyp of Name.t * Name.t list * Type.t * t
      (** The definition of a type. It is used to represent module values. *)
  | LetModuleUnpack of Name.t * PathName.t * t
      (** Open a first-class module. *)
  | Match of
      t
      * dependent_pattern_match option
      * (Pattern.t * match_existential_cast option * t) list
      * bool  (** Match an expression to a list of patterns. *)
  | MatchExtensible of
      t * Type.t * ((string * Pattern.t * Type.t) option * t) list
      (** Match an expression on a list of extensible type patterns. *)
  | MatchVariant of t * Type.t * (Pattern.dynamic_variant * t) list
      (** Match an unmapped polymorphic variant through its dynamic tag. *)
  | Record of (PathName.t * int * t) list
      (** Construct a record giving an expression for each field. *)
  | Field of t * PathName.t  (** Access to a field of a record. *)
  | IfThenElse of t * t * t  (** The "else" part may be unit. *)
  | Module of Type.t * (PathName.t * int * t) list
      (** The value of a first-class module. *)
  | ModulePack of (int Tree.t * t)  (** Pack a module. *)
  | Functor of Name.t * Type.t * t  (** A functor. *)
  | Cast of t * Type.t  (** Force the cast to a type (with an axiom). *)
  | TypAnnotation of t * Type.t  (** Annotate an expression by its type. *)
  | Assert of Type.t * t  (** The assert keyword. *)
  | Assumption of assumption_kind * Type.t * t list
      (** Evaluate the arguments of an OCaml failure primitive, then obtain its
          result from a type-indexed, explicitly declared assumption. *)
  | RequiresAssumption of assumption_kind * Type.t * t
      (** Record the trusted result required by a partial operation whose
          ordinary translated application remains in the output. *)
  | Error of string  (** An error message for unhandled expressions. *)
  | ErrorArray of t list  (** An error produced by an array of elements. *)
  | ErrorTyp of Type.t  (** An error composed of a type. *)
  | ErrorMessage of t * string
      (** An expression together with an error message. *)
  | Ltac of ltac

and ltac = Subst | Discriminate | Exact of t | Concat of ltac * ltac

(** Take a function expression and make explicit the list of arguments and
    the body. *)
let rec open_function (e : t) : Name.t list * t =
  match e with
  | Function (x, _, e) ->
      let xs, e = open_function e in
      (x :: xs, e)
  | _ -> ([], e)

let rec open_ocaml_arrow_type (env : Env.t) (typ : Types.type_expr) (n : int) :
    (Types.type_expr list * Types.type_expr) option =
  if n = 0 then Some ([], typ)
  else
    let typ =
      try Ctype.full_expand ~may_forget_scope:false env typ
      with _ -> typ
    in
    match Types.get_desc typ with
    | Tarrow (_, argument, result, _) -> (
        match open_ocaml_arrow_type env result (n - 1) with
        | Some (arguments, result) -> Some (argument :: arguments, result)
        | None -> None)
    | _ -> None

(** Whether rocq-of-ocaml's compatibility library provides a computational
    [EqDec] instance for the translation of this OCaml type.

    OCaml [(=)] is a polymorphic runtime primitive.  We use Rocq's executable
    [equiv_decb] only for the closed fragment where the compatibility library
    supplies decision procedures.  Other instantiations must retain the
    explicit [Stdlib.polymorphic_equal] boundary instead of leaving unresolved
    typeclass obligations in generated code. *)
let rec has_rocq_eq_dec (env : Env.t) (typ : Types.type_expr) : bool =
  let typ =
    try Ctype.full_expand ~may_forget_scope:false env typ with _ -> typ
  in
  match Types.get_desc typ with
  | Tconstr (path, arguments, _) -> (
      match Path.last path with
      | ( "int" | "int32" | "int64" | "nativeint" | "float" | "bool"
        | "unit" | "char" | "string" ) ->
          true
      | "list" | "option" | "array" | "iarray" ->
          List.for_all (has_rocq_eq_dec env) arguments
      | _ -> false)
  | Ttuple elements ->
      List.for_all
        (fun (_, element) -> has_rocq_eq_dec env element)
        elements
  | Tlink typ | Tsubst (typ, _) | Tpoly (typ, _) ->
      has_rocq_eq_dec env typ
  | Tvar _ | Tunivar _ | Tarrow _ | Tobject _ | Tfield _ | Tnil
  | Tvariant _ | Tpackage _ ->
      false

let equality_argument_has_rocq_eq_dec (e : expression) : bool =
  match open_ocaml_arrow_type e.exp_env e.exp_type 2 with
  | Some (argument :: _, _) -> has_rocq_eq_dec e.exp_env argument
  | Some ([], _) | None -> false

let error_message (e : t) (category : Error.Category.t) (message : string) :
    t Monad.t =
  raise (ErrorMessage (e, message)) category message

let error_message_in_module (field : Name.t option) (e : t)
    (category : Error.Category.t) (message : string) :
    (string option * Name.t option * t) option Monad.t =
  raise (Some (Some message, field, e)) category message

module ModuleTypValues = struct
  type t = {
    field : Name.t;
    access : Name.t list;
    nb_free_vars : int;
  }

  let get ?(skip_functors = false) (typ_vars : Name.t Name.Map.t)
      (module_typ : Types.module_type) :
      t list Monad.t =
    get_env >>= fun env ->
    let rec get_signature (prefix : string list) (access : Name.t list)
        (signature : Types.signature) : t list Monad.t =
      signature
      |> Monad.List.concat_map (fun item ->
             match item with
             | Types.Sig_value (ident, { val_type; _ }, _) ->
                 let* value = Name.of_ident true ident in
                 let* field =
                   Name.of_strings true (prefix @ [ Ident.name ident ])
                 in
                 let* _, _, new_typ_vars =
                   Type.of_typ_expr true typ_vars val_type
                 in
                 return
                   [
                     {
                       field;
                       access = access @ [ value ];
                       nb_free_vars = List.length new_typ_vars;
                     };
                   ]
             | Sig_module (ident, _, _, _, _)
               when Ident.name ident = "Internal_for_tests" ->
                 return []
             | Sig_module (ident, _, { Types.md_type; _ }, _, _) ->
                 if
                   skip_functors
                   &&
                   match Env.scrape_alias env md_type with
                   | Mty_functor _ -> true
                   | _ -> false
                 then return []
                 else
                 let* module_name = Name.of_ident false ident in
                 let* module_access =
                   match md_type with
                   | Mty_alias path ->
                       let* { PathName.path; base } =
                         PathName.of_path_without_convert false path
                       in
                       return (path @ [ base ])
                   | _ -> return (access @ [ module_name ])
                 in
                 let* is_first_class =
                   IsFirstClassModule.is_module_typ_first_class md_type
                     (Some (Path.Pident ident))
                 in
                 (match is_first_class with
                 | Found _ ->
                     let* field =
                       Name.of_strings false
                         (prefix @ [ Ident.name ident ])
                     in
                     let* nb_free_vars =
                       ModuleTypParams.get_functor_nb_free_vars_params md_type
                     in
                     return
                       [
                         {
                           field;
                           access = module_access;
                           nb_free_vars;
                         };
                       ]
                 | Not_found _ when
                     match Env.scrape_alias env md_type with
                     | Mty_functor _ -> true
                     | _ -> false
                   ->
                     let* field =
                       Name.of_strings false
                         (prefix @ [ Ident.name ident ])
                     in
                     let* nb_free_vars =
                       ModuleTypParams.get_functor_nb_free_vars_params md_type
                     in
                     return
                       [
                         {
                           field;
                           access = module_access;
                           nb_free_vars;
                         };
                       ]
                 | Not_found _ -> (
                     match Env.scrape_alias env md_type with
                     | Mty_signature signature ->
                         get_signature
                           (prefix @ [ Ident.name ident ])
                           module_access signature
                     | _ ->
                         raise [] Unexpected
                           ("Nested module `" ^ Ident.name ident
                          ^ "` has neither a named signature nor a concrete \
                             signature.")))
             | _ -> return [])
    in
    match Env.scrape_alias env module_typ with
    | Mty_signature signature -> get_signature [] [] signature
    | module_typ ->
        raise [] Unexpected
          ("Module type signature not found for `"
          ^ Format.asprintf "%a" Printtyp.modtype module_typ
          ^ "`")
end

let dependent_transform (e : t) (dep_match : dependent_pattern_match option) =
  match dep_match with
  | None -> e
  | Some { args; _ } ->
      let args =
        args
        |> List.mapi (fun i _ -> "eq" ^ string_of_int i |> Name.of_string_raw)
      in
      let e = Ltac (Concat (Subst, Exact e)) in
      Functions (args, e)

let rec any_patterns_with_ith_true (is_guarded : bool) (i : int) (n : int) :
    Pattern.t list =
  if n = 0 then []
  else
    let head =
      if i = 0 && is_guarded then Pattern.Constructor (PathName.true_value, [])
      else Pattern.Any
    in
    head :: any_patterns_with_ith_true is_guarded (i - 1) (n - 1)

let rec get_include_name (module_expr : module_expr) : Name.t Monad.t =
  match module_expr.mod_desc with
  | Tmod_ident (path, _) ->
      let* path_name =
        PathName.of_path_with_convert false path
      in
      let* name = PathName.to_name false path_name in
      return (Name.suffix_by_include name)
  | Tmod_apply (applied_expr, _, _) -> get_include_name applied_expr
  | Tmod_constraint (module_expr, _, _, _) -> get_include_name module_expr
  | _ ->
      raise
        (Name.of_string_raw "nameless_include")
        NotSupported
        ("Cannot find a name for this module expression.\n\n"
       ^ "Try to first give a name to this module before doing the include.")

let build_module
    ?(typ_param_of_path =
      fun path ->
        let* name = Name.of_strings false path in
        return (Type.Variable name))
    (typ_params_arity : int Tree.t)
    (values : ModuleTypValues.t list)
    (signature_path : Path.t)
    (mixed_path_of_value_or_typ :
      Name.t -> Name.t list -> MixedPath.t Monad.t) : t Monad.t =
  let* fields =
    values
    |> Monad.List.map (fun { ModuleTypValues.field; access; nb_free_vars } ->
           let* field_name =
             PathName.of_path_and_name_with_convert signature_path field
           in
           let* mixed_path = mixed_path_of_value_or_typ field access in
           return
             (field_name, nb_free_vars, Variable (mixed_path, [])))
  in
  let* signature_path, explicit_params =
    ModuleTyp.signature_path_and_explicit_params signature_path
  in
  let* typ_params =
    typ_params_arity
    |> Tree.flatten
    |> Monad.List.map (fun (path, _) ->
           let* name = Name.of_strings false path in
           let* typ = typ_param_of_path path in
           return (name, Some typ))
  in
  return
    (Module
       (Type.Signature (signature_path, explicit_params @ typ_params), fields))

(** Preserve the dependent signature of an anonymous structure at the point
    where its terminal record is elaborated.  The aliases introduced while
    translating the structure (for example, an associated type [t]) are still
    in scope there; annotating the whole [let] expression would put those
    aliases out of scope in the annotation. *)
let rec annotate_terminal_module_with
    (local_type_aliases : Name.Set.t) (e : t) : t =
  match e with
  | Module (Type.Signature (_, parameters) as typ, _) ->
      let has_scoped_parameters =
        parameters
        |> List.for_all (function
             | _, Some (Type.Variable name) ->
                 Name.Set.mem name local_type_aliases
             | _ -> true)
      in
      if has_scoped_parameters then TypAnnotation (e, typ) else e
  | Module _ -> e
  | LetVar (operator, name, typ_vars, value, body) ->
      LetVar
        ( operator,
          name,
          typ_vars,
          value,
          annotate_terminal_module_with local_type_aliases body )
  | LetFun (definition, body) ->
      LetFun
        (definition, annotate_terminal_module_with local_type_aliases body)
  | LetTyp (name, typ_args, typ, body) ->
      LetTyp
        ( name,
          typ_args,
          typ,
          annotate_terminal_module_with
            (Name.Set.add name local_type_aliases)
            body )
  | LetModuleUnpack (name, path, body) ->
      LetModuleUnpack
        (name, path, annotate_terminal_module_with local_type_aliases body)
  | ErrorMessage (body, message) ->
      ErrorMessage
        (annotate_terminal_module_with local_type_aliases body, message)
  | _ -> e

let annotate_terminal_module (e : t) : t =
  annotate_terminal_module_with Name.Set.empty e

let rec bind_existentials (existentials : Name.t list) (typ : Type.t) : Type.t =
  let name = Name.of_string_raw "fst" in
  let fst = Type.build_apply_from_name MixedPath.prim_proj_fst name in
  let snd = Type.build_apply_from_name MixedPath.prim_proj_snd name in
  match existentials with
  | [] -> typ
  | [ x ] -> Type.Let (x, Variable name, typ)
  | [ x; y ] -> Type.Let (x, snd, Type.Let (y, fst, typ))
  | x :: xs ->
      let typ = bind_existentials xs typ in
      Type.Let (x, snd, Type.Let (name, fst, typ))

let build_existential_return (existentials : Name.t list) (typ : Type.t) :
    Type.t =
  let fst = Name.of_string_raw "fst" in
  let exi = Name.of_string_raw "exi" in
  let exityp = Type.build_apply_from_name MixedPath.projT1 exi in
  let typ = bind_existentials (List.rev existentials) typ in
  Type.Let (fst, exityp, typ)

let rec smart_return (operator : string) (e : t) : t Monad.t =
  match e with
  | Return (operator2, e2) -> (
      let* configuration = get_configuration in
      match
        Configuration.is_in_merge_returns configuration operator operator2
      with
      | None -> return (Return (operator, e))
      | Some target -> return (Return (target, e2)))
  | LetVar (None, x, typ_params, e1, e2) ->
      let* e2 = smart_return operator e2 in
      return (LetVar (None, x, typ_params, e1, e2))
  | Match (e, dep_match, cases, is_with_default_case) ->
      let* cases =
        cases
        |> Monad.List.map (fun (p, existential_cast, e) ->
               let* e = smart_return operator e in
               return (p, existential_cast, e))
      in
      return (Match (e, dep_match, cases, is_with_default_case))
  | _ -> return (Return (operator, e))

(** The free exitential type variables in an expression. This is useful to know
    in the match which exitential types are actually used, so that unused
    existential types are not printed. *)
let rec free_existential_typs (e : t) : Name.Set.t =
  let of_list (es : t list) : Name.Set.t =
    List.fold_left Name.Set.union Name.Set.empty
      (List.map free_existential_typs es)
  in
  let of_definition (definition : t option Definition.t) : Name.Set.t =
    let { Definition.cases; _ } = definition in
    let free_typs_list =
      cases
      |> List.map (fun ({ Header.typ_vars; args; typ; _ }, body) ->
             let typs = List.map snd args in
             let es = match body with None -> [] | Some body -> [ body ] in
             Name.Set.diff
               (Name.Set.union
                  (Type.local_typ_constructors_of_typs (typ :: typs))
                  (of_list es))
               (Name.Set.of_list (List.map fst typ_vars)))
    in
    List.fold_left Name.Set.union Name.Set.empty free_typs_list
  in
  let of_implicits (implicits : (string * string) list) : Name.Set.t =
    Name.Set.of_list
      (List.map (fun (_, typ) -> Name.of_string_raw typ) implicits)
  in
  match e with
  | Constant _ -> Name.Set.empty
  | Variable (_, implicits) -> of_implicits implicits
  | Tuple es -> of_list es
  | Constructor (_, implicits, es) ->
      Name.Set.union (of_implicits implicits) (of_list es)
  | ConstructorExtensible (_, typ, e) ->
      Name.Set.union
        (Type.local_typ_constructors_of_typ typ)
        (free_existential_typs e)
  | ConstructorVariant (_, typ_e) -> (
      match typ_e with
      | None -> Name.Set.empty
      | Some (typ, e) ->
          Name.Set.union
            (Type.local_typ_constructors_of_typ typ)
            (free_existential_typs e))
  | Apply (e, es) | SourceApply (e, es, _) ->
      let es = e :: List.filter_map (fun x -> x) es in
      of_list es
  | Return (_, e) -> free_existential_typs e
  | InfixOperator (_, e1, e2) -> of_list [ e1; e2 ]
  | Function (_, typ, e) ->
      let typs = match typ with None -> [] | Some typ -> [ typ ] in
      Name.Set.union
        (Type.local_typ_constructors_of_typs typs)
        (free_existential_typs e)
  | Functions (_, e) -> free_existential_typs e
  | LetVar (_, _, typ_vars, e1, e2) ->
      Name.Set.diff (of_list [ e1; e2 ]) (Name.Set.of_list typ_vars)
  | LetFun (definition, e) ->
      Name.Set.union (of_definition definition) (free_existential_typs e)
  | LetTyp (name, typ_vars, typ, e) ->
      Name.Set.union
        (Name.Set.diff
           (Type.local_typ_constructors_of_typ typ)
           (Name.Set.of_list typ_vars))
        (Name.Set.remove name (free_existential_typs e))
  | LetModuleUnpack (_, _, e) -> free_existential_typs e
  | Match (e, _, cases, _) ->
      let cast_typs =
        cases
        |> List.map (fun (_, cast, e) ->
               let new_typ_vars =
                 match cast with
                 | Some { bound_vars; enable = true; _ } ->
                     Name.Set.of_list (List.map fst bound_vars)
                 | _ -> Name.Set.empty
               in
               let typ_vars_of_typs =
                 match cast with
                 | Some
                     { bound_vars; return_typ; cast_result; enable = true; _ }
                   ->
                     Type.local_typ_constructors_of_typs
                       ((if cast_result then [ return_typ ] else [])
                       @ List.map snd bound_vars)
                 | _ -> Name.Set.empty
               in
               Name.Set.diff
                 (Name.Set.union typ_vars_of_typs (free_existential_typs e))
                 new_typ_vars)
      in
      List.fold_left Name.Set.union Name.Set.empty
        (free_existential_typs e :: cast_typs)
  | MatchExtensible (e1, result_typ, cases) ->
      let es = e1 :: List.map snd cases in
      let typs =
        result_typ
        :: (cases
        |> List.filter_map (fun (pattern, _) ->
               match pattern with None -> None | Some (_, _, typ) -> Some typ))
      in
      Name.Set.union (of_list es) (Type.local_typ_constructors_of_typs typs)
  | MatchVariant (e1, result_typ, cases) ->
      let es = e1 :: List.map snd cases in
      let typs =
        result_typ
        :: (cases
        |> List.filter_map (fun (pattern, _) ->
               match pattern with
               | Pattern.VariantCase (_, _, typ, _) -> Some typ
               | Pattern.VariantDefault _ -> None))
      in
      Name.Set.union (of_list es) (Type.local_typ_constructors_of_typs typs)
  | Record items ->
      let es = List.map (fun (_, _, e) -> e) items in
      of_list es
  | Field (e, _) -> free_existential_typs e
  | IfThenElse (e1, e2, e3) -> of_list [ e1; e2; e3 ]
  | Module (_, items) ->
      let es = List.map (fun (_, _, e) -> e) items in
      of_list es
  | ModulePack (_, e) -> free_existential_typs e
  | Functor (_, typ, e) ->
      Name.Set.union
        (Type.local_typ_constructors_of_typ typ)
        (free_existential_typs e)
  | Cast (e, typ) ->
      Name.Set.union
        (Type.local_typ_constructors_of_typ typ)
        (free_existential_typs e)
  | TypAnnotation (e, typ) ->
      Name.Set.union
        (Type.local_typ_constructors_of_typ typ)
        (free_existential_typs e)
  | Assert (typ, e) ->
      Name.Set.union
        (Type.local_typ_constructors_of_typ typ)
        (free_existential_typs e)
  | Assumption (_, typ, es) ->
      Name.Set.union
        (Type.local_typ_constructors_of_typ typ)
        (of_list es)
  | RequiresAssumption (_, typ, e) ->
      Name.Set.union
        (Type.local_typ_constructors_of_typ typ)
        (free_existential_typs e)
  | Error _ -> Name.Set.empty
  | ErrorArray es -> of_list es
  | ErrorTyp typ -> Type.local_typ_constructors_of_typ typ
  | ErrorMessage (e, _) -> free_existential_typs e
  | Ltac _ -> Name.Set.empty

(** Get the free variables of an expression. This is useful to optimize the
    translation of mutually recursive definitions implemented as notation,
    by detecting which ones are used. *)
let rec get_free_vars (e : t) : Name.Set.t =
  let get_free_vars_of_list (es : t list) : Name.Set.t =
    List.fold_left Name.Set.union Name.Set.empty (List.map get_free_vars es)
  in
  match e with
  | Constant _ -> Name.Set.empty
  | Variable (x, _) -> (
      match x with
      | MixedPath.PathName { path = []; base } -> Name.Set.singleton base
      | _ -> Name.Set.empty)
  | Tuple es -> get_free_vars_of_list es
  | Constructor (_, _, es) -> get_free_vars_of_list es
  | ConstructorExtensible (_, _, e) -> get_free_vars e
  | ConstructorVariant (_, typ_e) -> (
      match typ_e with None -> Name.Set.empty | Some (_, e) -> get_free_vars e)
  | Apply (e, es) | SourceApply (e, es, _) ->
      let es = e :: List.filter_map (fun x -> x) es in
      get_free_vars_of_list es
  | Return (_, e) -> get_free_vars e
  | InfixOperator (_, e1, e2) -> get_free_vars_of_list [ e1; e2 ]
  | Function (x, _, e) -> Name.Set.remove x (get_free_vars e)
  | Functions (names, e) ->
      Name.Set.diff (get_free_vars e) (Name.Set.of_list names)
  | LetVar (_, x, _, e1, e2) ->
      Name.Set.union (get_free_vars e1) (Name.Set.remove x (get_free_vars e2))
  | LetFun (definition, e) ->
      let defined_names =
        definition.cases |> List.map (fun ({ Header.name; _ }, _) -> name)
      in
      let is_rec = definition.is_rec in
      let free_vars_of_bodies =
        definition.cases
        |> List.map (fun ({ Header.args; _ }, body) ->
               match body with
               | None -> Name.Set.empty
               | Some body ->
                   Name.Set.diff (get_free_vars body)
                     (Name.Set.of_list (List.map fst args)))
      in
      let free_vars_of_definition =
        Name.Set.diff
          (List.fold_left Name.Set.union Name.Set.empty free_vars_of_bodies)
          (if is_rec then Name.Set.of_list defined_names else Name.Set.empty)
      in
      Name.Set.union free_vars_of_definition
        (Name.Set.diff (get_free_vars e) (Name.Set.of_list defined_names))
  | LetTyp (_, _, _, e) -> get_free_vars e
  | LetModuleUnpack (x, _, e) -> Name.Set.remove x (get_free_vars e)
  | Match (e, _, entries, _) ->
      Name.Set.union (get_free_vars e)
        (List.fold_left Name.Set.union Name.Set.empty
           (entries
           |> List.map (fun (pattern, _, e) ->
                  Name.Set.diff (get_free_vars e)
                    (Pattern.get_free_vars pattern))))
  | MatchExtensible (e, _, entries) ->
      Name.Set.union (get_free_vars e)
        (List.fold_left Name.Set.union Name.Set.empty
           (entries
           |> List.map (fun (pattern, e) ->
                  let free_vars_of_pattern =
                    match pattern with
                    | Some (_, pattern, _) -> Pattern.get_free_vars pattern
                    | None -> Name.Set.empty
                  in
                  Name.Set.diff (get_free_vars e) free_vars_of_pattern)))
  | MatchVariant (e, _, entries) ->
      Name.Set.union (get_free_vars e)
        (List.fold_left Name.Set.union Name.Set.empty
           (entries
           |> List.map (fun (pattern, body) ->
                  let pattern =
                    match pattern with
                    | Pattern.VariantCase (_, pattern, _, _)
                    | Pattern.VariantDefault pattern ->
                        pattern
                  in
                  Name.Set.diff (get_free_vars body)
                    (Pattern.get_free_vars pattern))))
  | Record entries ->
      get_free_vars_of_list (List.map (fun (_, _, e) -> e) entries)
  | Field (e, _) -> get_free_vars e
  | IfThenElse (e1, e2, e3) -> get_free_vars_of_list [ e1; e2; e3 ]
  | Module (_, entries) ->
      get_free_vars_of_list (List.map (fun (_, _, e) -> e) entries)
  | ModulePack (_, e) -> get_free_vars e
  | Functor (x, _, e) -> Name.Set.remove x (get_free_vars e)
  | Cast (e, _) -> get_free_vars e
  | TypAnnotation (e, _) -> get_free_vars e
  | Assert (_, e) -> get_free_vars e
  | Assumption (_, _, es) -> get_free_vars_of_list es
  | RequiresAssumption (_, _, e) -> get_free_vars e
  | Error _ -> Name.Set.empty
  | ErrorArray es -> get_free_vars_of_list es
  | ErrorTyp _ -> Name.Set.empty
  | ErrorMessage (e, _) -> get_free_vars e
  | Ltac _ -> Name.Set.empty

(** Whether an expression contains a local well-founded recursive definition.
    The enclosing top-level command must use [Program] so that proof holes in
    the term-level [Fix] become obligations. *)
let rec has_well_founded_recursion (e : t) : bool =
  let any es = List.exists has_well_founded_recursion es in
  match e with
  | Constant _ | Variable _ | Error _ | ErrorTyp _ | Ltac _ -> false
  | Tuple es | Constructor (_, _, es) | Assumption (_, _, es)
  | ErrorArray es ->
      any es
  | ConstructorExtensible (_, _, e) | Return (_, e) | Function (_, _, e)
  | Functions (_, e) | LetTyp (_, _, _, e) | LetModuleUnpack (_, _, e)
  | Field (e, _) | ModulePack (_, e) | Functor (_, _, e) | Cast (e, _)
  | TypAnnotation (e, _) | Assert (_, e) | RequiresAssumption (_, _, e)
  | ErrorMessage (e, _) ->
      has_well_founded_recursion e
  | ConstructorVariant (_, None) -> false
  | ConstructorVariant (_, Some (_, e)) -> has_well_founded_recursion e
  | Apply (f, args) | SourceApply (f, args, _) ->
      any (f :: List.filter_map (fun argument -> argument) args)
  | InfixOperator (_, left, right) -> any [ left; right ]
  | LetVar (_, _, _, value, body) -> any [ value; body ]
  | LetFun (definition, body) ->
      (match definition.Definition.recursion_strategy with
      | Definition.WellFounded _ -> true
      | Definition.Partial
          { recursion = Definition.WellFoundedTerminates _; _ } ->
          true
      | Definition.Structural | Definition.Partial _
      | Definition.Convergent _ ->
          false)
      || has_well_founded_recursion body
      || any (List.filter_map snd definition.Definition.cases)
  | Match (scrutinee, _, cases, _) ->
      has_well_founded_recursion scrutinee
      || any (List.map (fun (_, _, body) -> body) cases)
  | MatchExtensible (scrutinee, _, cases) ->
      has_well_founded_recursion scrutinee || any (List.map snd cases)
  | MatchVariant (scrutinee, _, cases) ->
      has_well_founded_recursion scrutinee || any (List.map snd cases)
  | Record fields | Module (_, fields) ->
      any (List.map (fun (_, _, value) -> value) fields)
  | IfThenElse (condition, then_, else_) -> any [ condition; then_; else_ ]

(** Whether an expression contains a local partial recursive definition.  Its
    enclosing definition must expose the corresponding partial result type. *)
let rec has_partial_recursion (e : t) : bool =
  let any es = List.exists has_partial_recursion es in
  match e with
  | Constant _ | Variable _ | Error _ | ErrorTyp _ | Ltac _ -> false
  | Tuple es | Constructor (_, _, es) | Assumption (_, _, es)
  | ErrorArray es ->
      any es
  | ConstructorExtensible (_, _, e) | Return (_, e) | Function (_, _, e)
  | Functions (_, e) | LetTyp (_, _, _, e) | LetModuleUnpack (_, _, e)
  | Field (e, _) | ModulePack (_, e) | Functor (_, _, e) | Cast (e, _)
  | TypAnnotation (e, _) | Assert (_, e) | RequiresAssumption (_, _, e)
  | ErrorMessage (e, _) ->
      has_partial_recursion e
  | ConstructorVariant (_, None) -> false
  | ConstructorVariant (_, Some (_, e)) -> has_partial_recursion e
  | Apply (f, args) | SourceApply (f, args, _) ->
      any (f :: List.filter_map (fun argument -> argument) args)
  | InfixOperator (_, left, right) -> any [ left; right ]
  | LetVar (_, _, _, value, body) -> any [ value; body ]
  | LetFun (definition, body) ->
      (match definition.Definition.recursion_strategy with
      | Definition.Partial _ -> true
      | Definition.Structural | Definition.WellFounded _
      | Definition.Convergent _ ->
          false)
      || has_partial_recursion body
      || any (List.filter_map snd definition.Definition.cases)
  | Match (scrutinee, _, cases, _) ->
      has_partial_recursion scrutinee
      || any (List.map (fun (_, _, body) -> body) cases)
  | MatchExtensible (scrutinee, _, cases) ->
      has_partial_recursion scrutinee || any (List.map snd cases)
  | MatchVariant (scrutinee, _, cases) ->
      has_partial_recursion scrutinee || any (List.map snd cases)
  | Record fields | Module (_, fields) ->
      any (List.map (fun (_, _, value) -> value) fields)
  | IfThenElse (condition, then_, else_) -> any [ condition; then_; else_ ]

let rec expression_qualified_name (e : t) : string option =
  match e with
  | Variable (path, _) -> Some (MixedPath.to_string path)
  | Field (base, field) ->
      Option.map
        (fun base -> base ^ "." ^ PathName.to_string field)
        (expression_qualified_name base)
  | _ -> None

let rec application_function_name (e : t) : string option =
  match e with
  | Apply (function_, _) | SourceApply (function_, _, _) ->
      application_function_name function_
  | TypAnnotation (function_, _) | Cast (function_, _) ->
      application_function_name function_
  | RequiresAssumption (_, _, function_) ->
      application_function_name function_
  | _ -> expression_qualified_name e

let is_ocaml_format_function (e : t) : bool =
  match application_function_name e with
  | None -> false
  | Some name ->
      List.exists
        (fun suffix -> string_ends_with name suffix)
        [
          "OCamlFormat.printf";
          "OCamlFormat.eprintf";
          "OCamlFormat.sprintf";
          "Format.printf";
          "Format.eprintf";
          "Format.sprintf";
        ]

let configured_partial_path_matches (candidate : string) (expected : string) :
    bool =
  let candidate = drop_closing_parentheses candidate in
  let expected_components = String.split_on_char '.' expected in
  let dotted_suffix, flattened_suffix =
    match List.rev expected_components with
    | value :: module_ :: _ ->
        (module_ ^ "." ^ value, module_ ^ "_" ^ value)
    | _ -> (expected, expected)
  in
  candidate = expected
  || string_ends_with candidate ("." ^ expected)
  || string_ends_with candidate ("." ^ dotted_suffix)
  || string_ends_with candidate ("." ^ flattened_suffix)
  || string_ends_with candidate ("_" ^ flattened_suffix)
  ||
  match List.rev (String.split_on_char '.' candidate) with
  | final :: _ -> final = flattened_suffix
  | [] -> false

let is_configured_partial_expression (partial_definitions : string list)
    (e : t) : bool =
  match expression_qualified_name e with
  | Some candidate ->
      List.exists
        (configured_partial_path_matches candidate)
        partial_definitions
  | None -> false

(** Execute configured monadic sequence traversals inside a definition whose
    well-founded specification asserts totality. [Resumption.run] exposes the
    convergence proof as a [Program] obligation; it is never synthesized by
    the translator. *)
let rec discharge_partial_sequence_calls
    (partial_definitions : string list) (e : t) : t =
  let recurse = discharge_partial_sequence_calls partial_definitions in
  let map_option f = function None -> None | Some value -> Some (f value) in
  let field base name =
    match base with
    | Variable
        ( MixedPath.PathName { PathName.path; base },
          _ ) ->
        Variable
          ( MixedPath.PathName
              (PathName.of_name
                 (path @ [ base ])
                 (Name.of_string_raw name)),
            [] )
    | _ ->
        Field
          ( base,
            PathName.of_name [] (Name.of_string_raw name) )
  in
  let wildcard =
    Variable (MixedPath.of_name (Name.of_string_raw "_"), [])
  in
  let runtime_apply module_name value_name arguments =
    let value =
      Variable
        ( MixedPath.PathName
            {
              PathName.path =
                [
                  Name.of_string_raw "RocqOfOCaml";
                  Name.of_string_raw "Partial";
                  Name.of_string_raw module_name;
                ];
              base = Name.of_string_raw value_name;
            },
          [] )
    in
    Apply (value, List.map (fun argument -> Some argument) arguments)
  in
  let rewrite_application result_typ function_ arguments =
    let rec flatten function_ arguments =
      match function_ with
      | Apply (inner, preceding)
      | SourceApply (inner, preceding, _)
        when
          List.for_all
            (function None -> false | Some _ -> true)
            preceding ->
          flatten inner (preceding @ arguments)
      | _ -> (function_, arguments)
    in
    let function_, arguments = flatten function_ arguments in
    let function_ = recurse function_ in
    let arguments = List.map (map_option recurse) arguments in
    let is_partial_seq_map =
      match expression_qualified_name function_ with
      | None -> false
      | Some candidate ->
          partial_definitions
          |> List.exists (fun definition ->
                 configured_partial_path_matches definition "Seq.mapM"
                 && configured_partial_path_matches candidate definition)
    in
    let monad_of_seq_function =
      match function_ with
      | Variable
          ( MixedPath.PathName
              { PathName.path; base = _ },
            _ ) -> (
          match List.rev path with
          | seq :: monad_base :: rev_monad_path
            when Name.to_string seq = "Seq" ->
              let monad_path =
                MixedPath.PathName
                  (PathName.of_name
                     (List.rev rev_monad_path)
                     monad_base)
              in
              let monad_type_path =
                MixedPath.PathName
                  (PathName.of_name
                     (List.rev rev_monad_path @ [ monad_base ])
                     (Name.of_string_raw "t"))
              in
              Some
                (Variable (monad_path, []), monad_type_path)
          | _ -> None)
      | _ -> None
    in
    match (is_partial_seq_map, monad_of_seq_function, arguments) with
    | true, Some (monad, monad_path), [ Some _; Some _ ] ->
        let a = Name.of_string_raw "_rocq_partial_A" in
        let b = Name.of_string_raw "_rocq_partial_B" in
        let value = Name.of_string_raw "_rocq_partial_return_value" in
        let action = Name.of_string_raw "_rocq_partial_action" in
        let continuation =
          Name.of_string_raw "_rocq_partial_continuation"
        in
        let monad_type result =
          Type.Apply
            (monad_path, [ (Type.Variable result, false) ])
        in
        let typed_function name typ body =
          Function (name, Some typ, body)
        in
        let return_operation =
          typed_function a (Type.Kind Kind.Set)
            (typed_function value (Type.Variable a)
               (Apply
                  ( field monad "_return",
                    [
                      Some
                        (Variable
                           (MixedPath.of_name value, []));
                    ] )))
        in
        let bind_operation =
          typed_function a (Type.Kind Kind.Set)
            (typed_function b (Type.Kind Kind.Set)
               (typed_function action (monad_type a)
                  (typed_function continuation
                     (Type.Arrow (Type.Variable a, monad_type b))
                     (Apply
                        ( field monad "op_letdollar",
                          [
                            Some
                              (Variable
                                 (MixedPath.of_name action, []));
                            Some
                              (Variable
                                 (MixedPath.of_name continuation, []));
                          ] )))))
        in
        runtime_apply "Resumption" "run_explicit"
          [
            return_operation;
            bind_operation;
            Apply (function_, arguments);
            wildcard;
          ]
    | _ -> (
        match result_typ with
        | None -> Apply (function_, arguments)
        | Some result_typ ->
            SourceApply (function_, arguments, result_typ))
  in
  match e with
  | Constant _ | Variable _ | Error _ | ErrorTyp _ | Ltac _ -> e
  | Tuple values -> Tuple (List.map recurse values)
  | Constructor (name, implicits, values) ->
      Constructor (name, implicits, List.map recurse values)
  | ConstructorExtensible (tag, typ, value) ->
      ConstructorExtensible (tag, typ, recurse value)
  | ConstructorVariant (tag, value) ->
      ConstructorVariant
        (tag, Option.map (fun (typ, value) -> (typ, recurse value)) value)
  | Apply (function_, arguments) ->
      rewrite_application None function_ arguments
  | SourceApply (function_, arguments, result_typ) ->
      rewrite_application (Some result_typ) function_ arguments
  | Return (operator, value) -> Return (operator, recurse value)
  | InfixOperator (operator, left, right) ->
      InfixOperator (operator, recurse left, recurse right)
  | Function (name, typ, body) -> Function (name, typ, recurse body)
  | Functions (names, body) -> Functions (names, recurse body)
  | LetVar (operator, name, parameters, value, body) ->
      LetVar (operator, name, parameters, recurse value, recurse body)
  | LetFun (definition, body) ->
      let cases =
        definition.Definition.cases
        |> List.map (fun (header, body) ->
               (header, Option.map recurse body))
      in
      LetFun ({ definition with Definition.cases }, recurse body)
  | LetTyp (name, parameters, typ, body) ->
      LetTyp (name, parameters, typ, recurse body)
  | LetModuleUnpack (name, path, body) ->
      LetModuleUnpack (name, path, recurse body)
  | Match (scrutinee, dependent, cases, default) ->
      Match
        ( recurse scrutinee,
          dependent,
          List.map
            (fun (pattern, cast, body) ->
              (pattern, cast, recurse body))
            cases,
          default )
  | MatchExtensible (scrutinee, typ, cases) ->
      MatchExtensible
        ( recurse scrutinee,
          typ,
          List.map
            (fun (pattern, body) -> (pattern, recurse body))
            cases )
  | MatchVariant (scrutinee, typ, cases) ->
      MatchVariant
        ( recurse scrutinee,
          typ,
          List.map
            (fun (pattern, body) -> (pattern, recurse body))
            cases )
  | Record fields ->
      Record
        (List.map
           (fun (name, arity, value) -> (name, arity, recurse value))
           fields)
  | Field (value, name) -> Field (recurse value, name)
  | IfThenElse (condition, then_, else_) ->
      IfThenElse (recurse condition, recurse then_, recurse else_)
  | Module (typ, fields) ->
      Module
        ( typ,
          List.map
            (fun (name, arity, value) -> (name, arity, recurse value))
            fields )
  | ModulePack (arity, value) -> ModulePack (arity, recurse value)
  | Functor (name, typ, body) -> Functor (name, typ, recurse body)
  | Cast (value, typ) -> Cast (recurse value, typ)
  | TypAnnotation (value, typ) -> TypAnnotation (recurse value, typ)
  | Assert (typ, condition) -> Assert (typ, recurse condition)
  | Assumption (kind, typ, arguments) ->
      Assumption (kind, typ, List.map recurse arguments)
  | RequiresAssumption (kind, typ, body) ->
      RequiresAssumption (kind, typ, recurse body)
  | ErrorArray values -> ErrorArray (List.map recurse values)
  | ErrorMessage (body, message) -> ErrorMessage (recurse body, message)

let rec has_partial_reference (partial_definitions : string list) (e : t) :
    bool =
  let any es = List.exists (has_partial_reference partial_definitions) es in
  if is_configured_partial_expression partial_definitions e then true
  else
    match e with
    | Constant _ | Error _ | ErrorTyp _ | Ltac _ | Variable _ -> false
    | Tuple es | Constructor (_, _, es) | Assumption (_, _, es)
    | ErrorArray es ->
        any es
    | ConstructorExtensible (_, _, e) | Return (_, e) | Function (_, _, e)
    | Functions (_, e) | LetTyp (_, _, _, e) | LetModuleUnpack (_, _, e)
    | Field (e, _) | ModulePack (_, e) | Functor (_, _, e) | Cast (e, _)
    | TypAnnotation (e, _) | Assert (_, e) | RequiresAssumption (_, _, e)
    | ErrorMessage (e, _) ->
        has_partial_reference partial_definitions e
    | ConstructorVariant (_, None) -> false
    | ConstructorVariant (_, Some (_, e)) ->
        has_partial_reference partial_definitions e
    | Apply (f, args) | SourceApply (f, args, _) ->
        any (f :: List.filter_map (fun argument -> argument) args)
    | InfixOperator (_, left, right) -> any [ left; right ]
    | LetVar (_, _, _, value, body) -> any [ value; body ]
    | LetFun (definition, body) ->
        has_partial_reference partial_definitions body
        || any (List.filter_map snd definition.Definition.cases)
    | Match (scrutinee, _, cases, _) ->
        has_partial_reference partial_definitions scrutinee
        || any (List.map (fun (_, _, body) -> body) cases)
    | MatchExtensible (scrutinee, _, cases) ->
        has_partial_reference partial_definitions scrutinee
        || any (List.map snd cases)
    | MatchVariant (scrutinee, _, cases) ->
        has_partial_reference partial_definitions scrutinee
        || any (List.map snd cases)
    | Record fields | Module (_, fields) ->
        any (List.map (fun (_, _, value) -> value) fields)
    | IfThenElse (condition, then_, else_) ->
        any [ condition; then_; else_ ]

type assumption_requirement = assumption_kind * Type.t

let compare_assumption_requirement : assumption_requirement -> assumption_requirement -> int =
 fun left right -> compare left right

let sort_uniq_assumptions (requirements : assumption_requirement list) :
    assumption_requirement list =
  List.sort_uniq compare_assumption_requirement requirements

(** Collect every trusted result requested by an expression.  The result is
    used both to add polymorphic class parameters and to emit concrete,
    type-specific instances next to the translated definition. *)
let rec assumption_requirements (e : t) : assumption_requirement list =
  let collect es = List.concat_map assumption_requirements es in
  let collect_cases cases =
    collect (List.map (fun (_, _, body) -> body) cases)
  in
  match e with
  | Constant _ | Variable _ | Error _ | ErrorTyp _ | Ltac _ -> []
  | Tuple es | ErrorArray es -> collect es
  | Constructor (_, _, es) -> collect es
  | ConstructorExtensible (_, _, e)
  | Return (_, e)
  | Function (_, _, e)
  | Functions (_, e)
  | LetTyp (_, _, _, e)
  | LetModuleUnpack (_, _, e)
  | Field (e, _)
  | ModulePack (_, e)
  | Functor (_, _, e)
  | Cast (e, _)
  | TypAnnotation (e, _)
  | ErrorMessage (e, _) ->
      assumption_requirements e
  | ConstructorVariant (_, None) -> []
  | ConstructorVariant (_, Some (_, e)) -> assumption_requirements e
  | Apply (f, args) | SourceApply (f, args, _) ->
      collect
        (f :: List.filter_map (fun argument -> argument) args)
  | InfixOperator (_, left, right) -> collect [ left; right ]
  | LetVar (_, _, _, value, body) -> collect [ value; body ]
  | LetFun (definition, body) ->
      let definition_bodies =
        definition.cases
        |> List.filter_map (fun (_, body) -> body)
      in
      collect (body :: definition_bodies)
  | Match (scrutinee, _, cases, _) ->
      assumption_requirements scrutinee @ collect_cases cases
  | MatchExtensible (scrutinee, result_typ, cases) ->
      let propagated_exception =
        if List.exists (fun (pattern, _) -> Option.is_none pattern) cases then []
        else [ (Unreachable, result_typ) ]
      in
      assumption_requirements scrutinee
      @ collect (List.map snd cases)
      @ propagated_exception
  | MatchVariant (scrutinee, result_typ, cases) ->
      let default =
        if
          List.exists
            (fun (pattern, _) ->
              match pattern with Pattern.VariantDefault _ -> true | _ -> false)
            cases
        then []
        else [ (Unreachable, result_typ) ]
      in
      assumption_requirements scrutinee
      @ collect (List.map snd cases)
      @ default
  | Record fields | Module (_, fields) ->
      collect (List.map (fun (_, _, value) -> value) fields)
  | IfThenElse (condition, then_, else_) ->
      collect [ condition; then_; else_ ]
  | Assert (typ, condition) ->
      (Unreachable, typ) :: assumption_requirements condition
  | Assumption (kind, typ, arguments) ->
      (kind, typ) :: collect arguments
  | RequiresAssumption (kind, typ, body) ->
      (kind, typ) :: assumption_requirements body

let assumption_class_type ((kind, typ) : assumption_requirement) : Type.t =
  let class_name =
    match kind with
    | Unreachable -> "Unreachable"
    | Unimplemented -> "Unimplemented"
  in
  Type.Apply
    ( MixedPath.PathName
        {
          PathName.path =
            [
              Name.of_string_raw "RocqOfOCaml";
              Name.of_string_raw "Basics";
            ];
          base = Name.of_string_raw class_name;
        },
      [ (typ, false) ] )

let assumption_requirement_of_class_type (typ : Type.t) :
    assumption_requirement option =
  match typ with
  | Type.Apply
      ( MixedPath.PathName { PathName.base; _ },
        [ (result_typ, _) ] ) -> (
      match Name.to_string base with
      | "Unreachable" -> Some (Unreachable, result_typ)
      | "Unimplemented" -> Some (Unimplemented, result_typ)
      | _ -> None)
  | _ -> None

let concrete_assumption_requirements (e : t) : assumption_requirement list =
  assumption_requirements e
  |> List.filter (fun (_, typ) -> Name.Set.is_empty (Type.typ_args_of_typ typ))
  |> sort_uniq_assumptions

(** Add explicit class parameters for assumptions whose result depends on a
    translated OCaml type parameter.  Concrete assumptions are declared by
    [Structure.Value.to_coq] instead. *)
let add_assumption_instance_args (definition : t option Definition.t) :
    t option Definition.t =
  let add_case (header, body) =
    match body with
    | None -> (header, body)
    | Some body ->
        let header_typ_vars =
          header.Header.typ_vars |> List.map fst |> Name.Set.of_list
        in
        let requirements =
          assumption_requirements body
          |> List.filter (fun (_, typ) ->
                 let free_vars = Type.typ_args_of_typ typ in
                 (not (Name.Set.is_empty free_vars))
                 && Name.Set.subset free_vars header_typ_vars)
          |> sort_uniq_assumptions
        in
        let generated_args =
          requirements
          |> List.mapi (fun index requirement ->
                 ( Name.of_string_raw
                     ("_rocq_assumption_" ^ string_of_int index),
                   assumption_class_type requirement ))
        in
        let existing_args =
          header.Header.instance_args
          |> List.filter (fun (name, _) ->
                 let name = Name.to_string name in
                 not
                   (String.length name >= 17
                   && String.sub name 0 17 = "_rocq_assumption_"))
        in
        ( { header with
            Header.instance_args =
              existing_args @ generated_args;
          },
          Some body )
  in
  { definition with Definition.cases = List.map add_case definition.cases }

type assumption_call_spec = {
  result_typ : Type.t;
  requirements : assumption_requirement list;
}

type assumption_call_specs = assumption_call_spec Name.Map.t

let assumption_call_spec_for_field (specs : assumption_call_specs)
    (field : PathName.t) : assumption_call_spec option =
  match Name.Map.find_opt field.PathName.base specs with
  | Some spec -> Some spec
  | None ->
      let field_name = Name.to_string field.PathName.base in
      specs
      |> Name.Map.bindings
      |> List.find_map (fun (name, spec) ->
             let suffix = "_" ^ Name.to_string name in
             if string_ends_with field_name suffix then Some spec else None)

(** Add the extra binders needed when a generated module-record constructor
    stores translated functions that acquired assumption class parameters.
    Known standard-library partial fields are handled by the renderer because
    their flattened nested-module names do not always have a local call spec. *)
let add_root_record_field_assumption_arities (specs : assumption_call_specs)
    (expression : t) : t =
  let update_field (field, arity, value) =
    if is_partial_operation_field_name (PathName.to_string field) then
      (field, arity, value)
    else
      let extra =
        match assumption_call_spec_for_field specs field with
        | None -> 0
        | Some spec -> List.length spec.requirements
      in
      (field, arity + extra, value)
  in
  match expression with
  | Record fields -> Record (List.map update_field fields)
  | Module (typ, fields) -> Module (typ, List.map update_field fields)
  | expression -> expression

let assumption_call_specs_of_definition (definition : t option Definition.t) :
    assumption_call_specs =
  definition.cases
  |> List.fold_left
       (fun specs (header, _) ->
         let requirements =
           header.Header.instance_args
           |> List.filter_map (fun (_, typ) ->
                  assumption_requirement_of_class_type typ)
           |> sort_uniq_assumptions
         in
         match requirements with
         | [] -> specs
         | _ :: _ ->
             Name.Map.add header.Header.name
               { result_typ = header.Header.typ; requirements }
               specs)
       Name.Map.empty

(** Propagate a callee's generated class requirements to a source-level call.
    Matching the callee's declared result against the typed call result
    instantiates polymorphic requirements without inventing a universal
    instance. *)
let propagate_call_assumptions (specs : assumption_call_specs) (expression : t)
    : t =
  let map_option f = Option.map f in
  let rec map_definition (definition : t option Definition.t) =
    {
      definition with
      Definition.cases =
        definition.cases
        |> List.map (fun (header, body) ->
               (header, Option.map (transform false) body));
    }
  and transform covered expression =
    let recurse = transform false in
    match expression with
    | Constant _ | Variable _ | Error _ | ErrorTyp _ | Ltac _ -> expression
    | Tuple values -> Tuple (List.map recurse values)
    | Constructor (name, implicits, values) ->
        Constructor (name, implicits, List.map recurse values)
    | ConstructorExtensible (tag, typ, value) ->
        ConstructorExtensible (tag, typ, recurse value)
    | ConstructorVariant (tag, value) ->
        ConstructorVariant
          (tag, Option.map (fun (typ, value) -> (typ, recurse value)) value)
    | Apply (f, arguments) ->
        Apply (recurse f, List.map (map_option recurse) arguments)
    | SourceApply (f, arguments, result_typ) ->
        let f = recurse f in
        let arguments = List.map (map_option recurse) arguments in
        let application = SourceApply (f, arguments, result_typ) in
        if covered then application
        else
          let callee =
            match f with
            | Variable
                ( MixedPath.PathName { PathName.path = []; base },
                  _ ) ->
                Name.Map.find_opt base specs
            | _ -> None
          in
          (match callee with
          | None -> application
          | Some { result_typ = declared_result; requirements } ->
              let substitutions =
                match Type.match_variables declared_result result_typ with
                | Some substitutions -> substitutions
                | None -> []
              in
              List.fold_right
                (fun (kind, required_typ) body ->
                  RequiresAssumption
                    ( kind,
                      Type.subst_variables substitutions required_typ,
                      body ))
                requirements application)
    | Return (operator, value) -> Return (operator, recurse value)
    | InfixOperator (operator, left, right) ->
        InfixOperator (operator, recurse left, recurse right)
    | Function (name, typ, body) -> Function (name, typ, recurse body)
    | Functions (names, body) -> Functions (names, recurse body)
    | LetVar (operator, name, typ_vars, value, body) ->
        LetVar
          (operator, name, typ_vars, recurse value, recurse body)
    | LetFun (definition, body) ->
        LetFun (map_definition definition, recurse body)
    | LetTyp (name, parameters, typ, body) ->
        LetTyp (name, parameters, typ, recurse body)
    | LetModuleUnpack (name, path, body) ->
        LetModuleUnpack (name, path, recurse body)
    | Match (scrutinee, dependent, cases, default) ->
        Match
          ( recurse scrutinee,
            dependent,
            List.map
              (fun (pattern, cast, body) ->
                (pattern, cast, recurse body))
              cases,
            default )
    | MatchExtensible (scrutinee, typ, cases) ->
        MatchExtensible
          ( recurse scrutinee,
            typ,
            List.map
              (fun (pattern, body) -> (pattern, recurse body))
              cases )
    | MatchVariant (scrutinee, typ, cases) ->
        MatchVariant
          ( recurse scrutinee,
            typ,
            List.map
              (fun (pattern, body) -> (pattern, recurse body))
              cases )
    | Record fields ->
        Record
          (List.map
             (fun (name, arity, value) -> (name, arity, recurse value))
             fields)
    | Field (value, name) -> Field (recurse value, name)
    | IfThenElse (condition, then_, else_) ->
        IfThenElse (recurse condition, recurse then_, recurse else_)
    | Module (typ, fields) ->
        Module
          ( typ,
            List.map
              (fun (name, arity, value) -> (name, arity, recurse value))
              fields )
    | ModulePack (arity, value) -> ModulePack (arity, recurse value)
    | Functor (name, typ, body) -> Functor (name, typ, recurse body)
    | Cast (value, typ) -> Cast (recurse value, typ)
    | TypAnnotation (value, typ) -> TypAnnotation (recurse value, typ)
    | Assert (typ, condition) -> Assert (typ, recurse condition)
    | Assumption (kind, typ, arguments) ->
        Assumption (kind, typ, List.map recurse arguments)
    | RequiresAssumption (kind, typ, body) ->
        RequiresAssumption (kind, typ, transform true body)
    | ErrorArray values -> ErrorArray (List.map recurse values)
    | ErrorMessage (body, message) -> ErrorMessage (recurse body, message)
  in
  transform false expression

let propagate_definition_call_assumptions (specs : assumption_call_specs)
    (definition : t option Definition.t) : t option Definition.t =
  let definition =
    {
      definition with
      Definition.cases =
        definition.cases
        |> List.map (fun (header, body) ->
               (header, Option.map (propagate_call_assumptions specs) body));
    }
  in
  add_assumption_instance_args definition

(** Infer the instantiated OCaml type parameters of a polymorphic value
    projected from a translated module record.

    Rocq usually infers these parameters.  That is not reliable when an
    argument is typed through a local associated-type alias: unification may
    commit to the alias's argument before unfolding its body.  The typed OCaml
    tree already records the intended instantiation, so preserve it as named
    Rocq arguments on record projections. *)
let type_variable_source_name (typ : Types.type_expr) : Name.t Monad.t =
  match Types.get_desc typ with
  | Tvar (Some name) | Tunivar (Some name) -> Name.of_string false name
  | Tvar None | Tunivar None ->
      Name.of_string false (Printf.sprintf "A%d" (Types.get_id typ))
  | _ ->
      raise
        (Name.of_string_raw "invalid_type_parameter")
        Unexpected "A free type parameter was not a type variable"

let infer_projection_implicits (typ_vars : Name.t Name.Map.t)
    (source : expression) (translated : t) : t Monad.t =
  match (source.exp_desc, translated) with
  | ( Texp_ident (source_path, _, description),
      Variable (MixedPath.Access _ as path, []) ) ->
      let parent_and_field =
        match source_path with
        | Path.Pdot (parent, field) -> Some (parent, field)
        | Path.Pextra_ty (Path.Pdot (parent, field), _) ->
            Some (parent, field)
        | _ -> None
      in
      let* projection_type =
        match parent_and_field with
        | None -> return None
        | Some (parent, field) ->
            let* signature_path = MixedPath.get_signature_path parent in
            (match signature_path with
            | None -> return None
            | Some signature_path ->
                let* module_type = get_module_type_hint signature_path in
                match
                  Option.map
                    (Env.scrape_alias source.exp_env)
                    module_type
                with
                | Some (Mty_signature signature) ->
                    return
                      (signature
                      |> List.find_map (function
                           | Types.Sig_value (ident, description, _)
                             when String.equal (Ident.name ident) field ->
                               Some description.Types.val_type
                           | _ -> None))
                | _ -> return None)
      in
      (match projection_type with
      | None -> return translated
      | Some projection_type ->
        let source_type =
          match Env.find_value source_path source.exp_env with
          | declaration -> declaration.Types.val_type
          | exception Not_found -> description.Types.val_type
        in
        let source_parameters =
          Ctype.free_variables ~env:source.exp_env source_type
        in
        let projection_parameters =
          Ctype.free_variables ~env:source.exp_env projection_type
        in
        if
          source_parameters = []
          || List.length source_parameters
             <> List.length projection_parameters
        then return translated
        else
        let instantiated_parameters, instantiated_type =
          Ctype.instance_parameterized_type ~keep_names:true
            source_parameters source_type
        in
        let occurrence_parameters =
          Ctype.free_variables ~env:source.exp_env source.exp_type
        in
        let copied_occurrence_parameters, occurrence_type =
          Ctype.instance_parameterized_type ~keep_names:true
            occurrence_parameters source.exp_type
        in
        let unified =
          try
            Ctype.unify source.exp_env instantiated_type occurrence_type;
            true
          with _ -> false
        in
        if not unified then return translated
        else
        let* actual_typ_vars =
          List.combine occurrence_parameters copied_occurrence_parameters
          |> Monad.List.fold_left
               (fun actual_typ_vars
                    (original_parameter, copied_parameter) ->
                 let* original_name =
                   type_variable_source_name original_parameter
                 in
                 let* copied_name =
                   type_variable_source_name copied_parameter
                 in
                 match Name.Map.find_opt original_name typ_vars with
                 | None -> return actual_typ_vars
                 | Some generated_name ->
                     return
                       (Name.Map.add copied_name generated_name
                          actual_typ_vars))
               typ_vars
        in
        let* _, projection_name_map, projection_vars =
          Type.of_typ_expr true Name.Map.empty projection_type
        in
        let* implicits =
          List.combine projection_parameters instantiated_parameters
          |> Monad.List.filter_map (fun (generic_parameter, actual_parameter) ->
                 let* source_name =
                   type_variable_source_name generic_parameter
                 in
                 match Name.Map.find_opt source_name projection_name_map with
                 | None -> return None
                 | Some generated_name
                   when not
                          (List.mem_assoc generated_name projection_vars) ->
                     return None
                 | Some generated_name ->
                     let* actual_type, _, _ =
                       Type.of_typ_expr true actual_typ_vars actual_parameter
                     in
                     let rendered_type =
                       SmartPrint.to_string 1_000_000 0
                         (Type.to_coq None None actual_type)
                     in
                     return
                       (Some
                          (Name.to_string generated_name, rendered_type)))
        in
        return (Variable (path, implicits)))
  | _ -> return translated

(** Import an OCaml expression. *)
let names_bound_by_pattern (pattern : value general_pattern) :
    Name.t list Monad.t =
  Typedtree.pat_bound_idents_full pattern
  |> Monad.List.map (fun (ident, _, _, _) -> Name.of_ident true ident)

let rec of_expression (typ_vars : Name.t Name.Map.t) (e : expression) :
    t Monad.t =
  set_env e.exp_env
    (set_loc e.exp_loc
       (let* attributes = Attribute.of_attributes e.exp_attributes in
        let typ = e.exp_type in
        (* We do not indent here to preserve the diff. *)
        let* e =
          match e.exp_desc with
          | Texp_ident (path, _, _) ->
              let implicits = Attribute.get_implicits attributes in
              let* x = MixedPath.of_path true path in
              let x =
                if
                  String.equal (MixedPath.to_string x) "equiv_decb"
                  && not (equality_argument_has_rocq_eq_dec e)
                then
                  MixedPath.PathName
                    (PathName.__make
                       [ "RocqOfOCaml"; "Basics"; "Stdlib" ]
                       "polymorphic_equal")
                else if
                  String.equal (MixedPath.to_string x) "nequiv_decb"
                  && not (equality_argument_has_rocq_eq_dec e)
                then
                  MixedPath.PathName
                    (PathName.__make
                       [ "RocqOfOCaml"; "Basics"; "Stdlib" ]
                       "polymorphic_not_equal")
                else x
              in
              let variable = Variable (x, implicits) in
              if not (is_partial_operation_path path) then return variable
              else
                let* typ, _, _ =
                  Type.of_typ_expr false typ_vars e.exp_type
                in
                let required_typ = Type.arrow_result typ in
                let* () =
                  warn
                    "a partial OCaml library operation requires an Unreachable \
                     result; prove that its exceptional precondition cannot \
                     occur"
                in
                return
                  (RequiresAssumption
                     (Unreachable, required_typ, variable))
          | Texp_constant constant ->
              Constant.of_constant constant >>= fun constant ->
              return (Constant constant)
          | Texp_let (is_rec, cases, e2) ->
              let* bound_names =
                cases
                |> Monad.List.concat_map (fun { vb_pat; _ } ->
                       names_bound_by_pattern vb_pat)
              in
              push_term_environment (List.map Name.to_string bound_names)
                (of_expression typ_vars e2)
              >>= fun e2 ->
              of_let typ_vars is_rec cases e2
          | Texp_function (params, body) ->
              let is_gadt_match =
                Attribute.has_match_gadt attributes
                || Attribute.has_match_gadt_with_result attributes
              in
              let is_tagged_match = Attribute.has_tagged_match attributes in
              let do_cast_results =
                Attribute.has_match_gadt_with_result attributes
              in
              let is_with_default_case =
                Attribute.has_match_with_default attributes
              in
              let is_grab_existentials =
                Attribute.has_grab_existentials attributes
              in
              let* parameter_names =
                params
                |> Monad.List.concat_map (fun { fp_kind; _ } ->
                       match fp_kind with
                       | Tparam_pat pattern
                       | Tparam_optional_default (pattern, _) ->
                           names_bound_by_pattern pattern)
              in
              let of_param body { fp_kind; _ } =
                let of_pat pat =
                  let is_module_unpack = Pattern.has_unpack_marker pat in
                  match (is_module_unpack, pat.pat_desc) with
                  | ( true,
                      ( Tpat_var (x, _, _)
                      | Tpat_alias ({ pat_desc = Tpat_any; _ }, x, _, _, _) )
                    ) ->
                      let* x = Name.of_ident true x in
                      let* typ, _, _ =
                        Type.of_typ_expr true typ_vars pat.pat_type
                      in
                      let parameter_expr = Variable (MixedPath.of_name x, []) in
                      return
                        (Function
                           ( x,
                             Some typ,
                             Match
                               ( parameter_expr,
                                 None,
                                 [ (Pattern.ModuleUnpack x, None, body) ],
                                 false ) ))
                  | ( _,
                      ( Tpat_var (x, _, _)
                      | Tpat_alias ({ pat_desc = Tpat_any; _ }, x, _, _, _) )
                    ) ->
                      let* x = Name.of_ident true x in
                      let* typ, _, _ =
                        Type.of_typ_expr true typ_vars pat.pat_type
                      in
                      return (Function (x, Some typ, body))
                  | _ ->
                      let* typ, _, _ =
                        Type.of_typ_expr true typ_vars pat.pat_type
                      in
                      let parameter = Name.FunctionParameter in
                      let parameter_expr =
                        Variable (MixedPath.of_name parameter, [])
                      in
                      let* pattern = Pattern.of_pattern pat in
                      let cases =
                        match pattern with
                        | None -> []
                        | Some pattern -> [ (pattern, None, body) ]
                      in
                      return
                        (Function
                           ( parameter,
                             Some typ,
                             Match (parameter_expr, None, cases, false) ))
                in
                match fp_kind with
                | Tparam_pat pat -> of_pat pat
                | Tparam_optional_default (pat, default) ->
                    let* typ, _, _ =
                      Type.of_typ_expr true typ_vars pat.pat_type
                    in
                    let option_typ =
                      Type.Apply
                        ( MixedPath.of_name (Name.of_string_raw "option"),
                          [ (typ, false) ] )
                    in
                    let* pattern = Pattern.of_pattern pat in
                    let* default = of_expression typ_vars default in
                    let optional_name =
                      match pat.pat_desc with
                      | Tpat_var (ident, _, _)
                      | Tpat_alias
                          ({ pat_desc = Tpat_any; _ }, ident, _, _, _) ->
                          Name.of_string_raw
                            (Ident.name ident ^ "_optional")
                      | _ -> Name.of_string_raw "optional_parameter"
                    in
                    let optional_value =
                      Variable (MixedPath.of_name optional_name, [])
                    in
                    let some_name =
                      PathName.of_name [] (Name.of_string_raw "Some")
                    in
                    let none_name =
                      PathName.of_name [] (Name.of_string_raw "None")
                    in
                    (match pattern with
                    | None ->
                        raise body Unexpected
                          "An optional-default parameter has an impossible \
                           pattern"
                    | Some pattern ->
                        let default_branch =
                          Match
                            ( default,
                              None,
                              [ (pattern, None, body) ],
                              false )
                        in
                        return
                          (Function
                             ( optional_name,
                               Some option_typ,
                               Match
                                 ( optional_value,
                                   None,
                                   [
                                     ( Pattern.Constructor
                                         (some_name, [ pattern ]),
                                       None,
                                       body );
                                     ( Pattern.Constructor (none_name, []),
                                       None,
                                       default_branch );
                                   ],
                                   false ) )))
              in
              let* body =
                match body with
                | Tfunction_body e ->
                    push_term_environment
                      (List.map Name.to_string parameter_names)
                      (of_expression typ_vars e)
                | Tfunction_cases
                    {
                      cases =
                        [
                          {
                            c_lhs =
                              {
                                  pat_desc =
                                    ( Tpat_var (x, _, _)
                                    | Tpat_alias
                                        ( { pat_desc = Tpat_any; _ },
                                          x,
                                          _,
                                          _,
                                          _ ) );
                                  pat_type;
                                  pat_extra;
                                  _;
                                };
                            c_guard = None;
                            c_rhs = e;
                            _;
                          };
                        ];
                      _;
                    }
                  when not
                         (List.exists
                            (fun (extra, _, _) ->
                              match extra with Tpat_unpack -> true | _ -> false)
                            pat_extra) ->
                    let* x = Name.of_ident true x in
                    let* typ, _, _ = Type.of_typ_expr true typ_vars pat_type in
                    push_term_environment
                      (List.map Name.to_string (x :: parameter_names))
                      (of_expression typ_vars e)
                    >>= fun e ->
                    return (Function (x, Some typ, e))
                | Tfunction_cases { cases; _ } ->
                    let* x, typ, e =
                      open_cases typ_vars cases is_gadt_match is_tagged_match
                        do_cast_results is_with_default_case is_grab_existentials
                    in
                    return (Function (x, typ, e))
              in
              List.fold_right
                (fun param body -> body >>= fun body -> of_param body param)
                params (return body)
          | Texp_apply
              ( { exp_desc = Texp_ident (path, _, _); _ },
                e_xs )
            when
              List.mem (Path.name path)
                [
                  "Stdlib.failwith";
                  "Pervasives.failwith";
                  "Stdlib.invalid_arg";
                  "Pervasives.invalid_arg";
                  "Stdlib.raise";
                  "Pervasives.raise";
                ] ->
              let* arguments =
                e_xs
                |> Monad.List.filter_map (fun (_, argument) ->
                       match argument with
                       | Arg argument ->
                           let* argument = of_expression typ_vars argument in
                           return (Some argument)
                       | Omitted () -> return None)
              in
              let is_todo =
                match arguments with
                | Constant (Constant.String message) :: _ ->
                    String.length message >= 5
                    && String.sub message 0 5 = "todo "
                | _ -> false
              in
              let kind =
                if
                  List.mem (Path.name path)
                    [ "Stdlib.failwith"; "Pervasives.failwith" ]
                  && is_todo
                then Unimplemented
                else Unreachable
              in
              let* typ, _, _ =
                Type.of_typ_expr false typ_vars e.exp_type
              in
              let* () =
                match kind with
                | Unreachable ->
                    warn
                      "an OCaml exception primitive is represented by an \
                       Unreachable result; prove that this call cannot return"
                | Unimplemented ->
                    warn
                      "an explicitly unimplemented OCaml operation is \
                       represented by an Unimplemented result"
              in
              return (Assumption (kind, typ, arguments))
          | Texp_apply (source_e_f, e_xs) -> (
              let partial_operation =
                match source_e_f.exp_desc with
                | Texp_ident (path, _, _) -> is_partial_operation_path path
                | _ -> false
              in
              of_expression typ_vars source_e_f >>= fun e_f ->
              let rec peel_requirements requirements = function
                | RequiresAssumption (kind, typ, body) ->
                    peel_requirements ((kind, typ) :: requirements) body
                | body -> (List.rev requirements, body)
              in
              let inherited_requirements, e_f =
                peel_requirements [] e_f
              in
              let partial_operation_already_warned =
                partial_operation && inherited_requirements <> []
              in
              infer_projection_implicits typ_vars source_e_f e_f
              >>= fun e_f ->
              e_xs
              |> Monad.List.map (fun (_, e_x) ->
                     match e_x with
                     | Arg e_x ->
                         of_expression typ_vars e_x >>= fun e_x ->
                         return (Some e_x)
                     | Omitted () -> return None)
              >>= fun e_xs ->
              (* We consider the OCaml's [@@] and [|>] operators as syntactic sugar. *)
              let e_f, e_xs =
                match (e_f, e_xs) with
                | ( Variable
                      ( MixedPath.PathName
                          {
                            PathName.path =
                              [ Name.Make ("Pervasives" | "Stdlib") ];
                            base = Name.Make "op_atat";
                          },
                        [] ),
                    [ Some f; x ] ) ->
                    (f, [ x ])
                | ( Variable
                      ( MixedPath.PathName
                          {
                            PathName.path =
                              [ Name.Make ("Pervasives" | "Stdlib") ];
                            base = Name.Make "op_pipegt";
                          },
                        [] ),
                    [ x; Some f ] ) ->
                    (f, [ x ])
                | _ -> (e_f, e_xs)
              in
              (* We introduce a monadic notation according to the configuration. *)
              let* configuration = get_configuration in
              let apply_with_let =
                match (e_f, e_xs) with
                | ( Variable (MixedPath.PathName path_name, []),
                    [ Some e1; Some (Function (x, _, e2)) ] ) -> (
                    let name = PathName.to_string path_name in
                    match Configuration.is_monadic_let configuration name with
                    | Some let_symbol ->
                        Some (LetVar (Some let_symbol, x, [], e1, e2))
                    | None -> None)
                | _ -> None
              in
              let* apply_with_let_return =
                match (e_f, e_xs) with
                | ( Variable (MixedPath.PathName path_name, []),
                    [ Some e1; Some (Function (x, _, e2)) ] ) -> (
                    let name = PathName.to_string path_name in
                    match
                      Configuration.is_monadic_let_return configuration name
                    with
                    | Some (let_symbol, return_notation) ->
                        let* return_e2 = smart_return return_notation e2 in
                        return
                          (Some (LetVar (Some let_symbol, x, [], e1, return_e2)))
                    | None -> return None)
                | _ -> return None
              in
              let* apply_with_return =
                match (e_f, e_xs) with
                | Variable (MixedPath.PathName path_name, []), [ Some e ] -> (
                    let name = PathName.to_string path_name in
                    match
                      Configuration.is_monadic_return configuration name
                    with
                    | Some return_notation ->
                        let* return_e = smart_return return_notation e in
                        return (Some return_e)
                    | None -> return None)
                | _ -> return None
              in
              let* apply_with_return_let =
                match (e_f, e_xs) with
                | ( Variable (MixedPath.PathName path_name, []),
                    [ Some e1; Some (Function (x, _, e2)) ] ) -> (
                    let name = PathName.to_string path_name in
                    match
                      Configuration.is_monadic_return_let configuration name
                    with
                    | Some (return_notation, let_symbol) ->
                        let* return_e1 = smart_return return_notation e1 in
                        return
                          (Some (LetVar (Some let_symbol, x, [], return_e1, e2)))
                    | None -> return None)
                | _ -> return None
              in
              let apply_with_infix_operator =
                match (e_f, e_xs) with
                | Variable (mixed_path, []), [ Some e1; Some e2 ] -> (
                    let name = MixedPath.to_string mixed_path in
                    match
                      Configuration.is_operator_infix configuration name
                    with
                    | None -> None
                    | Some operator -> Some (InfixOperator (operator, e1, e2)))
                | _ -> None
              in
              let applies =
                [
                  apply_with_let;
                  apply_with_let_return;
                  apply_with_return;
                  apply_with_return_let;
                  apply_with_infix_operator;
                ]
              in
              let* application_typ, _, _ =
                Type.of_typ_expr false typ_vars e.exp_type
              in
              let apply =
                match List.find_map (fun x -> x) applies with
                | Some apply -> apply
                | None ->
                    let application =
                      SourceApply (e_f, e_xs, application_typ)
                    in
                    if is_ocaml_format_function e_f then
                      TypAnnotation (application, application_typ)
                    else application
              in
              let apply =
                List.fold_right
                  (fun (kind, typ) body ->
                    RequiresAssumption (kind, typ, body))
                  inherited_requirements apply
              in
              if not partial_operation then return apply
              else
                let* () =
                  if partial_operation_already_warned then return ()
                  else
                    warn
                      "a partial OCaml library operation requires an \
                       Unreachable result; prove that its exceptional \
                       precondition cannot occur"
                in
                return
                  (RequiresAssumption
                     (Unreachable, application_typ, apply)))
          | Texp_match (e, cases, [], _) ->
              let is_gadt_match =
                Attribute.has_match_gadt attributes
                || Attribute.has_match_gadt_with_result attributes
              in
              let is_tagged_match = Attribute.has_tagged_match attributes in
              let do_cast_results =
                Attribute.has_match_gadt_with_result attributes
              in
              let is_with_default_case =
                Attribute.has_match_with_default attributes
              in
              let is_grab_existential =
                Attribute.has_grab_existentials attributes
              in
              let* e = of_expression typ_vars e in
              of_match typ_vars e cases is_gadt_match is_tagged_match
                do_cast_results is_with_default_case is_grab_existential
          | Texp_match (_, _, _ :: _, _) ->
              raise (Error "effect_matching") SideEffect
                "Effect handlers are not supported"
          | Texp_tuple es ->
              let es = List.map snd es in
              Monad.List.map (of_expression typ_vars) es >>= fun es ->
              return (Tuple es)
          | Texp_construct (_, constructor_description, es) -> (
              let* es' = Monad.List.map (of_expression typ_vars) es in
              match constructor_description.cstr_tag with
              | Cstr_extension (path, _) ->
                  let* typs =
                    es
                    |> Monad.List.map (fun { exp_type; _ } ->
                           Type.of_type_expr_without_free_vars exp_type)
                  in
                  let typ = Type.Tuple typs in
                  let e = Tuple es' in
                  return (ConstructorExtensible (Path.last path, typ, e))
              | _ ->
                  let implicits = Attribute.get_implicits attributes in
                  let* x =
                    PathName.of_constructor_description constructor_description
                  in
                  let constructor = Constructor (x, implicits, es') in
                  if
                    List.mem constructor_description.cstr_name
                      [ "Ok"; "Error" ]
                  then
                    let* typ, _, _ =
                      Type.of_typ_expr true typ_vars typ
                    in
                    return (TypAnnotation (constructor, typ))
                  else return constructor)
          | Texp_variant (label, e) -> (
              let* path_name = PathName.constructor_of_variant label in
              match path_name with
              | None ->
                  let* typ_e =
                    match e with
                    | None -> return None
                    | Some e ->
                        let* typ =
                          Type.of_type_expr_without_free_vars e.exp_type
                        in
                        let* e = of_expression typ_vars e in
                        return (Some (typ, e))
                  in
                  return (ConstructorVariant (label, typ_e))
              | Some path_name -> (
                  let constructor =
                    Variable (MixedPath.PathName path_name, [])
                  in
                  match e with
                  | None -> return constructor
                  | Some e ->
                      let* e = of_expression typ_vars e in
                      return (Apply (constructor, [ Some e ]))))
          | Texp_record { fields; extended_expression; _ } -> (
              Array.to_list fields
              |> Monad.List.filter_map (fun (label_description, definition) ->
                     (match definition with
                     | Kept _ -> return None
                     | Overridden (_, e) ->
                         PathName.of_label_description label_description
                         >>= fun x ->
                         let* typ =
                           Type.of_type_expr_without_free_vars
                             label_description.lbl_arg
                         in
                         let arity = Type.nb_forall_typs typ in
                         return (Some (x, arity, e)))
                     >>= fun x_e ->
                     match x_e with
                     | None -> return None
                     | Some (x, arity, e) ->
                         of_expression typ_vars e >>= fun e ->
                         return (Some (x, arity, e)))
              >>= fun fields ->
              match extended_expression with
              | None -> return (Record fields)
              | Some extended_expression ->
                  of_expression typ_vars extended_expression
                  >>= fun extended_e ->
                  return
                    (List.fold_left
                       (fun extended_e (x, _, e) ->
                         Apply
                           ( Variable
                               ( MixedPath.PathName (PathName.prefix_by_with x),
                                 [] ),
                             [ Some e; Some extended_e ] ))
                       extended_e fields))
          | Texp_atomic_loc _ ->
              raise (Error "atomic_loc") NotSupported
                "Atomic locations are not supported"
          | Texp_field (e, _, label_description) ->
              PathName.of_label_description label_description >>= fun x ->
              of_expression typ_vars e >>= fun e -> return (Field (e, x))
          | Texp_ifthenelse (e1, e2, e3) ->
              of_expression typ_vars e1 >>= fun e1 ->
              of_expression typ_vars e2 >>= fun e2 ->
              (match e3 with
              | None -> return (Tuple [])
              | Some e3 -> of_expression typ_vars e3)
              >>= fun e3 -> return (IfThenElse (e1, e2, e3))
          | Texp_sequence (e1, e2) ->
              let* e1 = of_expression typ_vars e1 in
              let* e2 = of_expression typ_vars e2 in
              return (Match (e1, None, [ (Pattern.Any, None, e2) ], false))
          | Texp_try (e, cases, []) ->
              let* e = of_expression typ_vars e in
              let exception_name =
                Name.of_string_raw "_exception_value"
              in
              let exception_value =
                Variable (MixedPath.of_name exception_name, [])
              in
              let* error_handler =
                of_match_extensible typ_vars exception_value cases
              in
              return
                (Apply
                   ( Variable
                       ( MixedPath.of_name (Name.of_string_raw "try_with"),
                         [] ),
                     [
                       Some (Function (Name.Nameless, None, e));
                       Some
                         (Function
                            (exception_name, None, error_handler));
                     ] ))
          | Texp_try (_, _, _ :: _) ->
              raise (Error "effect_try") SideEffect
                "Effect handlers are not supported"
          | Texp_setfield (e_record, _, { lbl_name; _ }, e) ->
              of_expression typ_vars e_record >>= fun e_record ->
              of_expression typ_vars e >>= fun e ->
              error_message
                (Apply
                   ( Error "set_record_field",
                     [
                       Some e_record;
                       Some (Constant (Constant.String lbl_name));
                       Some e;
                     ] ))
                SideEffect "Set record field not handled."
          | Texp_array (_, es) ->
              Monad.List.map (of_expression typ_vars) es >>= fun es ->
              return (ErrorArray es)
          | Texp_while _ ->
              error_message (Error "while") SideEffect
                "While loops not handled."
          | Texp_for _ ->
              error_message (Error "for") SideEffect "For loops not handled."
          | Texp_send _ ->
              error_message (Error "send") NotSupported
                "Sending method message is not handled"
          | Texp_new _ ->
              error_message (Error "new") NotSupported
                "Creation of new objects is not handled"
          | Texp_instvar _ ->
              error_message (Error "instance_variable") NotSupported
                "Creating an instance variable is not handled"
          | Texp_setinstvar _ ->
              error_message (Error "set_instance_variable") SideEffect
                "Setting an instance variable is not handled"
          | Texp_override _ ->
              error_message (Error "override") NotSupported
                "Overriding is not handled"
          | Texp_letmodule
              ( x,
                _,
                _,
                {
                  mod_desc =
                    Tmod_unpack ({ exp_desc = Texp_ident (path, _, _); _ }, _);
                  _;
                },
                e ) ->
              let* x = Name.of_optional_ident true x in
              PathName.of_path_with_convert false path
              >>= fun path_name ->
              of_expression typ_vars e >>= fun e ->
              return (LetModuleUnpack (x, path_name, e))
          | Texp_letmodule (x, _, _, module_expr, e) ->
              let x_ident = x in
              let* x = Name.of_optional_ident true x_ident in
              let* module_signature =
                let path =
                  match module_expr.mod_desc with
                  | Tmod_ident (path, _) -> Some path
                  | _ -> None
                in
                let* classification =
                  IsFirstClassModule.is_module_typ_first_class
                    module_expr.mod_type path
                in
                match classification with
                | IsFirstClassModule.Found _ -> return classification
                | IsFirstClassModule.Not_found _ ->
                    let rec root_functor_path module_expr =
                      match module_expr.mod_desc with
                      | Tmod_ident (path, _) -> Some path
                      | Tmod_apply (functor_expr, _, _)
                      | Tmod_apply_unit functor_expr
                      | Tmod_constraint
                          (functor_expr, _, _, _) ->
                          root_functor_path functor_expr
                      | Tmod_structure _
                      | Tmod_functor _
                      | Tmod_unpack _
                      | Tmod_typed_hole ->
                          None
                    in
                    (match root_functor_path module_expr with
                    | Some functor_path ->
                        let* result_signature =
                          get_functor_result_signature functor_path
                        in
                        (match result_signature with
                        | Some signature_path ->
                            return
                              (IsFirstClassModule.Found
                                 signature_path)
                        | None -> return classification)
                    | None -> return classification)
              in
              push_env
                ( of_module_expr typ_vars module_expr None >>= fun value ->
                  set_env e.exp_env
                    (push_env
                       ( (match (x_ident, module_signature) with
                         | ( Some ident,
                             IsFirstClassModule.Found
                               signature_path ) ->
                             set_signature_hint
                               (Path.Pident ident)
                               signature_path
                               (of_expression typ_vars e)
                         | ( None,
                             IsFirstClassModule.Found _ )
                         | ( _,
                             IsFirstClassModule.Not_found _ ) ->
                             of_expression typ_vars e)
                       >>= fun e ->
                         return (LetVar (None, x, [], value, e)) )) )
          | Texp_letexception _ ->
              error_message (Error "let_exception") SideEffect
                "Let of exception is not handled"
          | Texp_assert (e',_) ->
              Type.of_typ_expr false typ_vars e.exp_type >>= fun (typ, _, _) ->
              of_expression typ_vars e' >>= fun e' ->
              warn
                "an OCaml assertion failure is represented by an Unreachable \
                 result; prove that the assertion cannot fail"
              >>= fun () ->
              return (Assert (typ, e'))
          | Texp_lazy e ->
              of_expression typ_vars e >>= fun e ->
              error_message
                (Apply (Error "lazy", [ Some e ]))
                SideEffect "Lazy expressions are not handled"
          | Texp_object _ ->
              error_message (Error "object") NotSupported
                "Creation of objects is not handled"
          | Texp_pack module_expr ->
              let* module_typ_params =
                ModuleTypParams.get_module_typ_typ_params_arity
                  module_expr.mod_type
              in
              push_env (of_module_expr typ_vars module_expr None) >>= fun e ->
              return (ModulePack (module_typ_params, e))
          | Texp_letop
              {
                let_ = { bop_op_path; bop_exp; _ };
                ands;
                body = { c_lhs; c_rhs; _ };
                _;
              } -> (
              match ands with
              | [] -> (
                  let* let_symbol_mixed_path =
                    MixedPath.of_path true bop_op_path
                  in
                  let let_symbol = MixedPath.to_string let_symbol_mixed_path in
                  let* configuration = get_configuration in
                  let let_symbol =
                    Configuration.is_monadic_let configuration let_symbol
                  in
                  let* pattern = Pattern.of_pattern c_lhs in
                  let* e1 = of_expression typ_vars bop_exp in
                  let* e2 = of_expression typ_vars c_rhs in
                  let cases =
                    match pattern with
                    | None -> []
                    | Some pattern -> [ (pattern, None, e2) ]
                  in
                  match (let_symbol, pattern) with
                  | None, Some (Variable name) ->
                      return
                        (Apply
                           ( Variable (let_symbol_mixed_path, []),
                             [ Some e1; Some (Function (name, None, e2)) ] ))
                  | None, _ ->
                      return
                        (Apply
                           ( Variable (let_symbol_mixed_path, []),
                             [
                               Some e1;
                               Some
                                 (Function
                                    ( Name.FunctionParameter,
                                      None,
                                      Match
                                        ( Variable
                                            ( MixedPath.PathName
                                                {
                                                  PathName.path = [];
                                                  base = Name.FunctionParameter;
                                                },
                                              [] ),
                                          None,
                                          cases,
                                          false ) ));
                             ] ))
                  | Some let_symbol, Some (Variable name) ->
                      return (LetVar (Some let_symbol, name, [], e1, e2))
                  | Some let_symbol, _ ->
                      return
                        (LetVar
                           ( Some let_symbol,
                             Name.FunctionParameter,
                             [],
                             e1,
                             Match
                               ( Variable
                                   ( MixedPath.PathName
                                       {
                                         PathName.path = [];
                                         base = Name.FunctionParameter;
                                       },
                                     [] ),
                                 None,
                                 cases,
                                 false ) )))
              | _ :: _ ->
                  error_message (Error "let_op_and") NotSupported
                    "We do not support let operators with and")
          | Texp_unreachable ->
              let* typ, _, _ =
                Type.of_typ_expr false typ_vars e.exp_type
              in
              let* () =
                warn
                  "an OCaml unreachable expression is represented by an \
                   Unreachable result; prove that this expression cannot be \
                   evaluated"
              in
              return (Assumption (Unreachable, typ, []))
          | Texp_extension_constructor _ ->
              error_message (Error "extension") NotSupported
                "Construction of extensions is not handled"
          | Texp_open (open_declaration, e) ->
              let {
                open_expr;
                open_bound_items;
                _;
              } = open_declaration
              in
              let rec raw_module_expr_path
                  (module_expr : Typedtree.module_expr) :
                  Path.t option =
                match module_expr.mod_desc with
                | Tmod_ident (path, _) -> Some path
                | Tmod_apply (functor_expr, argument_expr, _) ->
                    Option.bind
                      (raw_module_expr_path functor_expr)
                      (fun functor_path ->
                        Option.map
                          (fun argument_path ->
                            Path.Papply
                              (functor_path, argument_path))
                          (raw_module_expr_path argument_expr))
                | Tmod_constraint (inner, _, _, _) ->
                    raw_module_expr_path inner
                | Tmod_structure _
                | Tmod_functor _
                | Tmod_apply_unit _
                | Tmod_unpack _
                | Tmod_typed_hole ->
                    None
              in
              let* opened_signature =
                let path =
                  match open_expr.mod_desc with
                  | Tmod_ident (path, _) -> Some path
                  | _ -> None
                in
                let* classification =
                  IsFirstClassModule.is_module_typ_first_class
                    open_expr.mod_type path
                in
                match classification with
                | IsFirstClassModule.Found _ -> return classification
                | IsFirstClassModule.Not_found _ ->
                    let rec root_functor_path module_expr =
                      match module_expr.mod_desc with
                      | Tmod_ident (path, _) -> Some path
                      | Tmod_apply (functor_expr, _, _)
                      | Tmod_apply_unit functor_expr
                      | Tmod_constraint
                          (functor_expr, _, _, _) ->
                          root_functor_path functor_expr
                      | Tmod_structure _
                      | Tmod_functor _
                      | Tmod_unpack _
                      | Tmod_typed_hole ->
                          None
                    in
                    (match root_functor_path open_expr with
                    | Some functor_path ->
                        let* result_signature =
                          get_functor_result_signature functor_path
                        in
                        (match result_signature with
                        | Some signature_path ->
                            return
                              (IsFirstClassModule.Found
                                 signature_path)
                        | None -> return classification)
                    | None -> return classification)
              in
              let translate_body (opened_path : Path.t) =
                List.fold_right
                  (fun signature_item body ->
                    let ident =
                      Types.signature_item_id signature_item
                    in
                    set_module_path_alias
                      (Path.Pident ident)
                      (Path.Pdot
                         (opened_path, Ident.name ident))
                      body)
                  open_bound_items (of_expression typ_vars e)
              in
              (match opened_signature with
              | IsFirstClassModule.Found signature_path ->
                  let opened_ident =
                    Ident.create_local
                      ("opened_module_"
                      ^ string_of_int
                          open_declaration.open_loc.loc_start.pos_cnum)
                  in
                  let opened_path = Path.Pident opened_ident in
                  let* opened_name =
                    Name.of_ident false opened_ident
                  in
                  let* opened_value =
                    of_module_expr typ_vars open_expr None
                  in
                  let body =
                    let body = translate_body opened_path in
                    let source_paths =
                      [
                        raw_module_expr_path open_expr;
                        ModulePathAliases.module_expr_path open_expr;
                      ]
                      |> List.filter_map (fun path -> path)
                      |> List.sort_uniq Path.compare
                    in
                    List.fold_right
                      (fun source_path body ->
                        set_module_path_alias source_path
                          opened_path body)
                      source_paths body
                  in
                  let* body =
                    set_signature_hint opened_path signature_path
                      body
                  in
                  return
                    (LetVar
                       ( None,
                         opened_name,
                         [],
                         opened_value,
                         body ))
              | IsFirstClassModule.Not_found _ ->
                  (match
                     ModulePathAliases.module_expr_path open_expr
                   with
                  | Some opened_path ->
                      translate_body opened_path
                  | None ->
                      error_message
                        (Error "local_open")
                        NotSupported
                        "A local open of an anonymous namespace is not supported."))
          | Texp_typed_hole ->
              error_message (Error "expression_hole") Unexpected
                "Unexpected expression hole"
        in
        if Attribute.has_cast attributes then
          let* typ, _, _ = Type.of_typ_expr false typ_vars typ in
          return (Cast (e, typ))
        else if Attribute.has_typ_annotation attributes then
          let* typ, _, _ = Type.of_typ_expr false typ_vars typ in
          return (TypAnnotation (e, typ))
        else return e))

and of_match :
    type k.
    Name.t Name.Map.t ->
    t ->
    k case list ->
    bool ->
    bool ->
    bool ->
    bool ->
    bool ->
    t Monad.t =
 fun typ_vars e cases is_gadt_match is_tagged_match do_cast_results
     is_with_default_case is_grab_existentials ->
  let is_extensible_type_match =
    cases
    |> List.map (fun { c_lhs; _ } -> c_lhs)
    |> Pattern.are_extensible_patterns_or_any true
  in
  let rec variant_labels :
      type kind. kind general_pattern -> string list =
   fun pattern ->
    match pattern.pat_desc with
    | Tpat_variant (label, _, _) -> [ label ]
    | Tpat_alias (pattern, _, _, _, _) -> variant_labels pattern
    | Tpat_or (left, right, _) ->
        variant_labels left @ variant_labels right
    | Tpat_value pattern ->
        variant_labels (pattern :> value general_pattern)
    | _ -> []
  in
  let rec pattern_is_catch_all :
      type kind. kind general_pattern -> bool =
   fun pattern ->
    match pattern.pat_desc with
    | Tpat_any | Tpat_var _ -> true
    | Tpat_alias (pattern, _, _, _, _) -> pattern_is_catch_all pattern
    | Tpat_value pattern ->
        pattern_is_catch_all (pattern :> value general_pattern)
    | _ -> false
  in
  let* is_dynamic_variant_match =
    cases
    |> Monad.List.fold_left
         (fun found { c_lhs; _ } ->
           variant_labels c_lhs
           |> Monad.List.fold_left
                (fun found label ->
                  let* constructor = PathName.constructor_of_variant label in
                  return (found || Option.is_none constructor))
                found)
         false
  in
  let* mapped_variant_needs_default =
    match cases with
    | [] -> return false
    | { c_lhs = ({ pat_type; _ } as c_lhs); _ } :: _ -> (
        let typ =
          try
            Ctype.full_expand ~may_forget_scope:false
              c_lhs.pat_env pat_type
          with _ -> pat_type
        in
        match Types.get_desc typ with
        | Tvariant row_desc when not is_dynamic_variant_match ->
            let labels = Types.row_fields row_desc |> List.map fst in
            let* configuration = get_configuration in
            let covered_labels =
              cases
              |> List.concat_map (fun { c_lhs; _ } -> variant_labels c_lhs)
              |> List.sort_uniq String.compare
            in
            let source_has_default =
              List.exists
                (fun { c_lhs; _ } -> pattern_is_catch_all c_lhs)
                cases
            in
            return
              (not source_has_default
              &&
              (not (Types.row_closed row_desc)
              || not (Configuration.variant_row_is_exact configuration labels)
              || not
                   (List.equal String.equal covered_labels
                      (List.sort_uniq String.compare labels))))
        | _ -> return false)
  in
  let* match_result_typ =
    match cases with
    | [] -> return (Type.Error "empty_match")
    | { c_rhs; _ } :: _ ->
        let* typ, _, _ =
          Type.of_typ_expr false typ_vars c_rhs.exp_type
        in
        return typ
  in
  if is_dynamic_variant_match then of_match_variant typ_vars e cases
  else if is_extensible_type_match then of_match_extensible typ_vars e cases
  else
    let* (dep_match : dependent_pattern_match option) =
      match cases with
      | [] -> return None
      | { c_lhs; c_rhs; _ } :: _ ->
          if not is_tagged_match then return None
          else
            let* cast, _, new_typ_vars =
              Type.of_typ_expr true Name.Map.empty c_lhs.pat_type
            in
            let* motive, _, new_typ_vars' =
              Type.of_typ_expr true Name.Map.empty c_rhs.exp_type
            in
            let new_typ_vars = VarEnv.union new_typ_vars new_typ_vars' in
            let* cast = Type.decode_var_tags new_typ_vars false cast in
            let* motive = Type.decode_var_tags new_typ_vars false motive in
            let cast, args = Type.normalize_constructor cast in
            (* Only generates dependent pattern matching for actual gadts *)
            if List.length args = 0 || Type.is_native_type cast then return None
            else return (Some { cast; args; motive })
    in
    cases
    |> Monad.List.filter_map (fun { c_lhs; c_guard; c_rhs; _ } ->
           set_loc c_lhs.pat_loc
             (let* bound_vars =
                Typedtree.pat_bound_idents c_lhs
                |> List.rev
                |> Monad.List.map (fun ident ->
                       let { Types.val_type; _ } =
                         Env.find_value (Path.Pident ident) c_rhs.exp_env
                       in
                       let* name = Name.of_ident true ident in
                       return (name, val_type))
              in
              let typs = List.map snd bound_vars in
              let tag_list = Type.tag_no_args typs in
              let* new_typ_vars =
                Type.typed_existential_typs_of_typs typs tag_list
              in
              Monad.List.map
                (fun (name, typ) ->
                  Type.of_typ_expr true typ_vars typ >>= fun (typ, _, _) ->
                  return (name, typ))
                bound_vars
              >>= fun bound_vars ->
              let env_has_tag =
                List.exists (fun (_, ki) -> ki = Kind.Tag) new_typ_vars
              in
              let new_typ_vars =
                if is_gadt_match then new_typ_vars
                else
                  let free_vars =
                    Type.local_typ_constructors_of_typs
                      (List.map snd bound_vars)
                    |> Name.Set.elements
                  in
                  let tag_vars =
                    new_typ_vars
                    |> List.filter_map (fun (name, ki) ->
                           if ki = Kind.Tag then Some name else None)
                  in
                  VarEnv.keep_only (free_vars @ tag_vars) new_typ_vars
              in

              let* bound_vars =
                Monad.List.map
                  (fun (x, ty) ->
                    let* ty = Type.decode_var_tags new_typ_vars false ty in
                    return (x, ty))
                  bound_vars
              in

              let* typ =
                if is_gadt_match || do_cast_results || not env_has_tag then
                  let* typ, _, _ =
                    Type.of_typ_expr true typ_vars c_rhs.exp_type
                  in
                  return typ
                else
                  (* Only expand type if you really need to. It may cause the translation to break *)
                  let typ =
                    Ctype.full_expand ~may_forget_scope:false c_rhs.exp_env
                      c_rhs.exp_type
                  in
                  let* typ, _, _ = Type.of_typ_expr true typ_vars typ in
                  return typ
              in

              let existential_cast =
                Some
                  {
                    new_typ_vars;
                    bound_vars;
                    return_typ = typ;
                    use_axioms = is_gadt_match;
                    cast_result = do_cast_results;
                    enable = is_grab_existentials || is_gadt_match;
                  }
              in

              (match c_guard with
              | Some guard ->
                  of_expression typ_vars guard >>= fun guard ->
                  return (Some guard)
              | None -> return None)
              >>= fun guard ->
              Pattern.of_pattern c_lhs >>= fun pattern ->
              match c_rhs.exp_desc with
              | Texp_unreachable -> return None
              | _ ->
                  of_expression typ_vars c_rhs >>= fun e ->
                  let e = dependent_transform e dep_match in
                  return
                    (pattern
                    |> Option.map (fun pattern ->
                           (pattern, existential_cast, guard, e)))))
    >>= fun cases_with_guards ->
    let guards =
      cases_with_guards
      |> List.filter_map (function
           | p, _, Some guard, _ -> Some (p, guard)
           | _ -> None)
    in
    let guard_checks =
      guards
      |> List.map (fun (p, guard) ->
             let cases =
               [ (p, None, guard) ]
               @
               if Pattern.is_irrefutable p then []
               else
                 [
                   ( Pattern.Any,
                     None,
                     Variable (MixedPath.PathName PathName.false_value, []) );
                 ]
             in
             Match (e, None, cases, false))
    in
    let e = match guards with [] -> e | _ :: _ -> Tuple (e :: guard_checks) in
    let i = ref (-1) in
    let nb_guards = List.length guard_checks in
    let cases =
      cases_with_guards
      |> List.map (fun (p, existential_cast, guard, rhs) ->
             let is_guarded =
               match guard with Some _ -> true | None -> false
             in
             if is_guarded then i := !i + 1;
             let p =
               if nb_guards = 0 then p
               else
                 Pattern.Tuple
                   (p :: any_patterns_with_ith_true is_guarded !i nb_guards)
             in
             (p, existential_cast, rhs))
    in
    let* cases =
      if not mapped_variant_needs_default then return cases
      else
        let* () =
          warn
            "a configured polymorphic-variant target admits tags outside this \
             match; the corresponding Match_failure is represented by an \
             Unreachable result"
        in
        return
          (cases
          @ [
              ( Pattern.Any,
                None,
                Assumption (Unreachable, match_result_typ, []) );
            ])
    in
    (* We remove unused existential type variables *)
    let cases =
      cases
      |> List.map (fun (p, existential_cast, rhs) ->
             let existential_cast =
               match existential_cast with
               | None -> None
               | Some existential_cast ->
                   let { new_typ_vars; bound_vars; return_typ; _ } =
                     existential_cast
                   in
                   let free_typ_vars =
                     let typs = return_typ :: List.map snd bound_vars in
                     Name.Set.union
                       (Type.local_typ_constructors_of_typs typs)
                       (free_existential_typs rhs)
                   in
                   Some
                     {
                       existential_cast with
                       new_typ_vars =
                         VarEnv.keep_only
                           (Name.Set.elements free_typ_vars)
                           new_typ_vars;
                     }
             in
             (p, existential_cast, rhs))
    in
    let t = Match (e, dep_match, cases, is_with_default_case) in
    (* If its a deppendent pattern matching then add eq_refl at the end of the match *)
    match dep_match with
    | None -> return t
    | Some dep_match ->
        let eq_refl = "eq_refl" |> Name.of_string_raw |> MixedPath.of_name in
        let ts =
          List.map (fun _ -> Some (Variable (eq_refl, []))) dep_match.args
        in
        return (Apply (t, ts))

(** We suppose that we know that we have a match of extensible types. *)
and of_match_extensible :
    type kind. Name.t Name.Map.t -> t -> kind case list -> t Monad.t =
 fun (typ_vars : Name.t Name.Map.t) (e : t) (cases : kind case list) ->
  let* result_typ =
    match cases with
    | [] -> return (Type.Error "empty_extensible_match")
    | { c_rhs; _ } :: _ ->
        let* typ, _, _ =
          Type.of_typ_expr false typ_vars c_rhs.exp_type
        in
        return typ
  in
  let* cases =
    cases
    |> Monad.List.map (fun { c_lhs; c_rhs; _ } ->
           set_loc c_lhs.pat_loc
             (let* p = Pattern.of_extensible_pattern c_lhs in
              let* e = of_expression typ_vars c_rhs in
              return (p, e)))
  in
  let* () =
    if List.exists (fun (pattern, _) -> Option.is_none pattern) cases then
      return ()
    else
      warn
        "an unmatched OCaml exception is represented by an Unreachable \
         result; prove that this propagation path cannot occur"
  in
  return (MatchExtensible (e, result_typ, cases))

and of_match_variant :
    type kind. Name.t Name.Map.t -> t -> kind case list -> t Monad.t =
 fun (typ_vars : Name.t Name.Map.t) (e : t) (cases : kind case list) ->
  let* result_typ =
    match cases with
    | [] -> return (Type.Error "empty_dynamic_variant_match")
    | { c_rhs; _ } :: _ ->
        let* typ, _, _ =
          Type.of_typ_expr false typ_vars c_rhs.exp_type
        in
        return typ
  in
  let* nested_cases =
    cases
    |> Monad.List.map (fun { c_lhs; c_guard; c_rhs; _ } ->
           set_loc c_lhs.pat_loc
             (let* patterns = Pattern.of_dynamic_variant_patterns c_lhs in
              let* body = of_expression typ_vars c_rhs in
              match c_guard with
              | None ->
                  return (List.map (fun pattern -> (pattern, body)) patterns)
              | Some _ ->
                  raise
                    (List.map (fun pattern -> (pattern, body)) patterns)
                    NotSupported
                    "Guards on polymorphic-variant matches are not supported"))
  in
  let nested_cases = List.concat nested_cases in
  let has_default =
    List.exists
      (fun (pattern, _) ->
        match pattern with Pattern.VariantDefault _ -> true | _ -> false)
      nested_cases
  in
  let* () =
    if has_default then return ()
    else
      warn
        "a dynamic polymorphic-variant default is represented by an \
         Unreachable result; prove that no other tag can occur"
  in
  return (MatchVariant (e, result_typ, nested_cases))

(** Generate a variable and a "match" on this variable from a list of
    patterns. *)
and open_cases (type pattern_kind) (typ_vars : Name.t Name.Map.t)
    (cases : pattern_kind case list) (is_gadt_match : bool)
    (is_tagged_match : bool) (do_cast_results : bool)
    (is_with_default_case : bool) (is_grab_existentials : bool) :
    (Name.t * Type.t option * t) Monad.t =
  let name = Name.FunctionParameter in
  let* typ =
    match cases with
    | [] -> return None
    | { c_lhs = { pat_type; _ }; _ } :: _ ->
        let* typ, _, _ = Type.of_typ_expr true typ_vars pat_type in
        return (Some typ)
  in
  let e = Variable (MixedPath.of_name name, []) in
  let* e =
    of_match typ_vars e cases is_gadt_match is_tagged_match do_cast_results
      is_with_default_case is_grab_existentials
  in
  return (name, typ, e)

and import_let_fun (typ_vars : Name.t Name.Map.t) (_at_top_level : bool)
    (is_rec : Asttypes.rec_flag) (cases : value_binding list) :
    t option Definition.t Monad.t =
  let is_rec = Recursivity.of_rec_flag is_rec in
  let is_simple_binding_pattern (pattern : value general_pattern) : bool =
    match pattern.pat_desc with
    | Tpat_any
    | Tpat_var _
    | Tpat_alias ({ pat_desc = Tpat_any; _ }, _, _, _, _) ->
        true
    | _ -> false
  in
  let* cases_with_attributes =
    cases
    |> Monad.List.map (fun case ->
           let* attributes = Attribute.of_attributes case.vb_attributes in
           return (case, attributes))
  in
  let find_annotated predicate =
    List.find_opt
      (fun (_, attributes) -> predicate attributes)
      cases_with_attributes
  in
  let* configuration = get_configuration in
  let* enclosing_definition_path = get_definition_path in
  let source_binding_name (pattern : value general_pattern) : string option =
    match pattern.pat_desc with
    | Tpat_var (ident, _, _)
    | Tpat_alias (_, ident, _, _, _) ->
        Some (Ident.name ident)
    | _ -> None
  in
  let find_configured strategy =
    List.find_opt
      (fun (case, _) ->
        match source_binding_name case.vb_pat with
        | None -> false
        | Some name ->
            Configuration.get_recursion_strategy configuration
              (enclosing_definition_path @ [ name ])
            = Some strategy)
      cases_with_attributes
  in
  let well_founded_case =
    match find_annotated Attribute.has_well_founded with
    | Some _ as case -> case
    | None when is_rec ->
        find_configured Configuration.RecursionStrategy.WellFounded
    | None -> None
  in
  let partial_case =
    match find_annotated Attribute.has_partial with
    | Some _ as case -> case
    | None -> find_configured Configuration.RecursionStrategy.Partial
  in
  let convergent_case =
    find_configured Configuration.RecursionStrategy.Convergent
  in
  let* recursion_strategy =
    match (well_founded_case, partial_case, convergent_case) with
    | Some (case, _), Some _, _
    | Some (case, _), _, Some _
    | _, Some (case, _), Some _ ->
        set_loc case.vb_pat.pat_loc
          (raise Definition.Structural Unexpected
             "A definition cannot use more than one recursion strategy.")
    | _, Some (case, _), None ->
        set_loc case.vb_pat.pat_loc
          (let* () =
             warn
               "@rocq.partial changes the translated result type to an explicit \
                partial computation; callers must preserve or discharge its \
                convergence requirement."
           in
           let definition_name =
             match source_binding_name case.vb_pat with
             | Some name ->
                 String.concat "."
                   (enclosing_definition_path @ [ name ])
             | None -> "anonymous"
           in
           return
             (Definition.Partial
                {
                  definition_name;
                  partial_definitions =
                    Configuration.partial_definition_names configuration;
                  recursion = Definition.MayDiverge;
                }))
    | Some (case, attributes), None, None ->
        set_loc case.vb_pat.pat_loc
          (if not is_rec then
             raise Definition.Structural Unexpected
               "@rocq.wf can only annotate a recursive definition."
           else if Attribute.get_structs attributes <> [] then
             raise Definition.Structural Unexpected
               "@rocq.wf cannot be combined with @rocq_struct."
           else if Attribute.has_axiom_with_reason attributes then
             raise Definition.Structural Unexpected
               "@rocq.wf cannot be combined with @rocq_axiom_with_reason."
           else
             let* () =
               warn
                 "@rocq.wf introduces an abstract measure and admitted \
                  well-founded decrease obligations; replace both before \
                  relying on this definition."
             in
             let definition_name =
               match source_binding_name case.vb_pat with
               | Some name ->
                   String.concat "."
                     (enclosing_definition_path @ [ name ])
               | None -> "anonymous"
             in
             return (Definition.WellFounded definition_name))
    | None, None, Some (case, _) ->
        set_loc case.vb_pat.pat_loc
          (if is_rec then
             raise Definition.Structural Unexpected
               "The convergent strategy applies only to non-recursive \
                definitions."
           else
             let* () =
               warn
                 "the convergent strategy keeps the source result type and \
                  introduces admitted convergence obligations for partial \
                  callees; replace those obligations before relying on this \
                  definition."
             in
             let definition_name =
               match source_binding_name case.vb_pat with
               | Some name ->
                   String.concat "."
                     (enclosing_definition_path @ [ name ])
               | None -> "anonymous"
             in
             return (Definition.Convergent definition_name))
    | None, None, None -> return Definition.Structural
  in
  let* destructuring_cases =
    cases_with_attributes
    |> Monad.List.concat_map
         (fun ({ vb_pat; vb_expr; _ }, attributes) ->
           if is_simple_binding_pattern vb_pat then return []
           else
             set_env vb_expr.exp_env
               (set_loc vb_pat.pat_loc
                  (let* pattern = Pattern.of_pattern vb_pat in
                   match pattern with
                   | None | Some Pattern.Any -> return []
                   | Some pattern ->
                       let* translated_expression =
                         if
                           Attribute.has_axiom_with_reason attributes
                         then return None
                         else
                           let* expression =
                             of_expression typ_vars vb_expr
                           in
                           return (Some expression)
                       in
                       let predefined_variables =
                         List.map snd (Name.Map.bindings typ_vars)
                       in
                       Typedtree.pat_bound_idents_full vb_pat
                       |> Monad.List.map
                            (fun (ident, _, source_typ, _) ->
                              let* name = Name.of_ident true ident in
                              let* typ, _, new_typ_vars =
                                Type.of_typ_expr true typ_vars source_typ
                              in
                              let* typ =
                                Type.decode_var_tags new_typ_vars false typ
                              in
                              let new_typ_vars =
                                VarEnv.remove predefined_variables
                                  new_typ_vars
                              in
                              let body =
                                Option.map
                                  (fun expression ->
                                    Match
                                      ( expression,
                                        None,
                                        [
                                          ( pattern,
                                            None,
                                            Variable
                                              ( MixedPath.of_name name,
                                                [] ) );
                                        ],
                                        false ))
                                  translated_expression
                              in
                              let header =
                                {
                                  Header.name;
                                  typ_vars = new_typ_vars;
                                  args = [];
                                  instance_args = [];
                                  structs = [];
                                  typ;
                                  is_notation = false;
                                }
                              in
                              return (header, body)))))
  in
  let simple_cases =
    List.filter
      (fun ({ vb_pat; _ }, _) -> is_simple_binding_pattern vb_pat)
      cases_with_attributes
  in
  simple_cases
  |> Monad.List.filter_map (fun ({ vb_pat = p; vb_expr; _ }, attributes) ->
         let is_axiom = Attribute.has_axiom_with_reason attributes in
         let source_structs = Attribute.get_structs attributes in
         set_env vb_expr.exp_env
           (set_loc p.pat_loc
              ( let source_name = source_binding_name p in
                Pattern.of_pattern p >>= fun p ->
                (match p with
                | Some Pattern.Any -> return None
                | Some (Pattern.Variable x) -> return (Some x)
                | _ ->
                    raise None Unexpected
                      "A variable name instead of a pattern was expected")
                >>= fun x ->
                let predefined_variables =
                  List.map snd (Name.Map.bindings typ_vars)
                in
                Type.of_typ_expr true typ_vars vb_expr.exp_type
                >>= fun (e_typ, typ_vars, new_typ_vars) ->
                let* e_typ = Type.decode_var_tags new_typ_vars false e_typ in
                let all_new_typ_vars = new_typ_vars in
                let new_typ_vars =
                  VarEnv.remove predefined_variables new_typ_vars
                in
                match x with
                | None -> return None
                | Some x ->
                    let* args_names, e_body =
                      if not is_axiom then
                        let translation = of_expression typ_vars vb_expr in
                        let translation =
                          match source_name with
                          | Some name ->
                              push_definition_path name translation
                          | None -> translation
                        in
                        let* e = translation in
                        let args_names, e_body = open_function e in
                        return (args_names, Some e_body)
                      else return ([], None)
                    in
                    let* args_typs, e_body_typ =
                      match
                        open_ocaml_arrow_type vb_expr.exp_env vb_expr.exp_type
                          (List.length args_names)
                      with
                      | Some (argument_types, result_type) ->
                          let translate_segment typ =
                            let* typ, _, _ =
                              Type.of_typ_expr true typ_vars typ
                            in
                            Type.decode_var_tags all_new_typ_vars false typ
                          in
                          let* argument_types =
                            Monad.List.map translate_segment argument_types
                          in
                          let* result_type =
                            translate_segment result_type
                          in
                          return
                            (argument_types, result_type)
                      | None ->
                          let* argument_types, result_type =
                            Type.open_type e_typ (List.length args_names)
                          in
                          return (argument_types, result_type)
                    in
                    let* configuration = get_configuration in
                    let partial_definitions =
                      Configuration.partial_definition_names configuration
                    in
                    let e_body =
                      match (recursion_strategy, e_body) with
                      | (Definition.WellFounded _ | Definition.Convergent _),
                        Some body ->
                          Some
                            (discharge_partial_sequence_calls
                               partial_definitions body)
                      | _, _ -> e_body
                    in
                    let e_body_typ =
                      match recursion_strategy with
                      | Definition.Partial _ ->
                          Type.partialize e_body_typ
                      | Definition.WellFounded _
                      | Definition.Convergent _ ->
                          e_body_typ
                      | Definition.Structural ->
                          if
                            Option.fold ~none:false
                              ~some:(fun body ->
                                has_partial_recursion body
                                || has_partial_reference
                                     partial_definitions body)
                              e_body
                          then Type.partialize e_body_typ
                          else e_body_typ
                    in
                    let structs, instance_args =
                      match recursion_strategy with
                      | Definition.WellFounded _ | Definition.Partial _ ->
                          ([], [])
                      | Definition.Structural | Definition.Convergent _ -> (
                          match (source_structs, is_rec) with
                          | [], true
                            when Configuration.is_without_guard_checking
                                   configuration ->
                              let guard =
                                Name.of_string_raw "_rocq_guard"
                              in
                              ( [ Name.to_string guard ],
                                [
                                  ( guard,
                                    Type.Apply
                                      ( MixedPath.of_name
                                          (Name.of_string_raw
                                             "GeneralRecursionGuard"),
                                        [] ) );
                                ] )
                          | _ -> (source_structs, []))
                    in
                    let* _ =
                      match recursion_strategy with
                      | Definition.WellFounded _ | Definition.Partial _ ->
                          return ()
                      | Definition.Structural | Definition.Convergent _ -> (
                          match structs with
                          | [] -> return ()
                          | _ :: _ -> use_unsafe_fixpoint)
                    in
                    let header =
                      {
                        Header.name = x;
                        typ_vars = new_typ_vars;
                        args = List.combine args_names args_typs;
                        instance_args;
                        structs;
                        typ = e_body_typ;
                        is_notation =
                          Attribute.has_mutual_as_notation attributes;
                      }
                    in
                    return (Some (header, e_body)) )))
  >>= fun cases ->
  let has_partial_result =
    cases
    |> List.exists (function
         | _, Some body ->
             has_partial_recursion body
             || has_partial_reference
                  (Configuration.partial_definition_names configuration)
                  body
         | _, None -> false)
  in
  let recursion_strategy =
    match (recursion_strategy, has_partial_result) with
    | Definition.Structural, true ->
        let definition_name =
          match cases_with_attributes with
          | (case, _) :: _ -> (
              match source_binding_name case.vb_pat with
              | Some name ->
                  String.concat "."
                    (enclosing_definition_path @ [ name ])
              | None -> "anonymous")
          | [] -> "anonymous"
        in
        let recursion =
          match recursion_strategy with
          | Definition.Structural when is_rec ->
              Definition.WellFoundedTerminates definition_name
          | Definition.Structural ->
              Definition.StructurallyTerminates
          | Definition.WellFounded _ | Definition.Partial _
          | Definition.Convergent _ ->
              assert false
        in
        Definition.Partial
          {
            definition_name;
            partial_definitions =
              Configuration.partial_definition_names configuration;
            recursion;
          }
    | strategy, _ -> strategy
  in
  let* term_environment = get_term_environment in
  return
    {
      Definition.is_rec;
      recursion_strategy;
      term_environment = List.map Name.of_string_raw term_environment;
      cases = cases @ destructuring_cases;
    }

and of_let (typ_vars : Name.t Name.Map.t) (is_rec : Asttypes.rec_flag)
    (cases : Typedtree.value_binding list) (e2 : t) : t Monad.t =
  match cases with
  | [
   { vb_pat = { pat_desc = Tpat_construct (_, { cstr_res; _ }, _, _); _ }; _ };
  ]
    when match Types.get_desc cstr_res with
         | Tconstr (path, _, _) -> PathName.is_unit path
         | _ -> false ->
      raise
        (ErrorMessage (e2, "top_level_evaluation"))
        SideEffect "Top-level evaluations are ignored"
  | _ -> (
      (match cases with
      | [ { vb_expr = { exp_desc; exp_type; _ }; _ } ]
        when match exp_desc with Texp_function _ -> false | _ -> true ->
          Type.of_typ_expr true typ_vars exp_type >>= fun (_, typ_vars', _) ->
          let typ_vars = List.map fst (Name.Map.bindings typ_vars) in
          let new_vars =
            List.fold_left
              (fun map var -> Name.Map.remove var map)
              typ_vars' typ_vars
          in
          return (not @@ Name.Map.is_empty new_vars)
      | _ -> return true)
      >>= fun is_function ->
      match cases with
      | [ { vb_pat = p; vb_expr = e1; vb_attributes; _ } ] when not is_function
        -> (
	          let* attributes = Attribute.of_attributes vb_attributes in
	          let has_tagged_match = Attribute.has_tagged_match attributes in
	          let* dep_match =
	            if has_tagged_match then
	              let* p_typ =
	                Type.of_type_expr_without_free_vars p.pat_type
	              in
	              let* e1_typ =
	                Type.of_type_expr_without_free_vars e1.exp_type
	              in
	              return
	                (Some { cast = p_typ; args = []; motive = e1_typ })
	            else return None
	          in
	          let* p = Pattern.of_pattern p in
	          let* e1 = of_expression typ_vars e1 in
	          match p with
          | Some (Pattern.Variable x) -> return (LetVar (None, x, [], e1, e2))
          | Some (Pattern.ModuleUnpack x) ->
              let unpack =
                Match
                  ( Variable (MixedPath.of_name x, []),
                    dep_match,
                    [ (Pattern.ModuleUnpack x, None, e2) ],
                    false )
              in
              return (LetVar (None, x, [], e1, unpack))
          | Some p ->
              let is_with_default_case =
                Attribute.has_match_with_default attributes
              in
              return
                (Match (e1, dep_match, [ (p, None, e2) ], is_with_default_case))
          | None -> return (Match (e1, dep_match, [], false)))
      | _ ->
          import_let_fun typ_vars false is_rec cases >>= fun def ->
          return (LetFun (def, e2)))

and of_module_expr ?expected_signature_path (typ_vars : Name.t Name.Map.t)
    (module_expr : Typedtree.module_expr)
    (module_type : Types.module_type option) : t Monad.t =
  let { mod_desc; mod_env; mod_loc; mod_type = local_module_type; _ } =
    module_expr
  in
  set_env mod_env
    (set_loc mod_loc
       (let* is_local_module_typ_first_class =
          let path =
            match mod_desc with Tmod_ident (path, _) -> Some path | _ -> None
          in
          IsFirstClassModule.is_module_typ_first_class local_module_type path
        in
        let* is_module_typ_first_class =
          match (expected_signature_path, module_type) with
          | Some signature_path, Some module_type ->
              return
                (Some (IsFirstClassModule.Found signature_path, module_type))
          | _, None -> return None
          | None, Some module_type ->
              let* is_first_class =
                IsFirstClassModule.is_module_typ_first_class module_type None
              in
              return (Some (is_first_class, module_type))
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
        let rec applied_functor_argument_count
            (module_expr : Typedtree.module_expr) : int =
          match module_expr.mod_desc with
          | Tmod_apply (functor_expr, _, _) ->
              1 + applied_functor_argument_count functor_expr
          | Tmod_constraint (functor_expr, _, _, _) ->
              applied_functor_argument_count functor_expr
          | Tmod_ident _
          | Tmod_apply_unit _
          | Tmod_structure _
          | Tmod_functor _
          | Tmod_unpack _
          | Tmod_typed_hole ->
              0
        in
        let rec applied_functor_arguments
            (module_expr : Typedtree.module_expr) :
            Typedtree.module_expr list =
          match module_expr.mod_desc with
          | Tmod_apply (functor_expr, argument, _) ->
              applied_functor_arguments functor_expr @ [ argument ]
          | Tmod_constraint (inner, _, _, _) ->
              applied_functor_arguments inner
          | Tmod_ident _
          | Tmod_apply_unit _
          | Tmod_structure _
          | Tmod_functor _
          | Tmod_unpack _
          | Tmod_typed_hole ->
              []
        in
        let expected_anonymous_signature (functor_expr : Typedtree.module_expr)
            (functor_type : Types.module_type) : Path.t option Monad.t =
          match (root_functor_path functor_expr, functor_type) with
          | ( Some functor_path,
              Mty_functor (Named (parameter_ident, parameter_type), _) ) ->
              let* env = get_env in
              let* hinted_parameter_signature =
                let parameter_index =
                  applied_functor_argument_count functor_expr
                in
                let* parameter_types =
                  get_functor_parameter_types functor_path
                in
                return
                  (Option.bind parameter_types (fun parameter_types ->
                       Option.bind
                         (List.nth_opt parameter_types parameter_index)
                         (fun parameter ->
                           SignatureHints.module_type_path
                             parameter.FunctorParameterHint.module_type)))
              in
              begin match Env.scrape_alias env parameter_type with
              | Mty_functor _ ->
                  (* A higher-order functor parameter is already represented as
                     a Gallina function.  It is not a record-valued anonymous
                     module that needs a synthesized signature and cast. *)
                  return None
              | _ ->
                  let* named_signature =
                    IsFirstClassModule.is_module_typ_first_class parameter_type
                      None
                  in
                  begin match named_signature with
                  | Found signature_path -> return (Some signature_path)
                  | Not_found _ ->
                      begin match hinted_parameter_signature with
                      | Some signature_path -> return (Some signature_path)
                      | None ->
                          let parameter_name =
                            Name.string_of_optional_ident parameter_ident
                          in
                          let* local_hint =
                            get_anonymous_functor_parameter functor_path
                              parameter_name
                          in
                          return local_hint
                      end
                  end
              end
          | _ -> return None
        in
        (* We consider casts to a first-class module of a different kind, either from
           another first-class module or from a plain module. *)
        let get_is_cast_needed module_type_path =
          match is_local_module_typ_first_class with
          | Found local_module_type_path ->
              (* Printed OCaml paths are not unique in the presence of nested
                 module-type shadowing.  A name-based comparison can therefore
                 confuse [Outer.S] with a later [Inner.S] and omit the
                 structural record conversion required at a functor call. *)
              return (not (Path.same local_module_type_path module_type_path))
          | _ -> return true
        in
        let cast_path ?source_signature_path path module_type
            module_type_path =
          let source_signature =
            match source_signature_path with
            | Some path -> IsFirstClassModule.Found path
            | None -> is_local_module_typ_first_class
          in
          let* values = ModuleTypValues.get typ_vars module_type in
          let* module_typ_params_arity =
            ModuleTypParams.get_module_typ_typ_params_arity module_type
          in
          let typ_param_of_path (associated_path : string list) :
              Type.t Monad.t =
            match source_signature with
            | Found local_module_type_path ->
                let* base =
                  PathName.of_path_with_convert false path
                in
                let* field_name =
                  Name.of_strings false associated_path
                in
                let* field =
                  PathName.of_path_and_name_with_convert
                    local_module_type_path field_name
                in
                return
                  (Type.Apply
                     (MixedPath.Access (base, [ field ]), []))
            | _ ->
                let associated_type_path =
                  List.fold_left
                    (fun path field -> Path.Pdot (path, field))
                    path associated_path
                in
                let* mixed_path =
                  MixedPath.of_path false associated_type_path
                in
                return (Type.Apply (mixed_path, []))
          in
          let mixed_path_of_value_or_typ (name : Name.t)
              (_ : Name.t list) : MixedPath.t Monad.t =
            match source_signature with
            | Found local_module_type_path ->
                let* base =
                  PathName.of_path_with_convert false path
                in
                let* field =
                  PathName.of_path_and_name_with_convert local_module_type_path
                    name
                in
                return (MixedPath.Access (base, [ field ]))
            | _ ->
                let* path_name =
                  PathName.of_path_and_name_with_convert path name
                in
                return (MixedPath.PathName path_name)
          in
          build_module ~typ_param_of_path module_typ_params_arity values
            module_type_path mixed_path_of_value_or_typ
        in
        let signature_path_of_module_type
            ?signature_hint (module_type : Types.module_type) :
            Path.t Monad.t =
          let* classification =
            IsFirstClassModule.is_module_typ_first_class module_type None
          in
          match classification with
          | IsFirstClassModule.Found signature_path ->
              return signature_path
          | IsFirstClassModule.Not_found reason -> (
              match signature_hint with
              | Some signature_path -> return signature_path
              | None ->
                  raise
                    (Path.Pident
                       (Ident.create_local
                          "module_coercion_signature_error"))
                    Unexpected
                    ("A module coercion requires a named Rocq signature.\n\n"
                   ^ reason))
        in
        let cast_module_expression
            ~(source_signature_path : Path.t)
            ~(target_signature_path : Path.t)
            (target_module_type : Types.module_type) (expression : t) :
            t Monad.t =
          if Path.same source_signature_path target_signature_path then
            return expression
          else
            let binding_ident =
              Ident.create_local "module_coercion"
            in
            let* binding_name = Name.of_ident false binding_ident in
            let* casted =
              cast_path
                ~source_signature_path
                (Path.Pident binding_ident)
                target_module_type target_signature_path
            in
            return
              (LetVar
                 (None, binding_name, [], expression, casted))
        in
        let qualify_typed_path
            (typed_type : FunctorParameterHint.t option)
            (path : Path.t) : Path.t =
          let aliases =
            match typed_type with
            | Some typed_type -> typed_type.FunctorParameterHint.path_aliases
            | None -> []
          in
          let rec qualify = function
            | Path.Pident ident as path ->
                aliases
                |> List.find_map (fun (candidate, target) ->
                       if Ident.same candidate ident then Some target
                       else None)
                |> Option.value ~default:path
            | Path.Pdot (prefix, field) ->
                Path.Pdot (qualify prefix, field)
            | Path.Papply (functor_path, argument_path) ->
                Path.Papply
                  (qualify functor_path, qualify argument_path)
            | Path.Pextra_ty (prefix, extra) ->
                Path.Pextra_ty (qualify prefix, extra)
          in
          qualify path
        in
        let rec coerce_functor_expression
            (source_functor_path : Path.t option)
            (source_result_signature : Path.t option)
            (target_typed_type : FunctorParameterHint.t option)
            (target_path_substitution : Subst.t)
            (expression : t) (source_type : Types.module_type)
            (target_type : Types.module_type) : t Monad.t =
          let* env = get_env in
          match
            ( Env.scrape_alias env source_type,
              Env.scrape_alias env target_type )
          with
          | ( Mty_functor
                (Named (source_ident, source_parameter), source_result),
              Mty_functor
                (Named (target_ident, target_parameter), target_result) ) ->
              let target_typed_parameter, target_typed_result =
                match target_typed_type with
                | Some
                    {
                      FunctorParameterHint.module_type =
                        {
                          mty_desc =
                            Tmty_functor
                              ( Named (_, _, parameter),
                                result );
                          _;
                        };
                      path_aliases;
                      _;
                    } ->
                    ( Some
                        {
                          FunctorParameterHint.ident = None;
                          module_type = parameter;
                          path_aliases;
                        },
                      Some
                        {
                          FunctorParameterHint.ident = None;
                          module_type = result;
                          path_aliases;
                        } )
                | Some _ | None -> (None, None)
              in
              let target_ident =
                Option.value target_ident
                  ~default:(Ident.create_local "FunctorParameter")
              in
              let* target_name = Name.of_ident false target_ident in
              let* source_parameter_signature =
                let* signature_hint =
                  match source_functor_path with
                  | Some functor_path ->
                      let parameter_name =
                        Name.string_of_optional_ident source_ident
                      in
                      get_anonymous_functor_parameter functor_path
                        parameter_name
                  | None -> return None
                in
                signature_path_of_module_type
                  ?signature_hint source_parameter
              in
              let* target_parameter_signature =
                let typed_hint =
                  Option.bind target_typed_parameter
                    (fun parameter ->
                      ModuleTyp.get_module_typ_path_name
                        parameter.FunctorParameterHint.module_type)
                  |> Option.map
                       (Subst.module_path target_path_substitution)
                  |> Option.map
                       (qualify_typed_path target_typed_parameter)
                in
                signature_path_of_module_type
                  ?signature_hint:typed_hint
                  target_parameter
              in
              let* target_parameter_module_type =
                ModuleTyp.of_types
                  ~result_signature_path:target_parameter_signature
                  target_parameter
              in
              let* _, target_parameter_type =
                ModuleTyp.to_typ [] (Ident.name target_ident) false
                  target_parameter_module_type
              in
              let target_parameter_expression =
                Variable (MixedPath.of_name target_name, [])
              in
              let* source_argument =
                cast_module_expression
                  ~source_signature_path:target_parameter_signature
                  ~target_signature_path:source_parameter_signature
                  source_parameter target_parameter_expression
              in
              let application =
                Apply (expression, [ Some source_argument ])
              in
              let source_result =
                match source_ident with
                | Some source_ident ->
                    Subst.modtype Subst.Keep
                      (Subst.add_module source_ident
                         (Path.Pident target_ident)
                         Subst.identity)
                      source_result
                | None -> source_result
              in
              let result_env =
                Env.add_module ~arg:true target_ident Types.Mp_present
                  target_parameter env
              in
              let* body =
                set_env result_env
                  (set_signature_hint
                     (Path.Pident target_ident)
                     target_parameter_signature
                     (coerce_functor_expression source_functor_path
                        source_result_signature target_typed_result
                        target_path_substitution application source_result
                        target_result))
              in
              return
                (Functor
                   (target_name, target_parameter_type, body))
          | Mty_functor _, _
          | _, Mty_functor _ ->
              raise
                (Error "module_coercion_functor_shape")
                Unexpected
                "A module coercion cannot convert a functor to a non-functor."
          | _ ->
              let* source_signature_path =
                signature_path_of_module_type
                  ?signature_hint:source_result_signature source_type
              in
              let* target_signature_path =
                signature_path_of_module_type
                  ?signature_hint:
                    (Option.bind target_typed_type
                       (fun parameter ->
                         ModuleTyp.get_module_typ_path_name
                           parameter.FunctorParameterHint.module_type))
                  target_type
              in
              let target_signature_path =
                Subst.module_path target_path_substitution
                  target_signature_path
                |> qualify_typed_path target_typed_type
              in
              cast_module_expression ~source_signature_path
                ~target_signature_path target_type expression
        in
        let apply_mod e1 e2 argument_coercion =
          let e1_mod_type = e1.mod_type in
          let expected_module_typ_for_e2 =
            match e1_mod_type with
            | Mty_functor (Named (_, module_typ_arg), _) ->
              Some module_typ_arg
            | _ -> None
          in
          let* expected_signature_path_for_e2 =
            expected_anonymous_signature e1 e1_mod_type
          in
          let* expected_typed_module_type_for_e2 =
            match root_functor_path e1 with
            | Some functor_path ->
                let parameter_index =
                  applied_functor_argument_count e1
                in
                let* parameter_types =
                  get_functor_parameter_types functor_path
                in
                return
                  (Option.bind parameter_types (fun parameter_types ->
                       List.nth_opt parameter_types parameter_index))
            | None -> return None
          in
          let* expected_typed_module_path_substitution =
            match root_functor_path e1 with
            | Some functor_path ->
                let* parameter_types =
                  get_functor_parameter_types functor_path
                in
                let rec add_arguments substitution parameters arguments =
                  match (parameters, arguments) with
                  | parameter :: parameters, argument :: arguments ->
                      let substitution =
                        match
                          ( parameter.FunctorParameterHint.ident,
                            root_functor_path argument )
                        with
                        | Some ident, Some argument_path ->
                            Subst.add_module ident argument_path
                              substitution
                        | None, _ | _, None -> substitution
                      in
                      add_arguments substitution parameters arguments
                  | [], _ | _, [] -> substitution
                in
                return
                  (add_arguments Subst.identity
                     (Option.value parameter_types ~default:[])
                     (applied_functor_arguments e1))
            | None -> return Subst.identity
          in
          let* e1 = of_module_expr typ_vars e1 None in
          let* es =
            match e1_mod_type with
            | Mty_functor (Unit, _) -> return []
            | _ ->
              match e2 with
              | None ->
                raise [] Unexpected
                  ("Tmod_apply_unit was used with a non-generative functor")
              | Some e2 ->
                let* e2 =
                  match
                    (argument_coercion, expected_module_typ_for_e2)
                  with
                  | ( Tcoerce_functor _,
                      Some expected_module_type ) ->
                      let source_functor_path =
                        root_functor_path e2
                      in
                      let* source_result_signature =
                        match source_functor_path with
                        | Some functor_path ->
                            get_functor_result_signature functor_path
                        | None -> return None
                      in
                      let* expression =
                        of_module_expr typ_vars e2 None
                      in
                      coerce_functor_expression source_functor_path
                        source_result_signature
                        expected_typed_module_type_for_e2
                        expected_typed_module_path_substitution expression
                        e2.mod_type expected_module_type
                  | _ ->
                      of_module_expr
                        ?expected_signature_path:
                          expected_signature_path_for_e2
                        typ_vars e2 expected_module_typ_for_e2
                in
                return [ Some (annotate_terminal_module e2) ]
          in
          let application = Apply (e1, es) in
          match is_module_typ_first_class with
          | Some (Found module_type_path, module_type) ->
            let* is_cast_needed = get_is_cast_needed module_type_path in
            if not is_cast_needed then return application
            else
              let ident = Ident.create_local "functor_result" in
              let* name = Name.of_ident false ident in
              let path = Path.Pident ident in
              let* casted_result =
                cast_path path module_type module_type_path
              in
              return (LetVar (None, name, [], application, casted_result))
          | _ -> return application
        in
        match mod_desc with
        | Tmod_ident (path, _) -> (
            let* applied_child =
              get_applied_functor_child path
            in
            let* mixed_path =
              match applied_child with
              | None -> MixedPath.of_path false path
              | Some (target, parent_application) ->
                  let* target =
                    PathName.of_path_with_convert false target
                  in
                  let* parent =
                    PathName.of_path_with_convert false parent_application
                  in
                  let parent_fargs =
                    PathName.to_string
                      {
                        parent with
                        PathName.base =
                          Name.of_string_raw
                            (Name.to_string parent.base ^ "_fargs");
                      }
                  in
                  return
                    (MixedPath.AppliedAccess
                       ( target,
                         [ ("_fargs", parent_fargs) ],
                         [] ))
            in
            let default_result = return (Variable (mixed_path, [])) in
            match is_module_typ_first_class with
            | Some (Found module_type_path, module_type) ->
                let* is_cast_needed = get_is_cast_needed module_type_path in
                if not is_cast_needed then default_result
                else cast_path path module_type module_type_path
            | _ -> default_result)
        | Tmod_structure structure -> (
            match is_module_typ_first_class with
            | Some (Found signature_path, module_type) ->
                of_structure typ_vars signature_path module_type
                  structure.str_items structure.str_final_env
            | Some (IsFirstClassModule.Not_found reason, _) ->
                error_message
                  (Error "first_class_module_value_of_unknown_signature") Module
                  ("The signature name of this module could not be found\n\n"
                 ^ reason)
            | None ->
                error_message (Error "no_expected_module_type_found") Unexpected
                  ("No module type was found for this structure.\n"
                 ^ "Try to add a module type annotation."))
        | Tmod_functor (parameter, e) -> (
            match parameter with
            | Named (ident, _, module_typ_arg) ->
                let* signature =
                  IsFirstClassModule.is_module_typ_first_class
                    module_typ_arg.mty_type None
                in
                let body = of_module_expr typ_vars e None in
                let* e =
                  match (ident, signature) with
                  | Some ident, IsFirstClassModule.Found signature_path ->
                      set_signature_hint (Path.Pident ident) signature_path body
                  | _ -> body
                in
                let* x = Name.of_optional_ident false ident in
                let id = Name.string_of_optional_ident ident in
                let* module_typ_arg = ModuleTyp.of_ocaml module_typ_arg in
                let* _, module_typ_arg =
                  ModuleTyp.to_typ [] id false module_typ_arg
                in
                return (Functor (x, module_typ_arg, e))
            | Unit -> of_module_expr typ_vars e None)
        | Tmod_apply (e1, e2, coercion) ->
            apply_mod e1 (Some e2) coercion
        | Tmod_apply_unit e1 ->
            apply_mod e1 None Tcoerce_none
        | Tmod_constraint (module_expr, mod_type, _, _) ->
            let module_type =
              match module_type with
              | Some _ -> module_type
              | None -> Some mod_type
            in
            of_module_expr ?expected_signature_path typ_vars module_expr
              module_type
        | Tmod_unpack (e, _) ->
            of_expression typ_vars e >>= fun e ->
            raise e Module
              ("We do not support unpacking of first-class module outside of "
             ^ "expressions.\n\n"
             ^ "This is to prevent universe inconsistencies in Rocq. A module \
                can " ^ "become first-class but not the other way around.")
        | Tmod_typed_hole ->
            raise (Error "module_hole") Unexpected "Unexpected module hole."))

and of_structure (typ_vars : Name.t Name.Map.t) (signature_path : Path.t)
    (module_type : Types.module_type) (items : Typedtree.structure_item list)
    (final_env : Env.t) : t Monad.t =
  match items with
  | [] ->
      set_env final_env
        ( ModuleTypParams.get_module_typ_typ_params_arity module_type
        >>= fun module_typ_params_arity ->
          let* values = ModuleTypValues.get typ_vars module_type in
          let mixed_path_of_value_or_typ (_ : Name.t)
              (access : Name.t list) : MixedPath.t Monad.t =
            match List.rev access with
            | [] ->
                raise
                  (MixedPath.of_name (Name.of_string_raw "missing_access"))
                  Unexpected "A module field has an empty local access path"
            | base :: rev_path ->
                return
                  (MixedPath.PathName
                     (PathName.of_name (List.rev rev_path) base))
          in
          build_module module_typ_params_arity values signature_path
            mixed_path_of_value_or_typ )
  | item :: items ->
      set_env item.str_env
        (set_loc item.str_loc
           ( of_structure typ_vars signature_path module_type items final_env
           >>= fun e_next ->
             match item.str_desc with
             | Tstr_eval _ ->
                 raise
                   (ErrorMessage (e_next, "top_level_evaluation"))
                   SideEffect "Top-level evaluations are ignored"
             | Tstr_value (rec_flag, cases) ->
                 push_env (of_let typ_vars rec_flag cases e_next)
             | Tstr_primitive _ ->
                 raise
                   (ErrorMessage (e_next, "primitive"))
                   NotSupported "Primitive not handled"
             | Tstr_type (_, typs) -> (
                 match typs with
                 | [ typ ] -> (
                     match typ with
                     | {
                      typ_id;
                      typ_type =
                        {
                          type_kind = Type_abstract _;
                          type_manifest = Some typ;
                          type_params;
                          _;
                        };
                      _;
                     } ->
                         let* name = Name.of_ident false typ_id in
                         type_params
                         |> Monad.List.map Type.of_type_expr_variable
                         >>= fun typ_args ->
                         Type.of_type_expr_without_free_vars typ >>= fun typ ->
                         return (LetTyp (name, typ_args, typ, e_next))
                     | _ ->
                         raise
                           (ErrorMessage (e_next, "typ_definition"))
                           NotSupported
                           ("We only handle type synonyms here." ^ "\n\n"
                          ^ "Indeed, we compile this module as a dependent \
                             record for " ^ "the signature:\n"
                          ^ Path.name signature_path ^ "\n\n"
                          ^ "Thus we cannot introduce new type definitions. \
                             Use a "
                          ^ "separated module for the type definition and\n\
                             its use."))
                 | _ ->
                     raise
                       (ErrorMessage (e_next, "mutual_typ_definition"))
                       NotSupported
                       "Mutually recursive type definition not handled here")
             | Tstr_typext _ -> return e_next
             | Tstr_exception _ -> return e_next
             | Tstr_module { mb_id = Some ident; _ }
               when Ident.name ident = "Internal_for_tests" ->
                 return e_next
             | Tstr_module { mb_id; mb_expr; _ } ->
                 let* name = Name.of_optional_ident false mb_id in
                 of_module_expr typ_vars mb_expr (Some mb_expr.mod_type)
                 >>= fun value ->
                 return (LetVar (None, name, [], value, e_next))
             | Tstr_recmodule _ ->
                 raise
                   (ErrorMessage (e_next, "recursive_module"))
                   NotSupported "Recursive modules not handled"
             | Tstr_modtype _ ->
                 raise
                   (ErrorMessage (e_next, "module_type"))
                   NotSupported
                   "Module type not handled in module with a named signature"
             | Tstr_open _ ->
                 raise
                   (ErrorMessage (e_next, "open"))
                   NotSupported
                   "Open not handled in module with a named signature"
             | Tstr_class _ ->
                 raise
                   (ErrorMessage (e_next, "class"))
                   NotSupported "Class not handled"
             | Tstr_class_type _ ->
                 raise
                   (ErrorMessage (e_next, "class_type"))
                   NotSupported "Class type not handled"
             | Tstr_include { incl_mod; incl_type; _ } -> (
                 let path =
                   match incl_mod.mod_desc with
                   | Tmod_ident (path, _)
                   | Tmod_constraint
                       ({ mod_desc = Tmod_ident (path, _); _ }, _, _, _) ->
                       Some path
                   | _ -> None
                 in
                 let* included_record_alias =
                   match path with
                   | Some (Path.Pident ident) ->
                       get_included_record_alias ident
                   | Some _ ->
                       return None
                   | None -> return None
                 in
                 match included_record_alias with
                 | Some alias ->
                     of_include_record_alias typ_vars alias incl_type e_next
                 | None ->
                     let incl_module_type = Types.Mty_signature incl_type in
                     let* is_first_class =
                       IsFirstClassModule.is_module_typ_first_class
                         incl_module_type path
                     in
                     (match is_first_class with
                     | Found incl_signature_path -> (
                         match path with
                         | Some path ->
                             let* path_name =
                               PathName.of_path_with_convert false path
                             in
                             of_include typ_vars path_name incl_signature_path
                               incl_type e_next
                         | None ->
                             let* name = get_include_name incl_mod in
                             let path_name = PathName.of_name [] name in
                             let* included_module =
                               of_module_expr typ_vars incl_mod
                                 (Some incl_module_type)
                             in
                             let* e_next =
                               of_include typ_vars path_name incl_signature_path
                                 incl_type e_next
                             in
                             return
                               (LetVar
                                  (None, name, [], included_module, e_next)))
                     | Not_found reason ->
                         raise
                           (ErrorMessage
                              (e_next, "include_without_named_signature"))
                           NotSupported
                           ("We did not find a signature name for the include \
                             of this module\n\n" ^ reason)))
             | Tstr_attribute _ -> return e_next ))

and of_include (typ_vars : Name.t Name.Map.t) (module_path_name : PathName.t)
    (signature_path : Path.t) (signature : Types.signature) (e_next : t) :
    t Monad.t =
  match signature with
  | [] -> return e_next
  | signature_item :: signature -> (
      of_include typ_vars module_path_name signature_path signature e_next
      >>= fun e_next ->
      match signature_item with
      | Sig_value (ident, _, _) | Sig_type (ident, _, _, _) ->
          let is_value =
            match signature_item with Sig_value _ -> true | _ -> false
          in
          (match signature_item with
          | Sig_value (_, { Types.val_type; _ }, _) ->
              Type.of_typ_expr true typ_vars val_type
              >>= fun (_, _, new_typ_vars) -> return (List.map fst new_typ_vars)
          | _ -> return [])
          >>= fun typ_vars ->
          let* name = Name.of_ident is_value ident in
          PathName.of_path_and_name_with_convert signature_path name
          >>= fun signature_path_name ->
          let implicits =
            typ_vars
            |> List.map (fun name ->
                   let name = Name.to_string name in
                   (name, name))
          in
          return
            (LetVar
               ( None,
                 name,
                 typ_vars,
                 Variable
                   ( MixedPath.Access (module_path_name, [ signature_path_name ]),
                     implicits ),
                 e_next ))
      | Sig_typext _ | Sig_module _ | Sig_modtype _ | Sig_class _
      | Sig_class_type _ ->
          return e_next)

and of_include_record_alias (typ_vars : Name.t Name.Map.t)
    (alias : IncludedRecordAliasTarget.t) (signature : Types.signature)
    (e_next : t) : t Monad.t =
  match signature with
  | [] -> return e_next
  | signature_item :: signature -> (
      of_include_record_alias typ_vars alias signature e_next
      >>= fun e_next ->
      match signature_item with
      | Sig_value (ident, _, _) | Sig_type (ident, _, _, _) ->
          let is_value =
            match signature_item with Sig_value _ -> true | _ -> false
          in
          (match signature_item with
          | Sig_value (_, { Types.val_type; _ }, _) ->
              Type.of_typ_expr true typ_vars val_type
              >>= fun (_, _, new_typ_vars) ->
              return (List.map fst new_typ_vars)
          | _ -> return [])
          >>= fun polymorphic_variables ->
          let* name = Name.of_ident is_value ident in
          let implicits =
            polymorphic_variables
            |> List.map (fun name ->
                   let name = Name.to_string name in
                   (name, name))
          in
          let* access =
            MixedPath.of_included_record_alias is_value alias
              [ Ident.name ident ]
          in
          return
            (LetVar
               ( None,
                 name,
                 polymorphic_variables,
                 Variable (access, implicits),
                 e_next ))
      | Sig_typext _ | Sig_module _ | Sig_modtype _ | Sig_class _
      | Sig_class_type _ ->
          return e_next)

let rec flatten_list (e : t) : t list option =
  match e with
  | Constructor (x, _, es) -> (
      match (x, es) with
      | { PathName.path = []; base = Name.Make "[]" }, [] -> Some []
      | { PathName.path = []; base = Name.Make "cons" }, [ e; es ] -> (
          match flatten_list es with Some es -> Some (e :: es) | None -> None)
      | _ -> None)
  | _ -> None

let to_coq_let_symbol (let_symbol : string option) : SmartPrint.t =
  match let_symbol with None -> !^"let" | Some let_symbol -> !^let_symbol

let runtime_value ?monad (module_name : string) (value_name : string) : t =
  let implicits =
    match monad with
    | None -> []
    | Some monad ->
        [
          ( "M",
            SmartPrint.to_string 1_000_000 0
              (Type.to_coq None None monad) );
        ]
  in
  Variable
    ( MixedPath.PathName
        {
          PathName.path =
            [
              Name.of_string_raw "RocqOfOCaml";
              Name.of_string_raw "Partial";
              Name.of_string_raw module_name;
            ];
          base = Name.of_string_raw value_name;
        },
      implicits )

let apply_runtime ?monad (module_name : string) (value_name : string)
    (arguments : t list) : t =
  Apply
    ( runtime_value ?monad module_name value_name,
      List.map (fun argument -> Some argument) arguments )

let expression_function_name (e : t) : string option =
  expression_qualified_name e

let final_path_component (path : string) : string =
  match List.rev (String.split_on_char '.' path) with
  | component :: _ -> component
  | [] -> path

let definition_final_component (definition : string) : string =
  final_path_component definition

let function_name_matches (candidate : string) (expected : string) : bool =
  let candidate = drop_closing_parentheses candidate in
  let expected_components = String.split_on_char '.' expected in
  let flattened_suffix =
    match List.rev expected_components with
    | value :: module_ :: _ -> module_ ^ "_" ^ value
    | _ -> expected
  in
  candidate = expected
  || string_ends_with candidate ("." ^ expected)
  || final_path_component candidate = definition_final_component expected
  || string_ends_with candidate ("." ^ flattened_suffix)
  || string_ends_with candidate ("_" ^ flattened_suffix)
  || final_path_component candidate = flattened_suffix

let rewrite_local_well_founded_calls (recursive_name : Name.t)
    (recurse_name : Name.t) (argument_count : int) (e : t) : t =
  let map_option f = Option.map f in
  let rec flatten_application function_ arguments =
    match function_ with
    | Apply (inner, preceding)
    | SourceApply (inner, preceding, _)
      when
        List.for_all
          (function None -> false | Some _ -> true)
          preceding ->
        flatten_application inner (preceding @ arguments)
    | _ -> (function_, arguments)
  in
  let rec rewrite e =
    match e with
    | Constant _ | Variable _ | Error _ | ErrorTyp _ | Ltac _ -> e
    | Tuple values -> Tuple (List.map rewrite values)
    | Constructor (name, implicits, values) ->
        Constructor (name, implicits, List.map rewrite values)
    | ConstructorExtensible (tag, typ, value) ->
        ConstructorExtensible (tag, typ, rewrite value)
    | ConstructorVariant (tag, value) ->
        ConstructorVariant
          (tag, Option.map (fun (typ, value) -> (typ, rewrite value)) value)
    | Apply (function_, arguments) ->
        rewrite_application None function_ arguments
    | SourceApply (function_, arguments, result_typ) ->
        rewrite_application (Some result_typ) function_ arguments
    | Return (operator, value) -> Return (operator, rewrite value)
    | InfixOperator (operator, left, right) ->
        InfixOperator (operator, rewrite left, rewrite right)
    | Function (name, typ, body) -> Function (name, typ, rewrite body)
    | Functions (names, body) -> Functions (names, rewrite body)
    | LetVar (operator, name, parameters, value, body) ->
        LetVar
          (operator, name, parameters, rewrite value, rewrite body)
    | LetFun (definition, body) ->
        let cases =
          definition.Definition.cases
          |> List.map (fun (header, body) ->
                 (header, Option.map rewrite body))
        in
        LetFun ({ definition with Definition.cases }, rewrite body)
    | LetTyp (name, parameters, typ, body) ->
        LetTyp (name, parameters, typ, rewrite body)
    | LetModuleUnpack (name, path, body) ->
        LetModuleUnpack (name, path, rewrite body)
    | Match (scrutinee, dependent, cases, default) ->
        Match
          ( rewrite scrutinee,
            dependent,
            List.map
              (fun (pattern, cast, body) ->
                (pattern, cast, rewrite body))
              cases,
            default )
    | MatchExtensible (scrutinee, typ, cases) ->
        MatchExtensible
          ( rewrite scrutinee,
            typ,
            List.map
              (fun (pattern, body) -> (pattern, rewrite body))
              cases )
    | MatchVariant (scrutinee, typ, cases) ->
        MatchVariant
          ( rewrite scrutinee,
            typ,
            List.map
              (fun (pattern, body) -> (pattern, rewrite body))
              cases )
    | Record fields ->
        Record
          (List.map
             (fun (name, arity, value) -> (name, arity, rewrite value))
             fields)
    | Field (value, name) -> Field (rewrite value, name)
    | IfThenElse (condition, then_, else_) ->
        IfThenElse (rewrite condition, rewrite then_, rewrite else_)
    | Module (typ, fields) ->
        Module
          ( typ,
            List.map
              (fun (name, arity, value) -> (name, arity, rewrite value))
              fields )
    | ModulePack (arity, value) -> ModulePack (arity, rewrite value)
    | Functor (name, typ, body) -> Functor (name, typ, rewrite body)
    | Cast (value, typ) -> Cast (rewrite value, typ)
    | TypAnnotation (value, typ) -> TypAnnotation (rewrite value, typ)
    | Assert (typ, condition) -> Assert (typ, rewrite condition)
    | Assumption (kind, typ, arguments) ->
        Assumption (kind, typ, List.map rewrite arguments)
    | RequiresAssumption (kind, typ, body) ->
        RequiresAssumption (kind, typ, rewrite body)
    | ErrorArray values -> ErrorArray (List.map rewrite values)
    | ErrorMessage (body, message) ->
        ErrorMessage (rewrite body, message)
  and rewrite_application result_typ function_ arguments =
    let function_, arguments =
      flatten_application function_ arguments
    in
    let is_recursive_call =
      match expression_function_name function_ with
      | Some candidate ->
          function_name_matches candidate (Name.to_string recursive_name)
      | None -> false
    in
    let supplied_arguments =
      List.filter_map (fun argument -> argument) arguments
    in
    if
      is_recursive_call
      && List.length supplied_arguments = argument_count
      && List.length arguments = argument_count
    then
      let state =
        match supplied_arguments with
        | [] -> Tuple []
        | [ value ] -> rewrite value
        | values -> Tuple (List.map rewrite values)
      in
      Apply
        ( Variable (MixedPath.of_name recurse_name, []),
          [
            Some state;
            Some
              (Variable
                 (MixedPath.of_name (Name.of_string_raw "_"), []));
          ] )
    else
      let function_ = rewrite function_ in
      let arguments = List.map (map_option rewrite) arguments in
      match result_typ with
      | None -> Apply (function_, arguments)
      | Some result_typ ->
          SourceApply (function_, arguments, result_typ)
  in
  rewrite e

let is_named_expression (names : string list) (e : t) : bool =
  match expression_function_name e with
  | Some candidate ->
      List.exists (function_name_matches candidate) names
  | None -> false

let is_named_application (names : string list) (e : t) : bool =
  match e with
  | Apply (function_, _) | SourceApply (function_, _, _) -> (
      match expression_function_name function_ with
      | Some candidate ->
          List.exists (function_name_matches candidate) names
      | None -> false)
  | _ -> false

let partial_wrapper_is_resumption (typ : Type.t) : bool =
  match Type.arrow_result typ with
  | Type.Apply (path, _) ->
      let path = MixedPath.to_string path in
      path = "RocqOfOCaml.Partial.Resumption.t"
      || string_ends_with path ".Partial.Resumption.t"
  | _ -> false

let partial_wrapper_monad (typ : Type.t) : Type.t option =
  match Type.arrow_result typ with
  | Type.Apply
      ( path,
        [ (monad, _); _ ] )
    when
      let path = MixedPath.to_string path in
      path = "RocqOfOCaml.Partial.Resumption.t"
      || string_ends_with path ".Partial.Resumption.t" ->
      Some monad
  | _ -> None

(** Lift one source expression into the explicit partial-computation syntax.
    Recursive calls and calls to other configured partial definitions already
    have the lifted type. Pure branches become [Done]. In a monadic partial
    computation, ordinary source-monad actions become [Bind] nodes, while a
    lifted recursive/partial action composes with [Resumption.bind]. *)
let rec lift_partial_expression ~(resumption : bool)
    ~(monad : Type.t option)
    ~(recursive_names : string list) ~(partial_definitions : string list)
    (e : t) : t =
  let rec flatten_application e =
    match e with
    | Apply (function_, arguments)
    | SourceApply (function_, arguments, _)
      when
        List.for_all (function None -> false | Some _ -> true) arguments ->
        let function_, preceding_arguments =
          match flatten_application function_ with
          | Apply (function_, preceding_arguments) ->
              (function_, preceding_arguments)
          | function_ -> (function_, [])
        in
        Apply (function_, preceding_arguments @ arguments)
    | _ -> e
  in
  let e = flatten_application e in
  let recurse =
    lift_partial_expression ~resumption ~monad ~recursive_names
      ~partial_definitions
  in
  let is_partial e =
    is_named_application (recursive_names @ partial_definitions) e
  in
  let contains_partial e =
    is_partial e
    || has_partial_recursion e
    || has_partial_reference partial_definitions e
  in
  let done_ value =
    apply_runtime ?monad:(if resumption then monad else None)
      (if resumption then "Resumption" else "Delay")
      "Done" [ value ]
  in
  let bind computation continuation =
    apply_runtime ?monad "Resumption" "Compose"
      [ computation; continuation ]
  in
  let action action continuation =
    apply_runtime ?monad "Resumption" "Bind" [ action; continuation ]
  in
  let suspend computation =
    let thunk = Function (Name.of_string_raw "_", None, computation) in
    apply_runtime ?monad:(if resumption then monad else None)
      (if resumption then "Resumption" else "Delay")
      "Tau" [ thunk ]
  in
  let continuation name typ body =
    Function (name, typ, recurse body)
  in
  let runtime_sequence_value value_name =
    Variable
      ( MixedPath.PathName
          {
            PathName.path =
              [
                Name.of_string_raw "RocqOfOCaml";
                Name.of_string_raw "OCamlSeq";
              ];
            base = Name.of_string_raw value_name;
          },
        [] )
  in
  let is_configured_seq_map function_ =
    match expression_function_name function_ with
    | None -> false
    | Some candidate ->
        partial_definitions
        |> List.exists (fun definition ->
               configured_partial_path_matches definition "Seq.mapM"
               && configured_partial_path_matches candidate definition)
  in
  let lift_callback callback =
    match callback with
    | Function (name, typ, body) ->
        Function (name, typ, recurse body)
    | _ ->
        let value = Name.of_string_raw "_rocq_partial_argument" in
        Function
          ( value,
            None,
            recurse
              (Apply
                 ( callback,
                   [ Some (Variable (MixedPath.of_name value, [])) ] )) )
  in
  let lift_seq_map function_ arguments =
    match arguments with
    | [ Some callback; Some sequence ]
      when resumption && is_configured_seq_map function_ ->
        Some
          (apply_runtime ?monad "Resumption" "traverse"
             [
               runtime_sequence_value "uncons";
               runtime_sequence_value "empty";
               runtime_sequence_value "cons";
               lift_callback callback;
               sequence;
             ])
    | _ -> None
  in
  let lifted_seq_map =
    match e with
    | Apply (function_, arguments)
    | SourceApply (function_, arguments, _) ->
        lift_seq_map function_ arguments
    | _ -> None
  in
  match lifted_seq_map with
  | Some e -> e
  | None when is_named_application recursive_names e -> suspend e
  | None when is_partial e -> e
  | None ->
    match e with
    | Match (scrutinee, dependent, cases, default) ->
        Match
          ( scrutinee,
            dependent,
            List.map
              (fun (pattern, cast, body) -> (pattern, cast, recurse body))
              cases,
            default )
    | MatchExtensible (scrutinee, typ, cases) ->
        MatchExtensible
          ( scrutinee,
            typ,
            List.map
              (fun (pattern, body) -> (pattern, recurse body))
              cases )
    | MatchVariant (scrutinee, typ, cases) ->
        MatchVariant
          ( scrutinee,
            typ,
            List.map
              (fun (pattern, body) -> (pattern, recurse body))
              cases )
    | IfThenElse (condition, then_, else_) ->
        IfThenElse (condition, recurse then_, recurse else_)
    | LetVar (None, name, parameters, value, body) ->
        LetVar (None, name, parameters, value, recurse body)
    | LetFun (definition, body)
      when
        match definition.Definition.recursion_strategy with
        | Definition.Partial _ -> true
        | Definition.Structural | Definition.WellFounded _
        | Definition.Convergent _ ->
            false ->
        let local_partial_names =
          definition.Definition.cases
          |> List.map (fun (header, _) ->
                 Name.to_string header.Header.name)
        in
        LetFun
          ( definition,
            lift_partial_expression ~resumption ~monad
              ~recursive_names
              ~partial_definitions:
                (local_partial_names @ partial_definitions)
              body )
    | LetFun (definition, body)
      when
        has_partial_recursion body
        || has_partial_reference partial_definitions body ->
        LetFun (definition, recurse body)
    | LetVar (Some _, name, [], value, body) when resumption ->
        let continuation = continuation name None body in
        if contains_partial value then bind (recurse value) continuation
        else action value continuation
    | Apply
        ( function_,
          [ Some value; Some (Function (name, typ, body)) ] )
    | SourceApply
        ( function_,
          [ Some value; Some (Function (name, typ, body)) ],
          _ )
      when
        resumption
        &&
        match expression_function_name function_ with
        | Some name ->
            function_name_matches name "op_letdollar"
            || function_name_matches name "op_gtgteq"
            || function_name_matches name "bind"
        | None -> false ->
        let continuation = continuation name typ body in
        if contains_partial value then bind (recurse value) continuation
        else action value continuation
    | Apply (function_, [ Some value; Some continuation_function ])
    | SourceApply
        (function_, [ Some value; Some continuation_function ], _)
      when
        resumption
        &&
        match expression_function_name function_ with
        | Some name ->
            function_name_matches name "op_letdollar"
            || function_name_matches name "op_gtgteq"
            || function_name_matches name "bind"
        | None -> false ->
        let value_name = Name.of_string_raw "_rocq_partial_bound" in
        let continuation =
          Function
            ( value_name,
              None,
              recurse
                (Apply
                   ( continuation_function,
                     [
                       Some
                         (Variable
                            (MixedPath.of_name value_name, []));
                     ] )) )
        in
        if contains_partial value then bind (recurse value) continuation
        else action value continuation
    | Apply (function_, [ Some mapper; Some computation ])
    | SourceApply (function_, [ Some mapper; Some computation ], _)
      when
        resumption
        && (has_partial_recursion computation
           || has_partial_reference partial_definitions computation)
        &&
        match expression_function_name function_ with
        | Some name -> function_name_matches name "fmap"
        | None -> false ->
        let value_name = Name.of_string_raw "_rocq_partial_mapped" in
        bind (recurse computation)
          (Function
             ( value_name,
               None,
               done_
                 (Apply
                    ( mapper,
                      [
                        Some
                          (Variable
                             (MixedPath.of_name value_name, []));
                      ] )) ))
    | Return (_, value) -> done_ value
    | Apply (function_, [ Some value ])
    | SourceApply (function_, [ Some value ], _)
      when
        match expression_function_name function_ with
        | Some name -> function_name_matches name "return"
        | None -> false ->
        done_ value
    | ErrorMessage (body, message) ->
        ErrorMessage (recurse body, message)
    | TypAnnotation (body, typ) ->
        TypAnnotation (recurse body, Type.partialize typ)
    | _ when resumption ->
        let result = Name.of_string_raw "_rocq_partial_value" in
        action e (Function (result, None, done_ (Variable (MixedPath.of_name result, []))))
    | _ -> done_ e

let guard_partial_body (resumption : bool) (monad : Type.t option)
    (body : t) : t =
  let thunk =
    Function (Name.of_string_raw "_", None, body)
  in
  apply_runtime ?monad:(if resumption then monad else None)
    (if resumption then "Resumption" else "Delay")
    "Tau" [ thunk ]

let to_coq_implicit (implicit : string * string) : SmartPrint.t =
  let name, value = implicit in
  nest (parens (!^name ^^ !^":=" ^^ !^value))

let to_coq_assumed_value (kind : assumption_kind) (typ : Type.t) :
    SmartPrint.t =
  let projection =
    match kind with
    | Unreachable -> "@RocqOfOCaml.Basics.unreachable"
    | Unimplemented -> "@RocqOfOCaml.Basics.unimplemented"
  in
  parens
    (nest
       (!^projection
       ^^ Type.to_coq None (Some Type.Context.Apply) typ
       ^^ !^"_"))

let to_coq_record_fields
    (field_implicits : (Name.t * SmartPrint.t) list)
    (render_expression : t -> SmartPrint.t)
    (fields : (PathName.t * int * t) list) : SmartPrint.t =
  if fields = [] then !^"ltac:(constructor)"
  else
  let field_implicits =
    field_implicits
    |> List.map (fun (name, value) ->
           parens (Name.to_coq name ^^ !^":=" ^^ value))
  in
  nest
    (!^"{|"
    ^^ separate space
         (fields
         |> List.map (fun (field, arity, expression) ->
                let arity =
                  arity
                  +
                  if
                    is_partial_operation_field_name (PathName.to_string field)
                  then 1
                  else 0
                in
                nest
                  (nest
                     (PathName.to_coq field
                     ^^ separate space
                          (field_implicits @ Pp.n_underscores arity)
                     ^^ !^":=")
                  ^^ render_expression expression ^-^ !^";")))
    ^^ !^"|}")

let to_coq_module_fields
    (field_implicits : (Name.t * SmartPrint.t) list)
    (render_expression : t -> SmartPrint.t)
    (fields : (PathName.t * int * t) list) : SmartPrint.t =
  let field_implicits =
    field_implicits
    |> List.map (fun (name, value) ->
           parens (Name.to_coq name ^^ !^":=" ^^ value))
  in
  group
    (!^"{|" ^^ newline
    ^^ indent
         (separate (!^";" ^^ newline)
            (fields
            |> List.map (fun (field, arity, expression) ->
                   let arity =
                     arity
                     +
                     if
                       is_partial_operation_field_name
                         (PathName.to_string field)
                     then 1
                     else 0
                   in
                   nest
                     (group
                        (nest
                           (PathName.to_coq field
                           ^^ separate space
                                (field_implicits
                                @ Pp.n_underscores arity))
                        ^^ !^":=")
                     ^^ render_expression expression))))
    ^^ newline ^^ !^"|}")

(** Pretty-print an expression to Rocq (inside parenthesis if the [paren] flag is
    set). *)
let rec to_coq (paren : bool) (e : t) : SmartPrint.t =
  match e with
  | Constant c -> Constant.to_coq paren c
  | Variable (x, implicits) -> (
      let x = MixedPath.to_coq x in
      match implicits with
      | [] -> x
      | _ :: _ ->
          parens (separate space (x :: List.map to_coq_implicit implicits)))
  | Tuple es -> (
      match es with
      | [] -> !^"tt"
      | [ e ] -> to_coq paren e
      | _ :: _ :: _ ->
          parens @@ nest
          @@ separate (!^"," ^^ space) (List.map (to_coq true) es))
  | Constructor (x, implicits, es) -> (
      let implicits = List.map to_coq_implicit implicits in
      match flatten_list e with
      | Some [] -> (
          let nil = !^"nil" in
          match implicits with
          | [] -> nil
          | _ :: _ -> parens (separate space (nil :: implicits)))
      | Some es -> OCaml.list (to_coq false) es
      | None -> (
          let arguments = implicits @ List.map (to_coq true) es in
          match arguments with
          | [] -> PathName.to_coq x
          | _ :: _ ->
              Pp.parens paren @@ nest
              @@ separate space (PathName.to_coq x :: arguments)))
  | ConstructorExtensible (tag, typ, payload) ->
      Pp.parens paren
        (nest
           (!^"Build_extensible"
           ^^ !^("\"" ^ tag ^ "\"")
           ^^ Type.to_coq None (Some Type.Context.Apply) typ
           ^^ to_coq true payload))
  | ConstructorVariant (tag, typ_payload) ->
      Pp.parens paren
        (nest
           (!^"Variant.Build"
           ^^ !^("\"" ^ tag ^ "\"")
           ^^ (match typ_payload with
              | None -> !^"unit"
              | Some (typ, _) -> Type.to_coq None (Some Type.Context.Apply) typ)
           ^^
           match typ_payload with
           | None -> !^"tt"
           | Some (_, payload) -> to_coq true payload))
  | Apply (e_f, e_xs) -> (
      match e_f with
      | Apply (e_f, e_xs')
        when List.for_all (function None -> false | Some _ -> true) e_xs' ->
          to_coq paren (Apply (e_f, e_xs' @ e_xs))
      | _ ->
          let missing_args, all_args, _ =
            List.fold_left
              (fun (missing_args, all_args, index) e_x ->
                match e_x with
                | None ->
                    let missing_arg = !^("x_" ^ string_of_int index) in
                    ( missing_args @ [ missing_arg ],
                      all_args @ [ missing_arg ],
                      index + 1 )
                | Some e_x ->
                    (missing_args, all_args @ [ to_coq true e_x ], index))
              ([], [], 1) e_xs
          in
          Pp.parens paren
            (nest
               ((match missing_args with
                | [] -> empty
                | _ :: _ ->
                    !^"fun" ^^ separate space missing_args ^^ !^"=>" ^^ space)
               ^-^ nest (separate space (to_coq true e_f :: all_args)))))
  | SourceApply (e_f, e_xs, _) ->
      to_coq paren (Apply (e_f, e_xs))
  | Return ("", e) -> to_coq paren e
  | Return (operator, e) ->
      Pp.parens paren @@ nest @@ !^operator ^^ to_coq true e
  | InfixOperator (operator, e1, e2) ->
      Pp.parens paren @@ group @@ to_coq true e1 ^^ !^operator ^^ to_coq true e2
  | Function (x, typ, e) ->
      Pp.parens paren
      @@ nest
           (!^"fun"
           ^^ (match typ with
              | None -> Name.to_coq x
              | Some typ ->
                  parens (Name.to_coq x ^^ !^":" ^^ Type.to_coq None None typ))
           ^^ !^"=>" ^^ to_coq false e)
  | Functions (xs, e) ->
      Pp.parens paren
      @@ nest
           (!^"fun"
           ^^ separate space (List.map Name.to_coq xs)
           ^^ !^"=>" ^^ to_coq false e)
  | LetVar (let_symbol, x, typ_params, e1, e2) -> (
      let get_default () =
        Pp.parens paren
        @@ nest
             (to_coq_let_symbol let_symbol
             ^^ Name.to_coq x
             ^^ (match typ_params with
                | [] -> empty
                | _ :: _ ->
                    braces
                      (nest
                         (separate space (typ_params |> List.map Name.to_coq)
                         ^^ !^":" ^^ !^"Set")))
             ^^ !^":=" ^^ to_coq false e1 ^^ !^"in" ^^ newline
             ^^ to_coq false e2)
      in
      match (let_symbol, x, e1, e2) with
      | None, _, Variable (PathName { path = []; base }, []), _
        when Name.equal base x ->
          to_coq paren e2
      | ( _,
          Name.FunctionParameter,
          _,
          Match
            ( Variable
                ( MixedPath.PathName
                    { PathName.path = []; base = Name.FunctionParameter },
                  [] ),
              _,
              cases,
              is_with_default_case ) ) -> (
          let single_let =
            to_coq_try_single_let_pattern paren let_symbol e1 cases
              is_with_default_case
          in
          match single_let with
          | Some single_let -> single_let
          | None -> get_default ())
      | _ -> get_default ())
  | LetFun (def, e) ->
      (match def.Definition.recursion_strategy with
      | Definition.WellFounded definition_name ->
          to_coq_well_founded_let paren definition_name def e
      | Definition.Partial
          { definition_name; partial_definitions; recursion } ->
          to_coq_partial_let paren definition_name partial_definitions
            recursion def e
      | Definition.Structural | Definition.Convergent _ ->
      let is_mutual_fixpoint =
        def.Definition.is_rec && List.length def.Definition.cases > 1
      in
      let mutual_fixpoint_selector =
        match (is_mutual_fixpoint, def.Definition.cases) with
        | true, (header, _) :: _ ->
            newline ^^ !^"for" ^^ Name.to_coq header.Header.name
        | _ -> empty
      in
      Pp.parens paren
      @@ nest
           (separate newline
              (def.Definition.cases
              |> List.mapi (fun index (header, e) ->
                     let first_case = index = 0 in
                     let { Header.name; _ } = header in
                     (if first_case then
                      if is_mutual_fixpoint then
                        !^"let" ^^ Name.to_coq name ^^ !^":=" ^^ newline
                        ^^ !^"fix"
                      else
                        !^"let"
                        ^^
                        if def.Definition.is_rec && e <> None then !^"fix"
                        else empty
                     else if def.Definition.is_rec then !^"with"
                     else !^"in" ^^ !^"let")
                     ^^ Name.to_coq name
                     ^^ Type.typ_vars_to_coq braces empty empty
                          header.Header.typ_vars
                     ^^ Header.to_coq_instance_args header
                     ^^ group
                          (separate space
                             (header.Header.args
                             |> List.map (fun (x, x_typ) ->
                                    parens
                                      (nest
                                         (Name.to_coq x ^^ !^":"
                                         ^^ Type.to_coq None None x_typ)))))
                     ^^ Header.to_coq_structs header
                     ^^ !^": "
                     ^-^ Type.to_coq None None header.Header.typ
                     ^-^ !^" :=" ^^ newline
                     ^^ indent
                          (match e with
                          | None -> !^"axiom"
                          | Some e -> to_coq false e)))
           ^^ mutual_fixpoint_selector
           ^^ !^"in" ^^ newline ^^ to_coq false e))
  | LetTyp (x, typ_args, typ, e) ->
      Pp.parens paren
      @@ nest
           (!^"let" ^^ Name.to_coq x
           ^^ (match typ_args with
              | [] -> empty
              | _ ->
                  parens
                    (separate space (List.map Name.to_coq typ_args)
                    ^^ !^":" ^^ Pp.set))
           ^^ !^":" ^^ Pp.set ^^ !^":=" ^^ Type.to_coq None None typ ^^ !^"in"
           ^^ newline ^^ to_coq false e)
  | LetModuleUnpack (x, path_name, e2) ->
      Pp.parens paren
      @@ nest
          (!^"let" ^^ !^"'existS" ^^ !^"_" ^^ !^"_" ^^ Name.to_coq x ^^ !^":="
          ^^ PathName.to_coq path_name ^^ !^"in" ^^ newline ^^ to_coq false e2)
  | Match (e, dep_match, cases, is_with_default_case) -> (
      let top_or_alias =
        cases
        |> List.find_map (fun (pattern, _, _) ->
               match pattern with
               | Pattern.Alias (pattern, name)
                 when Pattern.has_or_patterns pattern ->
                   Some name
               | _ -> None)
      in
      match top_or_alias with
      | Some alias ->
          let cases =
            cases
            |> List.map (fun (pattern, cast, body) ->
                   let pattern =
                     match pattern with
                     | Pattern.Alias (pattern, name)
                       when Name.equal name alias ->
                         pattern
                     | _ -> pattern
                   in
                   (pattern, cast, body))
          in
          to_coq paren
            (LetVar
               ( None,
                 alias,
                 [],
                 e,
                 Match
                   ( Variable (MixedPath.of_name alias, []),
                     dep_match,
                     cases,
                     is_with_default_case ) ))
      | None ->
      let single_let =
        to_coq_try_single_let_pattern paren None e cases is_with_default_case
      in
      match single_let with
      | Some single_let -> single_let
      | None ->
          let dep_match_print =
            match dep_match with
            | None -> empty
            | Some { cast; args; motive } ->
                !^"in" ^^ Type.to_coq None None cast ^^ !^"return"
                ^^ separate
                     (space ^^ !^"->" ^^ space)
                     (List.map (Type.to_coq None None) (args @ [ motive ]))
          in
          nest
            (!^"match" ^^ to_coq false e ^^ dep_match_print ^^ !^"with"
           ^^ newline
            ^^ separate space
                 (cases
                 |> List.map (fun (p, existential_cast, e) ->
                        nest
                          (!^"|" ^^ Pattern.to_coq false p ^^ !^"=>"
                          ^^ to_coq_cast_existentials existential_cast e
                          ^^ newline)))
            ^^ (if is_with_default_case then
                if Option.is_some dep_match then
                  !^"|" ^^ !^"_" ^^ !^"=>" ^^ to_coq_ltac Discriminate
                  ^^ newline
                else
                  !^"|" ^^ !^"_" ^^ !^"=>"
                  ^^ !^"unreachable_gadt_branch"
                  ^^ newline
               else empty)
            ^^ !^"end"))
  | MatchExtensible (e, result_typ, cases) -> (
      match cases with
      | [ (None, body) ] ->
          Pp.parens paren
          @@ nest
               (!^"let" ^^ !^"'_" ^^ !^":=" ^^ to_coq false e ^^ !^"in"
              ^^ newline ^^ to_coq false body)
      | _ ->
          let rec dispatch = function
            | [] ->
                to_coq_assumed_value Unreachable result_typ
            | (None, body) :: _ -> to_coq false body
            | (Some (tag, p, typ), body) :: rest ->
                nest
                  (!^"if"
                  ^^ nest
                       (!^"String.eqb" ^^ !^"tag"
                      ^^ !^("\"" ^ tag ^ "\""))
                  ^^ !^"then")
                ^^ newline
                ^^ indent
                     (nest
                        ((match p with
                         | Pattern.Tuple [] -> empty
                         | _ ->
                             nest
                               (!^"let"
                               ^^ (match p with
                                  | Pattern.Tuple [ Pattern.Variable _ ] ->
                                      empty
                                  | _ -> !^"'")
                               ^-^ Pattern.to_coq false p ^^ !^":=")
                             ^^ nest
                                  (!^"cast"
                                  ^^ Type.to_coq None (Some Type.Context.Apply)
                                       typ
                                  ^^ !^"payload" ^^ !^"in")
                             ^^ newline)
                        ^^ to_coq false body))
                ^^ newline ^^ !^"else" ^^ newline
                ^^ indent (dispatch rest)
          in
          nest
            (!^"match" ^^ to_coq false e ^^ !^"with" ^^ newline
            ^^ nest
                 (nest
                    (!^"|" ^^ !^"Build_extensible" ^^ !^"tag" ^^ !^"_"
                   ^^ !^"payload" ^^ !^"=>")
                 ^^ nest (dispatch cases))
            ^^ newline ^^ !^"end"))
  | MatchVariant (e, result_typ, cases) ->
      let variant_name = Name.of_string_raw "_variant_value" in
      let tag_name = Name.of_string_raw "_variant_tag" in
      let payload_name = Name.of_string_raw "_variant_payload" in
      let bind_pattern_doc value pattern body =
        match pattern with
        | Pattern.Any -> body
        | _ ->
            nest
              (!^"let"
              ^^ (match pattern with
                 | Pattern.Variable _ -> empty
                 | _ -> !^"'")
              ^-^ Pattern.to_coq false pattern ^^ !^":=" ^^ value ^^ !^"in")
            ^^ newline ^^ body
      in
      let bind_pattern value pattern body =
        bind_pattern_doc value pattern (to_coq false body)
      in
      let rec dispatch = function
        | [] -> to_coq_assumed_value Unreachable result_typ
        | (Pattern.VariantDefault pattern, body) :: _ ->
            bind_pattern (Name.to_coq variant_name) pattern body
        | (Pattern.VariantCase (tag, pattern, typ, whole), body) :: rest ->
            let fallback = dispatch rest in
            let body =
              match whole with
              | None -> to_coq false body
              | Some whole ->
                  bind_pattern_doc
                    (Name.to_coq variant_name)
                    whole (to_coq false body)
            in
            let payload =
              nest
                (!^"cast"
                ^^ Type.to_coq None (Some Type.Context.Apply) typ
                ^^ Name.to_coq payload_name)
            in
            let tagged_body =
              match pattern with
              | Pattern.Tuple [] -> body
              | _ when Pattern.is_irrefutable pattern ->
                  bind_pattern_doc payload pattern body
              | _ ->
                  nest
                    (!^"match" ^^ payload ^^ !^"with" ^^ newline
                   ^^ !^"|" ^^ Pattern.to_coq false pattern ^^ !^"=>"
                   ^^ body ^^ newline ^^ !^"|" ^^ !^"_"
                   ^^ !^"=>" ^^ fallback ^^ newline ^^ !^"end")
            in
            nest
              (!^"if" ^^ !^"String.eqb" ^^ Name.to_coq tag_name
             ^^ !^("\"" ^ tag ^ "\"") ^^ !^"then")
            ^^ newline
            ^^ indent tagged_body
            ^^ newline ^^ !^"else" ^^ newline ^^ indent fallback
      in
      Pp.parens paren
      @@ nest
           (!^"let" ^^ Name.to_coq variant_name ^^ !^":=" ^^ to_coq false e
          ^^ !^"in" ^^ newline ^^ !^"match" ^^ Name.to_coq variant_name
          ^^ !^"with" ^^ newline ^^ !^"|" ^^ !^"Variant.Build"
          ^^ Name.to_coq tag_name ^^ !^"_" ^^ Name.to_coq payload_name
          ^^ !^"=>" ^^ newline ^^ indent (dispatch cases) ^^ newline ^^ !^"end")
  | Record fields ->
      to_coq_record_fields [] (to_coq false) fields
  | Field (e, x) -> to_coq true e ^-^ !^".(" ^-^ PathName.to_coq x ^-^ !^")"
  | IfThenElse (e1, e2, e3) ->
      Pp.parens paren
      @@ nest
           (group_all (!^"if" ^^ indent (to_coq false e1) ^^ !^"then")
           ^^ newline
           ^^ indent (to_coq false e2)
           ^^ newline ^^ !^"else" ^^ newline
           ^^ indent (to_coq false e3))
  | Module (typ, []) ->
      parens
        (nest
           (!^"ltac:(constructor)" ^^ !^":"
          ^^ Type.to_coq None None typ))
  | Module (_, fields) ->
      to_coq_module_fields [] (to_coq false) fields
  | ModulePack (modul_typ_params, e) ->
      Pp.parens paren @@ nest (to_coq_exist_s modul_typ_params (to_coq true e))
  | Functor (x, typ, e) ->
      Pp.parens paren
      @@ nest
           (!^"fun"
           ^^ parens
                (nest (Name.to_coq x ^^ !^":" ^^ Type.to_coq None None typ))
           ^^ !^"=>" ^^ to_coq false e)
  | Cast (e, typ) ->
      Pp.parens paren
      @@ nest
           (!^"cast"
           ^^ Type.to_coq None (Some Type.Context.Apply) typ
           ^^ to_coq true e)
  | TypAnnotation (e, typ) ->
      parens @@ nest (to_coq true e ^^ !^":" ^^ Type.to_coq None None typ)
  | Assert (typ, e) ->
      Pp.parens paren
      @@
      if Type.is_unit typ then
        nest
          (!^"if" ^^ to_coq false e ^^ !^"then" ^^ !^"tt"
         ^^ !^"else" ^^ to_coq_assumed_value Unreachable typ)
      else
        nest
          (!^"let" ^^ !^"'_" ^^ !^":=" ^^ to_coq false e ^^ !^"in"
         ^^ newline ^^ to_coq_assumed_value Unreachable typ)
  | Assumption (kind, typ, arguments) ->
      Pp.parens paren
      @@ List.fold_right
           (fun argument body ->
             nest
               (!^"let" ^^ !^"'_" ^^ !^":=" ^^ to_coq false argument
              ^^ !^"in" ^^ newline ^^ body))
           arguments (to_coq_assumed_value kind typ)
  | RequiresAssumption (_, _, body) -> to_coq paren body
  | Error message -> !^message
  | ErrorArray es -> OCaml.list (to_coq false) es
  | ErrorTyp typ -> Pp.parens paren @@ Type.to_coq None None typ
  | ErrorMessage (e, error_message) ->
      group (Error.to_comment error_message ^^ newline ^^ to_coq paren e)
  | Ltac tac -> to_coq_ltac tac

(** Render local well-founded recursion with the term-level kernel [Fix].
    The enclosing [Program] command turns each proof hole passed to
    [_rocq_recurse] into a decrease obligation in its branch context. *)
and to_coq_partial_let (paren : bool) (_definition_name : string)
    (partial_definitions : string list)
    (recursion : Definition.partial_recursion)
    (definition : t option Definition.t)
    (continuation : t) : SmartPrint.t =
  match definition.Definition.cases with
  | [ (header, Some body) ] ->
      let resumption = partial_wrapper_is_resumption header.Header.typ in
      let monad = partial_wrapper_monad header.Header.typ in
      let recursive_names = [ Name.to_string header.Header.name ] in
      let body =
        lift_partial_expression ~resumption ~monad ~recursive_names
          ~partial_definitions body
      in
      let body =
        if
          definition.Definition.is_rec
          && recursion = Definition.MayDiverge
        then
          guard_partial_body resumption monad body
        else body
      in
      Pp.parens paren
      @@ nest
           (!^"let"
           ^^
           (if definition.Definition.is_rec then
              match recursion with
              | Definition.MayDiverge -> !^"cofix"
              | Definition.StructurallyTerminates -> !^"fix"
              | Definition.WellFoundedTerminates _ ->
                  failwith
                    "local well-founded recursion returning a partial \
                     computation is not supported"
            else empty)
           ^^ Name.to_coq header.Header.name
           ^^ Type.typ_vars_to_coq braces empty empty header.Header.typ_vars
           ^^ Header.to_coq_instance_args header
           ^^ group
                (separate space
                   (header.Header.args
                   |> List.map (fun (name, typ) ->
                          parens
                            (nest
                               (Name.to_coq name ^^ !^":"
                               ^^ Type.to_coq None None typ)))))
           ^^ !^":" ^^ Type.to_coq None None header.Header.typ
           ^^ !^":=" ^^ newline ^^ indent (to_coq false body)
           ^^ !^"in" ^^ newline ^^ to_coq false continuation)
  | _ ->
      failwith
        "local partial recursion must contain one concrete definition"

and to_coq_well_founded_let (paren : bool) (definition_name : string)
    (definition : t option Definition.t) (continuation : t) : SmartPrint.t =
  match definition.Definition.cases with
  | [ (header, Some body) ] ->
      if header.Header.typ_vars <> [] || header.Header.instance_args <> [] then
        failwith
          "local well-founded recursion with polymorphic or instance \
           parameters is not supported"
      else
        let { Header.name; args; typ; _ } = header in
        let state_name = Name.of_string_raw "_rocq_state" in
        let recurse_name = Name.of_string_raw "_rocq_recurse" in
        let measure_name = Name.of_string_raw "_rocq_measure" in
        let body_name = Name.of_string_raw "_rocq_body" in
        let fix_name = Name.of_string_raw "_rocq_fix" in
        let state_typ =
          match List.map snd args with
          | [] ->
              Type.Apply
                (MixedPath.of_name (Name.of_string_raw "unit"), [])
          | [ typ ] -> typ
          | typs -> Type.Tuple typs
        in
        let tuple values =
          match values with
          | [] -> !^"tt"
          | [ value ] -> value
          | _ -> parens (separate (!^"," ^^ space) values)
        in
        let state_value =
          tuple (List.map (fun (argument, _) -> Name.to_coq argument) args)
        in
        let defined_names =
          definition.Definition.cases
          |> List.map (fun ({ Header.name; _ }, _) -> name)
          |> Name.Set.of_list
        in
        let bound_arguments = args |> List.map fst |> Name.Set.of_list in
        let captures =
          Name.Set.diff
            (Name.Set.of_list definition.Definition.term_environment)
            (Name.Set.union defined_names bound_arguments)
          |> Name.Set.elements
        in
        let measure_input =
          tuple (List.map Name.to_coq captures @ [ Name.to_coq state_name ])
        in
        let bind name value inner =
          !^"let" ^^ Name.to_coq name ^^ !^":=" ^^ value ^^ !^"in"
          ^^ newline ^^ inner
        in
        let rec destruct_tuple index arguments state inner =
          match arguments with
          | [] -> inner
          | [ (argument, _) ] ->
              bind argument state inner
          | (argument, _) :: remaining ->
              let tail =
                Name.of_string_raw
                  ("_rocq_state_tail_" ^ string_of_int index)
              in
              bind argument (!^"fst" ^^ state)
                (bind tail (!^"snd" ^^ state)
                   (destruct_tuple (index + 1) remaining
                      (Name.to_coq tail) inner))
        in
        let destruct_state inner =
          match args with
          | [] -> inner
          | [ (argument, _) ] ->
              bind argument (Name.to_coq state_name) inner
          | _ ->
              destruct_tuple 0 args (Name.to_coq state_name) inner
        in
        let rendered_arguments =
          args
          |> List.map (fun (argument, argument_typ) ->
                 parens
                   (nest
                      (Name.to_coq argument ^^ !^":"
                      ^^ Type.to_coq None None argument_typ)))
          |> separate space
        in
        let body =
          rewrite_local_well_founded_calls name recurse_name
            (List.length args) body
        in
        let () =
          if Name.Set.mem name (get_free_vars body) then
            failwith
              ("local well-founded recursive function "
              ^ Name.to_string name
              ^ " must be fully applied at each recursive call")
        in
        let functional =
          parens
            (nest
               (!^"fun" ^^ Name.to_coq state_name
               ^^ Name.to_coq recurse_name ^^ !^"=>" ^^ newline
               ^^ indent (destruct_state (to_coq false body))))
        in
        let body_definition =
          !^"let" ^^ Name.to_coq body_name ^^ !^":"
          ^^ parens
               (nest
                  (!^"forall" ^^ Name.to_coq state_name ^^ !^":"
                  ^^ Type.to_coq None None state_typ ^-^ !^","
                  ^^ parens
                       (nest
                          (!^"forall" ^^ !^"_rocq_next" ^^ !^":"
                          ^^ Type.to_coq None None state_typ ^-^ !^","
                          ^^ !^"ltof"
                          ^^ Type.to_coq None (Some Type.Context.Apply)
                               state_typ
                          ^^ Name.to_coq measure_name ^^ !^"_rocq_next"
                          ^^ Name.to_coq state_name ^^ !^"->"
                          ^^ Type.to_coq None None typ))
                  ^^ !^"->" ^^ Type.to_coq None None typ))
          ^^ !^":=" ^^ functional ^^ !^"in"
        in
        let motive =
          parens
            (!^"fun" ^^ !^"_" ^^ !^"=>" ^^ Type.to_coq None None typ)
        in
        let measure_definition =
          !^"let" ^^ Name.to_coq measure_name
          ^^ parens
               (Name.to_coq state_name ^^ !^":"
               ^^ Type.to_coq None None state_typ)
          ^^ !^":" ^^ !^"nat" ^^ !^":="
          ^^ !^"RocqOfOCaml.Basics.well_founded_measure"
          ^^ !^("\"" ^ String.escaped definition_name ^ "\"")
          ^^ measure_input ^^ !^"in"
        in
        let fix_definition =
          !^"let" ^^ Name.to_coq fix_name ^^ !^":="
          ^^ !^"@Fix" ^^ Type.to_coq None (Some Type.Context.Apply) state_typ
          ^^ parens
               (!^"ltof"
               ^^ Type.to_coq None (Some Type.Context.Apply) state_typ
               ^^ Name.to_coq measure_name)
          ^^ parens
               (!^"well_founded_ltof"
               ^^ Type.to_coq None (Some Type.Context.Apply) state_typ
               ^^ Name.to_coq measure_name)
          ^^ motive ^^ Name.to_coq body_name ^^ !^"in"
        in
        let public_definition =
          !^"let" ^^ Name.to_coq name ^^ rendered_arguments
          ^^ !^":" ^^ Type.to_coq None None typ ^^ !^":="
          ^^ Name.to_coq fix_name ^^ state_value ^^ !^"in"
        in
        Pp.parens paren
        @@ nest
             (measure_definition ^^ newline
             ^^ body_definition ^^ newline
             ^^ fix_definition ^^ newline
             ^^ public_definition ^^ newline
             ^^ to_coq false continuation)
  | _ ->
      failwith
        "local well-founded recursion must contain one concrete definition"

and to_coq_ltac (tac : ltac) : SmartPrint.t =
  !^"ltac:" ^-^ parens (to_coq_tac tac)

and to_coq_tac (tac : ltac) : SmartPrint.t =
  match tac with
  | Subst -> !^"subst"
  | Discriminate -> !^"discriminate"
  | Exact t -> !^"exact" ^^ to_coq true t
  | Concat (t1, t2) ->
      separate (!^";" ^^ space) [ to_coq_tac t1; to_coq_tac t2 ]

and to_coq_try_single_let_pattern (paren : bool) (let_symbol : string option)
    (e : t) (cases : (Pattern.t * match_existential_cast option * t) list)
    (is_with_default_case : bool) : SmartPrint.t option =
  match (cases, is_with_default_case) with
  | [ (pattern, existential_cast, e2) ], false
    when not (Pattern.has_or_patterns pattern) ->
      Some
        (Pp.parens paren
        @@ nest
             (to_coq_let_symbol let_symbol
             ^^ !^"'"
             ^-^ Pattern.to_coq false pattern
             ^-^ !^" :=" ^^ to_coq false e ^^ !^"in" ^^ newline
             ^^ to_coq_cast_existentials existential_cast e2))
  | _ -> None

and to_coq_cast_existentials (existential_cast : match_existential_cast option)
    (e : t) : SmartPrint.t =
  let e =
    match existential_cast with
    | Some { return_typ; cast_result = true; _ } ->
        group
          (nest
             (!^"cast" ^^ Type.to_coq None (Some Type.Context.Apply) return_typ)
          ^^ to_coq true e)
    | _ -> to_coq false e
  in
  match existential_cast with
  | None -> e
  | Some { new_typ_vars; bound_vars; use_axioms; enable; _ } -> (
      let variable_names =
        Pp.primitive_tuple
          (bound_vars |> List.map (fun (name, _) -> Name.to_coq name))
      in
      let variable_typ paren =
        match bound_vars with
        | [ (_, typ) ] ->
            let context = if paren then Some Type.Context.Apply else None in
            Type.to_coq None context typ
        | _ ->
            Pp.primitive_tuple_type
              (bound_vars
              |> List.map (fun (_, typ) -> Type.to_coq None None typ))
      in
      match (enable, bound_vars, new_typ_vars) with
      | false, _, _ | _, [], _ -> e
      | _, _, [] ->
          if use_axioms then
            let variable_names_pattern =
              match bound_vars with
              | [ _ ] -> variable_names
              | _ -> !^"'" ^-^ variable_names
            in
            nest
              (!^"let" ^^ variable_names_pattern ^^ !^":="
              ^^ nest (!^"cast" ^^ variable_typ true ^^ variable_names)
              ^^ !^"in" ^^ newline ^^ e)
          else e
      | _ ->
          let new_typ_vars_names =
            List.map (fun var -> Name.to_coq @@ fst var) new_typ_vars
          in
          let new_typ_vars_kinds =
            List.map (fun var -> Kind.to_coq @@ snd var) new_typ_vars
          in
          let existential_names = Pp.primitive_tuple new_typ_vars_names in
          let existential_names_pattern =
            Pp.primitive_tuple_pattern new_typ_vars_names
          in
          nest
            (!^"let" ^^ !^"'existT" ^^ !^"_" ^^ existential_names
           ^^ variable_names ^^ !^":="
            ^^ nest
                 (let operator, option =
                    if use_axioms then ("cast_exists", "Es") else ("existT", "A")
                  in
                  !^operator
                  ^^ nest
                       (parens
                          (!^option ^^ !^":="
                          ^^ Pp.primitive_tuple_type new_typ_vars_kinds))
                  ^^ parens
                       (nest
                          (!^"fun" ^^ existential_names_pattern ^^ !^"=>"
                         ^^ variable_typ false))
                  ^^ (if use_axioms then empty
                     else Pp.primitive_tuple_infer (List.length new_typ_vars))
                  ^^ variable_names)
            ^^ !^"in" ^^ newline ^^ e))

and to_coq_exist_s (module_typ_params : int Tree.t) (e : SmartPrint.t) :
    SmartPrint.t =
  let arities =
    Tree.flatten module_typ_params |> List.map (fun (_, arity) -> arity)
  in
  let typ_names = Tree.flatten module_typ_params |> List.map (fun _ -> !^"_") in
  let nb_of_existential_variables = List.length typ_names in
  nest
    (!^"existS"
    ^^ parens
         (nest
            (!^"A :=" ^^ Pp.primitive_tuple_type (List.map Pp.typ_arity arities)))
    ^^ (match nb_of_existential_variables with
       | 0 -> !^"(fun _ => _)"
       | _ -> !^"_")
    ^^ Pp.primitive_tuple typ_names
    ^^ e)

let to_coq_record_with_field_implicits
    (field_implicits : (Name.t * SmartPrint.t) list) (e : t) :
    SmartPrint.t =
  match e with
  | Record fields ->
      to_coq_record_fields field_implicits (to_coq false) fields
  | Module (typ, []) ->
      parens
        (nest
           (!^"ltac:(constructor)" ^^ !^":"
          ^^ Type.to_coq None None typ))
  | Module (_, fields) ->
      to_coq_module_fields field_implicits (to_coq false) fields
  | _ -> to_coq false e
