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
              (nest (Name.to_coq name ^^ !^":" ^^ Type.to_coq None None typ)))
    |> separate space
end

module Definition = struct
  type termination_certificate = { measure : string; tactic : string }

  type well_founded_details = {
    definition_name : string;
    certificate : termination_certificate option;
  }

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
    | WellFounded of well_founded_details
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

type assumption_kind = Unreachable | Unimplemented | ModuleContext
type assumption_requirement = assumption_kind * Type.t

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
    "Option.get";
    "Map.min_binding";
    "Map.max_binding";
    "Map.choose";
    "Map.find";
    "Map.find_first";
    "Map.find_last";
    "Set.min_elt";
    "Set.max_elt";
    "Set.choose";
    "Set.find";
    "Set.find_first";
    "Set.find_last";
    "Char.chr";
    "Iarray.init";
    "Iarray.get";
    "Iarray.exists2";
    "String.make";
    "String.init";
    "String.get";
    "String.sub";
    "String.contains_from";
    "String.rcontains_from";
    "String.get_uint8";
    "String.get_int8";
    "String.get_uint16_be";
    "String.get_uint16_le";
    "String.get_uint16_ne";
    "String.get_int16_be";
    "String.get_int16_le";
    "String.get_int16_ne";
    "String.get_uint32_be";
    "String.get_uint32_le";
    "String.get_int32_be";
    "String.get_int32_le";
    "String.get_int32_ne";
    "String.get_int64_be";
    "String.get_int64_le";
    "String.get_int64_ne";
    "String.unsafe_get";
    "String.index_from";
    "String.index_from_opt";
    "String.rindex_from";
    "String.rindex_from_opt";
    "String.index";
    "String.rindex";
    "Result.get_ok";
    "Result.get_ok'";
    "Result.get_error";
    "Result.error_to_failure";
    "Z.to_int";
    "Z.to_int32";
    "Z.to_int64";
    "Z.to_int32_unsigned";
    "Z.to_int64_unsigned";
    "Z.extract";
    "Z.signed_extract";
    "Z.powm";
    "Z.of_string";
    "Int64.of_string";
    "Seq.init";
    "Seq.take";
    "Seq.drop";
    "Seq.once";
    "Seq.range";
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
  |> replace_prefix "Option." "OCamlOption."
  |> replace_prefix "Map." "OCamlMap."
  |> replace_prefix "Set." "OCamlSet."
  |> replace_prefix "Char." "OCamlChar."
  |> replace_prefix "Iarray." "OCamlIarray."
  |> replace_prefix "String." "OCamlString."
  |> replace_prefix "Result." "OCamlResult."
  |> replace_prefix "Z." "OCamlZ."
  |> replace_prefix "Int64." "OCamlInt64."
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
      let source_signature_name =
        match String.rindex_opt name '.' with
        | None -> name
        | Some separator ->
            String.sub name 0 separator
            ^ ".S"
            ^ String.sub name separator (String.length name - separator)
      in
      path = name
      || path = "Stdlib." ^ name
      || string_ends_with path ("." ^ name)
      || path = source_signature_name
      || path = "Stdlib." ^ source_signature_name
      || string_ends_with path ("." ^ source_signature_name)
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

type source_application_type = {
  callee : Type.t;
  result : Type.t;
  specialization : Type.t;
  module_substitutions : (Type.t * Type.t) list;
  module_assumption_telescope : assumption_requirement list option;
  assumption_telescope : assumption_requirement list option;
}

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
  | SourceApply of t * t option list * source_application_type
      (** An application from the typed OCaml tree. [result] is the public
          source type used by the normal translation, while [specialization]
          expands source aliases so propagated requirements can be instantiated
          through local aliases of applied-functor result types. *)
  | Return of string * t  (** Application specialized for a return operation. *)
  | InfixOperator of string * t * t
      (** Application specialized for an infix operator. An argument name, an
          optional type and a body. *)
  | Function of Name.t * Type.t option * t
  | Functions of Name.t list * t  (** An argument names and a body. *)
  | LetVar of string option * Name.t * Name.t list * t * t
      (** The let of a variable, with optionally a list of polymorphic
          variables. We optionally specify the symbol of the let operator as it
          may be non-standard for monadic binds. *)
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
  | MatchWithEquation of
      t
      * (Pattern.t * match_existential_cast option * t) list
      * bool
      (** A computationally identical nondependent match whose branches
          receive an equation relating the scrutinee to the selected pattern.
          Certified well-founded recursion uses it to retain the source facts
          needed by decrease proofs. *)
  | MatchExtensible of
      t * Type.t * ((string * Pattern.t * Type.t) option * t) list
      (** Match an expression on a list of extensible type patterns. *)
  | MatchVariant of t * Type.t * (Pattern.dynamic_variant * t) list
      (** Match an unmapped polymorphic variant through its dynamic tag. *)
  | Record of (PathName.t * int * t) list
      (** Construct a record giving an expression for each field. *)
  | Field of t * PathName.t  (** Access to a field of a record. *)
  | IfThenElse of t * t * t  (** The "else" part may be unit. *)
  | IfThenElseWithEquation of t * t * t
      (** A computationally identical conditional whose branches receive the
          selected guard equation. Certified well-founded recursion uses it so
          decrease tactics can recover source control-flow facts. *)
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
  | PropagatedAssumption of assumption_kind * Type.t * t
      (** A transient call-graph requirement. The propagation pass rebuilds
          these nodes from current callee specifications on every iteration. *)
  | Error of string  (** An error message for unhandled expressions. *)
  | ErrorArray of t list  (** An error produced by an array of elements. *)
  | ErrorTyp of Type.t  (** An error composed of a type. *)
  | ErrorMessage of t * string
      (** An expression together with an error message. *)
  | Ltac of ltac

and ltac =
  | Subst
  | Discriminate
  | Exact of t
  | Concat of ltac * ltac
  | Raw of string

(** Take a function expression and make explicit the list of arguments and the
    body. *)
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
      try Ctype.full_expand ~may_forget_scope:false env typ with _ -> typ
    in
    match Types.get_desc typ with
    | Tarrow (_, argument, result, _) -> (
        match open_ocaml_arrow_type env result (n - 1) with
        | Some (arguments, result) -> Some (argument :: arguments, result)
        | None -> None)
    | _ -> None

(** Whether rocq-of-ocaml's compatibility library provides a computational
    [EqDec] instance for the translation of this OCaml type.

    OCaml [(=)] is a polymorphic runtime primitive. We use Rocq's executable
    [equiv_decb] only for the closed fragment where the compatibility library
    supplies decision procedures. Other instantiations must retain the explicit
    [Stdlib.polymorphic_equal] boundary instead of leaving unresolved typeclass
    obligations in generated code. *)
let rec has_rocq_eq_dec (env : Env.t) (typ : Types.type_expr) : bool =
  let typ =
    try Ctype.full_expand ~may_forget_scope:false env typ with _ -> typ
  in
  match Types.get_desc typ with
  | Tconstr (path, arguments, _) -> (
      match Path.last path with
      | "int" | "int32" | "int64" | "nativeint" | "float" | "bool" | "unit"
      | "char" | "string" ->
          true
      | "list" | "option" | "array" | "iarray" ->
          List.for_all (has_rocq_eq_dec env) arguments
      | _ -> false)
  | Ttuple elements ->
      List.for_all (fun (_, element) -> has_rocq_eq_dec env element) elements
  | Tlink typ | Tsubst (typ, _) | Tpoly (typ, _) -> has_rocq_eq_dec env typ
  | Tvar _ | Tunivar _ | Tarrow _ | Tobject _ | Tfield _ | Tnil | Tvariant _
  | Tpackage _ ->
      false

let equality_argument_has_rocq_eq_dec (e : expression) : bool =
  match open_ocaml_arrow_type e.exp_env e.exp_type 2 with
  | Some (argument :: _, _) -> has_rocq_eq_dec e.exp_env argument
  | Some ([], _) | None -> false

(** OCaml's ordering operators are polymorphic runtime primitives, but their
    behavior at [int] is exactly the corresponding signed integer comparison.
    Preserve the explicit polymorphic boundary for every other type while giving
    integer programs a computational, provable translation. *)
let specialized_integer_comparison (e : expression) : string option =
  let target =
    match e.exp_desc with
    | Texp_ident (path, _, _) -> (
        match Path.name path with
        | "Stdlib.<" | "Pervasives.<" | "Stdlib.op_lt" | "Pervasives.op_lt" ->
            Some "ltb"
        | "Stdlib.>" | "Pervasives.>" | "Stdlib.op_gt" | "Pervasives.op_gt" ->
            Some "gtb"
        | "Stdlib.<=" | "Pervasives.<=" | "Stdlib.op_lteq"
        | "Pervasives.op_lteq" ->
            Some "leb"
        | "Stdlib.>=" | "Pervasives.>=" | "Stdlib.op_gteq"
        | "Pervasives.op_gteq" ->
            Some "geb"
        | _ -> None)
    | _ -> None
  in
  match (target, open_ocaml_arrow_type e.exp_env e.exp_type 2) with
  | Some target, Some (argument :: _, _) -> (
      let argument =
        try Ctype.full_expand ~may_forget_scope:false e.exp_env argument
        with _ -> argument
      in
      match Types.get_desc argument with
      | Tconstr (path, _, _) when String.equal (Path.last path) "int" ->
          Some target
      | _ -> None)
  | Some _, Some ([], _) | Some _, None | None, _ -> None

let z_comparison_variable (name : string) : t =
  Variable
    ( MixedPath.PathName
        (PathName.of_name [ Name.of_string_raw "Z" ] (Name.of_string_raw name)),
      [] )

type constructor_equality = {
  negate : bool;
  scrutinee : expression;
  constructor : Data_types.constructor_description;
  payloads : expression list;
  exhaustive : bool;
}

let constructor_equality_application (path : Path.t)
    (arguments : (Asttypes.arg_label * apply_arg) list) :
    constructor_equality option =
  let negate =
    match Path.name path with
    | "Stdlib.=" | "Pervasives.=" | "Stdlib.op_eq" | "Pervasives.op_eq" ->
        Some false
    | "Stdlib.<>" | "Pervasives.<>" | "Stdlib.op_ltgt" | "Pervasives.op_ltgt" ->
        Some true
    | _ -> None
  in
  let arguments =
    arguments
    |> List.filter_map (fun (_, argument) ->
        match argument with
        | Arg expression -> Some expression
        | Omitted () -> None)
  in
  let as_constructor expression =
    match expression.exp_desc with
    | Texp_construct (_, constructor, payloads) -> (
        match constructor.cstr_tag with
        | Cstr_extension _ -> None
        | _ ->
            if
              List.for_all
                (fun payload ->
                  has_rocq_eq_dec payload.exp_env payload.exp_type)
                payloads
            then Some (constructor, payloads)
            else None)
    | _ -> None
  in
  match (negate, arguments) with
  | Some negate, [ left; right ] -> (
      match as_constructor right with
      | Some (constructor, payloads) ->
          Some
            {
              negate;
              scrutinee = left;
              constructor;
              payloads;
              exhaustive =
                constructor.cstr_consts + constructor.cstr_nonconsts = 1;
            }
      | None -> (
          match as_constructor left with
          | Some (constructor, payloads) ->
              Some
                {
                  negate;
                  scrutinee = right;
                  constructor;
                  payloads;
                  exhaustive =
                    constructor.cstr_consts + constructor.cstr_nonconsts = 1;
                }
          | None -> None))
  | _ -> None

let error_message (e : t) (category : Error.Category.t) (message : string) :
    t Monad.t =
  raise (ErrorMessage (e, message)) category message

let error_message_in_module (field : Name.t option) (e : t)
    (category : Error.Category.t) (message : string) :
    (string option * Name.t option * t) option Monad.t =
  raise (Some (Some message, field, e)) category message

module ModuleTypValues = struct
  type nested_module = {
    source_fields : string list;
    target_type : Types.module_type;
    target_signature : Path.t;
  }

  type record_operation =
    | RecordMake of string list * int * string list * Path.t option
    | RecordGet of string list * int * string * Path.t option

  type t = {
    field : Name.t;
    access : Name.t list;
    nb_free_vars : int;
    nested_module : nested_module option;
    record_operation : record_operation option;
  }

  let record_operation_name (is_constructor : bool) (prefix : string list)
      (type_name : string) (field_name : string option) : Name.t Monad.t =
    let operation =
      if is_constructor then "_rocq_record_make"
      else "_rocq_record_get_" ^ Option.get field_name
    in
    Name.of_strings true (prefix @ [ type_name; operation ])

  let get ?(skip_functors = false)
      ?(exclude_value = fun (_ : string list) -> false)
      (typ_vars : Name.t Name.Map.t) (module_typ : Types.module_type) :
      t list Monad.t =
    get_env >>= fun env ->
    let rec get_signature (prefix : string list) (access : Name.t list)
        (signature : Types.signature) : t list Monad.t =
      signature
      |> Monad.List.concat_map (fun item ->
          match item with
          | Types.Sig_value (ident, { val_type; _ }, _) ->
              if exclude_value (prefix @ [ Ident.name ident ]) then return []
              else
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
                      nested_module = None;
                      record_operation = None;
                    };
                  ]
          | Types.Sig_type
              ( ident,
                {
                  Types.type_kind = Type_record (labels, _);
                  type_params;
                  type_manifest;
                  _;
                },
                _,
                _ ) ->
              let type_path = prefix @ [ Ident.name ident ] in
              let type_parameter_count = List.length type_params in
              let canonical_type_path =
                match type_manifest with
                | Some manifest -> (
                    match Types.get_desc manifest with
                    | Tconstr (path, _, _) -> Some path
                    | _ -> None)
                | None -> None
              in
              let field_names =
                labels
                |> List.map
                     (fun ({ Types.ld_id; _ } : Types.label_declaration) ->
                       Ident.name ld_id)
              in
              let* constructor =
                record_operation_name true prefix (Ident.name ident) None
              in
              let constructor =
                {
                  field = constructor;
                  access;
                  nb_free_vars = 0;
                  nested_module = None;
                  record_operation =
                    Some
                      (RecordMake
                         ( type_path,
                           type_parameter_count,
                           field_names,
                           canonical_type_path ));
                }
              in
              let* projections =
                field_names
                |> Monad.List.map (fun field_name ->
                    let* field =
                      record_operation_name false prefix (Ident.name ident)
                        (Some field_name)
                    in
                    return
                      {
                        field;
                        access;
                        nb_free_vars = 0;
                        nested_module = None;
                        record_operation =
                          Some
                            (RecordGet
                               ( type_path,
                                 type_parameter_count,
                                 field_name,
                                 canonical_type_path ));
                      })
              in
              return (constructor :: projections)
          | Sig_module (ident, _, _, _, _)
            when Ident.name ident = "Internal_for_tests" ->
              return []
          | Sig_module (ident, _, { Types.md_type; _ }, _, _) -> (
              if exclude_value (prefix @ [ Ident.name ident ]) then return []
              else if
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
                  | Mty_alias path
                    when not (Type.path_contains_functor_application path) ->
                      let* { PathName.path; base } =
                        PathName.of_path_without_convert false path
                      in
                      return (path @ [ base ])
                  | Mty_alias _ | Mty_ident _ | Mty_signature _ | Mty_functor _
                  | Mty_for_hole ->
                      return (access @ [ module_name ])
                in
                let* is_first_class =
                  IsFirstClassModule.is_module_typ_first_class md_type
                    (Some (Path.Pident ident))
                in
                let is_synthetic_parameter_alias =
                  match (md_type, is_first_class) with
                  | Mty_alias (Path.Pident parameter), Found signature_path
                    when not (Ident.global parameter) ->
                      let signature_name = Path.last signature_path in
                      let parameter_name = Ident.name parameter in
                      String.ends_with ~suffix:"_signature" signature_name
                      && (String.ends_with
                            ~suffix:("_" ^ parameter_name ^ "_signature")
                            signature_name
                         || String.equal parameter_name (Ident.name ident)
                            && not
                                 (String.ends_with
                                    ~suffix:
                                      ("_" ^ Ident.name ident ^ "_signature")
                                    signature_name))
                  | _ -> false
                in
                match is_first_class with
                | Found _ when is_synthetic_parameter_alias -> (
                    match Env.scrape_alias env md_type with
                    | Mty_signature signature ->
                        get_signature
                          (prefix @ [ Ident.name ident ])
                          module_access signature
                    | _ ->
                        raise [] Unexpected
                          ("Anonymous functor parameter alias `"
                         ^ Ident.name ident
                         ^ "` did not expose a concrete signature."))
                | Found target_signature ->
                    let* field =
                      Name.of_strings false (prefix @ [ Ident.name ident ])
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
                          nested_module =
                            Some
                              {
                                source_fields = prefix @ [ Ident.name ident ];
                                target_type = md_type;
                                target_signature;
                              };
                          record_operation = None;
                        };
                      ]
                | Not_found _
                  when match Env.scrape_alias env md_type with
                       | Mty_functor _ -> true
                       | _ -> false ->
                    let* field =
                      Name.of_strings false (prefix @ [ Ident.name ident ])
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
                          nested_module = None;
                          record_operation = None;
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

let record_operation_expression ?source_root
    (operation : ModuleTypValues.record_operation) : t Monad.t =
  let type_path, type_parameter_count, field_names, canonical_type_path =
    match operation with
    | ModuleTypValues.RecordMake
        (type_path, parameter_count, fields, canonical_type_path) ->
        (type_path, parameter_count, fields, canonical_type_path)
    | ModuleTypValues.RecordGet
        (type_path, parameter_count, field, canonical_type_path) ->
        (type_path, parameter_count, [ field ], canonical_type_path)
  in
  let type_parameters =
    List.init type_parameter_count (fun index ->
        Name.of_string_raw ("_rocq_record_parameter_" ^ string_of_int index))
  in
  let module_fields, type_name =
    match List.rev type_path with
    | type_name :: reversed_modules -> (List.rev reversed_modules, type_name)
    | [] -> failwith "record operation without a type path"
  in
  let* env = get_env in
  let actual_type_path =
    match source_root with
    | Some root ->
        let module_path =
          List.fold_left
            (fun path field -> Path.Pdot (path, field))
            root module_fields
        in
        Path.Pdot (module_path, type_name)
    | None ->
        Option.value canonical_type_path
          ~default:
            (let longident =
               match Longident.unflatten (module_fields @ [ type_name ]) with
               | Some longident -> longident
               | None -> assert false
             in
             fst (Env.lookup_type ~use:false ~loc:Location.none longident env))
  in
  let labels =
    try
      Env.lookup_all_labels_from_type ~use:false ~loc:Location.none
        Env.Construct actual_type_path env
      |> List.map fst
    with Not_found | Env.Error _ -> []
  in
  let* projection_paths =
    field_names
    |> Monad.List.map (fun field_name ->
        match
          List.find_opt
            (fun (label : Data_types.label_description) ->
              String.equal label.lbl_name field_name)
            labels
        with
        | Some label -> PathName.of_label_description label
        | None ->
            let* field_name = Name.of_string true field_name in
            PathName.of_path_and_name_with_convert actual_type_path field_name)
  in
  match (operation, projection_paths) with
  | ModuleTypValues.RecordMake (_, _, _, _), _ ->
      let* arguments =
        field_names
        |> Monad.List.map (fun field ->
            Name.of_string true ("_rocq_record_field_" ^ field))
      in
      let fields =
        List.map2
          (fun projection argument ->
            (projection, 0, Variable (MixedPath.of_name argument, [])))
          projection_paths arguments
      in
      return (Functions (type_parameters @ arguments, Record fields))
  | ModuleTypValues.RecordGet (_, _, _, _), [ projection ] ->
      let value = Name.of_string_raw "_rocq_record_value" in
      return
        (Functions
           ( type_parameters @ [ value ],
             Field (Variable (MixedPath.of_name value, []), projection) ))
  | ModuleTypValues.RecordGet _, _ -> assert false

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
      let* path_name = PathName.of_path_with_convert false path in
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
        return (Type.Variable name)) (typ_params_arity : int Tree.t)
    ?(field_value =
      fun ({ ModuleTypValues.record_operation; _ } : ModuleTypValues.t)
        mixed_path
      ->
        match record_operation with
        | None -> return (Variable (mixed_path, []))
        | Some operation -> record_operation_expression operation)
    (values : ModuleTypValues.t list) (signature_path : Path.t)
    (mixed_path_of_value_or_typ : Name.t -> Name.t list -> MixedPath.t Monad.t)
    : t Monad.t =
  let* fields =
    values
    |> Monad.List.map
         (fun ({ ModuleTypValues.field; access; nb_free_vars; _ } as value) ->
           let* field_name =
             PathName.of_path_and_name_with_convert signature_path field
           in
           let* mixed_path =
             match value.ModuleTypValues.record_operation with
             | Some _ ->
                 (* Synthetic record constructors and projections are rebuilt
                 from the nominal source record.  They do not denote an
                 existing module field, and therefore legitimately have no
                 local access path. *)
                 return (MixedPath.of_name field)
             | None -> mixed_path_of_value_or_typ field access
           in
           let* value = field_value value mixed_path in
           return (field_name, nb_free_vars, value))
  in
  let* signature_path, explicit_params =
    ModuleTyp.signature_path_and_explicit_params signature_path
  in
  let* typ_params =
    typ_params_arity |> Tree.flatten
    |> Monad.List.map (fun (path, _) ->
        let* name = Name.of_strings false path in
        let* typ = typ_param_of_path path in
        return (name, Some typ))
  in
  return
    (Module
       (Type.Signature (signature_path, explicit_params @ typ_params), fields))

(** Preserve the dependent signature of an anonymous structure at the point
    where its terminal record is elaborated. The aliases introduced while
    translating the structure (for example, an associated type [t]) are still in
    scope there; annotating the whole [let] expression would put those aliases
    out of scope in the annotation. *)
let rec annotate_terminal_module_with (local_type_aliases : Name.Set.t) (e : t)
    : t =
  match e with
  | Module ((Type.Signature (_, parameters) as typ), _) ->
      let has_scoped_parameters =
        parameters
        |> List.for_all (function
          | _, Some (Type.Variable name) -> Name.Set.mem name local_type_aliases
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
      LetFun (definition, annotate_terminal_module_with local_type_aliases body)
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
  | Match (e, _, cases, _) | MatchWithEquation (e, cases, _) ->
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
              | Some { bound_vars; return_typ; cast_result; enable = true; _ }
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
  | IfThenElse (e1, e2, e3) | IfThenElseWithEquation (e1, e2, e3) ->
      of_list [ e1; e2; e3 ]
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
      Name.Set.union (Type.local_typ_constructors_of_typ typ) (of_list es)
  | RequiresAssumption (_, typ, e) | PropagatedAssumption (_, typ, e) ->
      Name.Set.union
        (Type.local_typ_constructors_of_typ typ)
        (free_existential_typs e)
  | Error _ -> Name.Set.empty
  | ErrorArray es -> of_list es
  | ErrorTyp typ -> Type.local_typ_constructors_of_typ typ
  | ErrorMessage (e, _) -> free_existential_typs e
  | Ltac _ -> Name.Set.empty

(** Get the free variables of an expression. This is useful to optimize the
    translation of mutually recursive definitions implemented as notation, by
    detecting which ones are used. *)
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
  | Match (e, _, entries, _) | MatchWithEquation (e, entries, _) ->
      Name.Set.union (get_free_vars e)
        (List.fold_left Name.Set.union Name.Set.empty
           (entries
           |> List.map (fun (pattern, _, e) ->
               Name.Set.diff (get_free_vars e) (Pattern.get_free_vars pattern))
           ))
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
  | IfThenElse (e1, e2, e3) | IfThenElseWithEquation (e1, e2, e3) ->
      get_free_vars_of_list [ e1; e2; e3 ]
  | Module (_, entries) ->
      get_free_vars_of_list (List.map (fun (_, _, e) -> e) entries)
  | ModulePack (_, e) -> get_free_vars e
  | Functor (x, _, e) -> Name.Set.remove x (get_free_vars e)
  | Cast (e, _) -> get_free_vars e
  | TypAnnotation (e, _) -> get_free_vars e
  | Assert (_, e) -> get_free_vars e
  | Assumption (_, _, es) -> get_free_vars_of_list es
  | RequiresAssumption (_, _, e) | PropagatedAssumption (_, _, e) ->
      get_free_vars e
  | Error _ -> Name.Set.empty
  | ErrorArray es -> get_free_vars_of_list es
  | ErrorTyp _ -> Name.Set.empty
  | ErrorMessage (e, _) -> get_free_vars e
  | Ltac _ -> Name.Set.empty

(** Whether an expression contains a local well-founded recursive definition
    selected by [accept]. *)
let rec has_well_founded_recursion_matching
    (accept : Definition.well_founded_details -> bool) (e : t) : bool =
  let recurse = has_well_founded_recursion_matching accept in
  let any es = List.exists recurse es in
  match e with
  | Constant _ | Variable _ | Error _ | ErrorTyp _ | Ltac _ -> false
  | Tuple es | Constructor (_, _, es) | Assumption (_, _, es) | ErrorArray es ->
      any es
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
  | Assert (_, e)
  | RequiresAssumption (_, _, e)
  | PropagatedAssumption (_, _, e)
  | ErrorMessage (e, _) ->
      recurse e
  | ConstructorVariant (_, None) -> false
  | ConstructorVariant (_, Some (_, e)) -> recurse e
  | Apply (f, args) | SourceApply (f, args, _) ->
      any (f :: List.filter_map (fun argument -> argument) args)
  | InfixOperator (_, left, right) -> any [ left; right ]
  | LetVar (_, _, _, value, body) -> any [ value; body ]
  | LetFun (definition, body) ->
      (match definition.Definition.recursion_strategy with
        | Definition.WellFounded details -> accept details
        | Definition.Partial
            { recursion = Definition.WellFoundedTerminates _; _ } ->
            true
        | Definition.Structural | Definition.Partial _ | Definition.Convergent _
          ->
            false)
      || recurse body
      || any (List.filter_map snd definition.Definition.cases)
  | Match (scrutinee, _, cases, _)
  | MatchWithEquation (scrutinee, cases, _) ->
      recurse scrutinee || any (List.map (fun (_, _, body) -> body) cases)
  | MatchExtensible (scrutinee, _, cases) ->
      recurse scrutinee || any (List.map snd cases)
  | MatchVariant (scrutinee, _, cases) ->
      recurse scrutinee || any (List.map snd cases)
  | Record fields | Module (_, fields) ->
      any (List.map (fun (_, _, value) -> value) fields)
  | IfThenElse (condition, then_, else_)
  | IfThenElseWithEquation (condition, then_, else_) ->
      any [ condition; then_; else_ ]

(** The enclosing top-level command must use [Program] for local [Fix] terms.
    Certified recursive calls contain checked tactic proof terms; uncertified
    calls leave holes that become obligations. *)
let has_well_founded_recursion (e : t) : bool =
  has_well_founded_recursion_matching (fun _ -> true) e

let has_uncertified_well_founded_recursion (e : t) : bool =
  has_well_founded_recursion_matching
    (fun details -> Option.is_none details.Definition.certificate)
    e

(** Whether an expression contains a local partial recursive definition. Its
    enclosing definition must expose the corresponding partial result type. *)
let rec has_partial_recursion (e : t) : bool =
  let any es = List.exists has_partial_recursion es in
  match e with
  | Constant _ | Variable _ | Error _ | ErrorTyp _ | Ltac _ -> false
  | Tuple es | Constructor (_, _, es) | Assumption (_, _, es) | ErrorArray es ->
      any es
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
  | Assert (_, e)
  | RequiresAssumption (_, _, e)
  | PropagatedAssumption (_, _, e)
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
  | Match (scrutinee, _, cases, _)
  | MatchWithEquation (scrutinee, cases, _) ->
      has_partial_recursion scrutinee
      || any (List.map (fun (_, _, body) -> body) cases)
  | MatchExtensible (scrutinee, _, cases) ->
      has_partial_recursion scrutinee || any (List.map snd cases)
  | MatchVariant (scrutinee, _, cases) ->
      has_partial_recursion scrutinee || any (List.map snd cases)
  | Record fields | Module (_, fields) ->
      any (List.map (fun (_, _, value) -> value) fields)
  | IfThenElse (condition, then_, else_)
  | IfThenElseWithEquation (condition, then_, else_) ->
      any [ condition; then_; else_ ]

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
  | RequiresAssumption (_, _, function_) | PropagatedAssumption (_, _, function_)
    ->
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
    | value :: module_ :: _ -> (module_ ^ "." ^ value, module_ ^ "_" ^ value)
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

let is_configured_partial_expression (partial_definitions : string list) (e : t)
    : bool =
  match expression_qualified_name e with
  | Some candidate ->
      List.exists
        (configured_partial_path_matches candidate)
        partial_definitions
  | None -> false

(** Execute configured monadic sequence traversals inside a definition whose
    well-founded specification asserts totality. [Resumption.run] exposes the
    convergence proof as a [Program] obligation; it is never synthesized by the
    translator. *)
let rec rewrite_sequence_calls ~(discharge_partial : bool)
    (partial_definitions : string list) (e : t) : t =
  let recurse = rewrite_sequence_calls ~discharge_partial partial_definitions in
  let map_option f = function None -> None | Some value -> Some (f value) in
  let field base name =
    match base with
    | Variable (MixedPath.PathName { PathName.path; base }, _) ->
        Variable
          ( MixedPath.PathName
              (PathName.of_name (path @ [ base ]) (Name.of_string_raw name)),
            [] )
    | _ -> Field (base, PathName.of_name [] (Name.of_string_raw name))
  in
  let wildcard = Variable (MixedPath.of_name (Name.of_string_raw "_"), []) in
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
  let finite_range count start =
    let function_ =
      Variable
        ( MixedPath.PathName
            {
              PathName.path =
                [
                  Name.of_string_raw "RocqOfOCaml";
                  Name.of_string_raw "OCamlSeq";
                ];
              base = Name.of_string_raw "range";
            },
          [] )
    in
    Apply (function_, [ Some count; Some start ])
  in
  let finite_iteration count step start =
    let function_ =
      Variable
        ( MixedPath.PathName
            {
              PathName.path =
                [
                  Name.of_string_raw "RocqOfOCaml";
                  Name.of_string_raw "OCamlSeq";
                ];
              base = Name.of_string_raw "iterate_take";
            },
          [] )
    in
    Apply (function_, [ Some count; Some step; Some start ])
  in
  let is_seq_operation operation expression =
    match application_function_name expression with
    | Some candidate ->
        configured_partial_path_matches candidate ("Seq." ^ operation)
        || configured_partial_path_matches candidate ("OCamlSeq." ^ operation)
    | None -> false
  in
  let bounded_int_range function_ arguments =
    match (is_seq_operation "take" function_, arguments) with
    | true, [ Some count; Some sequence ] -> (
        let sequence =
          match sequence with
          | RequiresAssumption (_, _, body) | PropagatedAssumption (_, _, body)
            ->
              body
          | sequence -> sequence
        in
        match sequence with
        | (Apply (ints, [ Some start ]) | SourceApply (ints, [ Some start ], _))
          when is_seq_operation "ints" ints ->
            Some (finite_range count start)
        | _ -> None)
    | _ -> None
  in
  let bounded_iteration function_ arguments =
    match (is_seq_operation "take" function_, arguments) with
    | true, [ Some count; Some sequence ] -> (
        let sequence =
          match sequence with
          | RequiresAssumption (_, _, body) | PropagatedAssumption (_, _, body)
            ->
              body
          | sequence -> sequence
        in
        match sequence with
        | Apply (iterate, [ Some step; Some start ])
        | SourceApply (iterate, [ Some step; Some start ], _)
          when is_seq_operation "iterate" iterate ->
            Some (finite_iteration count step start)
        | _ -> None)
    | _ -> None
  in
  let rewrite_application result_typ function_ arguments =
    let rec flatten function_ arguments =
      match function_ with
      | (Apply (inner, preceding) | SourceApply (inner, preceding, _))
        when List.for_all (function None -> false | Some _ -> true) preceding ->
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
      | Variable (MixedPath.PathName { PathName.path; base = _ }, _) -> (
          match List.rev path with
          | seq :: monad_base :: rev_monad_path when Name.to_string seq = "Seq"
            ->
              let monad_path =
                MixedPath.PathName
                  (PathName.of_name (List.rev rev_monad_path) monad_base)
              in
              let monad_type_path =
                MixedPath.PathName
                  (PathName.of_name
                     (List.rev rev_monad_path @ [ monad_base ])
                     (Name.of_string_raw "t"))
              in
              Some (Variable (monad_path, []), monad_type_path)
          | _ -> None)
      | _ -> None
    in
    match bounded_int_range function_ arguments with
    | Some range -> range
    | None -> (
        match bounded_iteration function_ arguments with
        | Some iteration -> iteration
        | None -> (
            match
              ( discharge_partial && is_partial_seq_map,
                monad_of_seq_function,
                arguments )
            with
            | true, Some (monad, monad_path), [ Some _; Some _ ] ->
                let a = Name.of_string_raw "_rocq_partial_A" in
                let b = Name.of_string_raw "_rocq_partial_B" in
                let value = Name.of_string_raw "_rocq_partial_return_value" in
                let action = Name.of_string_raw "_rocq_partial_action" in
                let continuation =
                  Name.of_string_raw "_rocq_partial_continuation"
                in
                let monad_type result =
                  Type.Apply (monad_path, [ (Type.Variable result, false) ])
                in
                let typed_function name typ body =
                  Function (name, Some typ, body)
                in
                let return_operation =
                  typed_function a (Type.Kind Kind.Set)
                    (typed_function value (Type.Variable a)
                       (Apply
                          ( field monad "_return",
                            [ Some (Variable (MixedPath.of_name value, [])) ] )))
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
                                      (Variable (MixedPath.of_name action, []));
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
                    SourceApply (function_, arguments, result_typ))))
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
  | Apply (function_, arguments) -> rewrite_application None function_ arguments
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
        |> List.map (fun (header, body) -> (header, Option.map recurse body))
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
            (fun (pattern, cast, body) -> (pattern, cast, recurse body))
            cases,
          default )
  | MatchWithEquation (scrutinee, cases, default) ->
      MatchWithEquation
        ( recurse scrutinee,
          List.map
            (fun (pattern, cast, body) -> (pattern, cast, recurse body))
            cases,
          default )
  | MatchExtensible (scrutinee, typ, cases) ->
      MatchExtensible
        ( recurse scrutinee,
          typ,
          List.map (fun (pattern, body) -> (pattern, recurse body)) cases )
  | MatchVariant (scrutinee, typ, cases) ->
      MatchVariant
        ( recurse scrutinee,
          typ,
          List.map (fun (pattern, body) -> (pattern, recurse body)) cases )
  | Record fields ->
      Record
        (List.map
           (fun (name, arity, value) -> (name, arity, recurse value))
           fields)
  | Field (value, name) -> Field (recurse value, name)
  | IfThenElse (condition, then_, else_) ->
      IfThenElse (recurse condition, recurse then_, recurse else_)
  | IfThenElseWithEquation (condition, then_, else_) ->
      IfThenElseWithEquation (recurse condition, recurse then_, recurse else_)
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
  | PropagatedAssumption (kind, typ, body) ->
      PropagatedAssumption (kind, typ, recurse body)
  | ErrorArray values -> ErrorArray (List.map recurse values)
  | ErrorMessage (body, message) -> ErrorMessage (recurse body, message)

let rec has_partial_reference (partial_definitions : string list) (e : t) : bool
    =
  let any es = List.exists (has_partial_reference partial_definitions) es in
  if is_configured_partial_expression partial_definitions e then true
  else
    match e with
    | Constant _ | Error _ | ErrorTyp _ | Ltac _ | Variable _ -> false
    | Tuple es | Constructor (_, _, es) | Assumption (_, _, es) | ErrorArray es
      ->
        any es
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
    | Assert (_, e)
    | RequiresAssumption (_, _, e)
    | PropagatedAssumption (_, _, e)
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
    | Match (scrutinee, _, cases, _)
    | MatchWithEquation (scrutinee, cases, _) ->
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
    | IfThenElse (condition, then_, else_)
    | IfThenElseWithEquation (condition, then_, else_) ->
        any [ condition; then_; else_ ]

let normalize_assumption_requirement (kind, typ) =
  (kind, Type.drop_unused_forall_modules typ)

let compare_normalized_assumption_requirement :
    assumption_requirement -> assumption_requirement -> int =
 fun ((left_kind, left_typ) as left) ((right_kind, right_typ) as right) ->
  if left_kind = right_kind && left_typ == right_typ then 0
  else compare left right

let compare_assumption_requirement :
    assumption_requirement -> assumption_requirement -> int =
 fun ((left_kind, left_typ) as left) ((right_kind, right_typ) as right) ->
  if left_kind = right_kind && left_typ == right_typ then 0
  else
    compare_normalized_assumption_requirement
      (normalize_assumption_requirement left)
      (normalize_assumption_requirement right)

module NormalizedAssumptionTable = Hashtbl.Make (struct
  type t = assumption_requirement

  let equal left right =
    compare_normalized_assumption_requirement left right = 0

  (** The default polymorphic hash inspects only a bounded prefix. Generated
      module requirements often share a very long prefix, so hash the complete
      practical type tree and retain structural equality as the collision check.
  *)
  let hash (kind, typ) =
    Hashtbl.hash (kind, Hashtbl.hash_param 1_000_000 1_000_000 typ)
end)

let stable_uniq_normalized_assumptions
    (requirements : assumption_requirement list) : assumption_requirement list =
  let seen = NormalizedAssumptionTable.create (List.length requirements) in
  requirements
  |> List.fold_left
       (fun unique requirement ->
         if NormalizedAssumptionTable.mem seen requirement then unique
         else (
           NormalizedAssumptionTable.add seen requirement ();
           requirement :: unique))
       []
  |> List.rev

let sort_uniq_assumptions (requirements : assumption_requirement list) :
    assumption_requirement list =
  requirements
  |> List.map normalize_assumption_requirement
  |> stable_uniq_normalized_assumptions
  |> List.sort compare_normalized_assumption_requirement

let stable_uniq_assumptions (requirements : assumption_requirement list) :
    assumption_requirement list =
  requirements
  |> List.map normalize_assumption_requirement
  |> stable_uniq_normalized_assumptions

(** Put provider requirements before requirements whose types mention local
    generated projections. Gallina elaborates dependent binders from left to
    right, so a binder over [M.t] cannot precede the class arguments needed to
    elaborate [M]. *)
let order_assumption_binders (requirements : assumption_requirement list) :
    assumption_requirement list =
  let requirements = stable_uniq_assumptions requirements in
  let canonical =
    List.stable_sort (fun left right ->
        compare_normalized_assumption_requirement right left)
  in
  let local, providers =
    List.partition
      (fun (_, typ) -> Type.contains_local_mixed_path_root typ)
      requirements
  in
  (* Requirements can denote definitionally equal source aliases, in which
     case Rocq type-class search selects the later binder.  Canonical ordering
     makes that choice independent of call-discovery order; the dependency
     refinement below still moves actual providers ahead of their projections. *)
  canonical providers @ canonical local

(** Reinterpret the small expression fragment used for module applications as a
    Gallina term embedded in a dependent type. This is used only to preserve
    local module [let] bindings in generated assumption parameters. *)
let rec assumption_term_of_expression (expression : t) : Type.t option =
  let render typ =
    typ |> Type.to_coq None None |> SmartPrint.to_string 1_000_000 0
  in
  let record fields =
    let fields =
      fields
      |> List.map (fun (name, _, value) ->
          Option.map
            (fun value -> PathName.to_string name ^ " := " ^ render value)
            (assumption_term_of_expression value))
    in
    if List.for_all Option.is_some fields then
      Some
        (Type.Error
           ("{| "
           ^ (fields |> List.filter_map Fun.id |> String.concat "; ")
           ^ " |}"))
    else None
  in
  let rec application arguments = function
    | Apply (function_, arguments') | SourceApply (function_, arguments', _) ->
        application (arguments' @ arguments) function_
    | Variable (path, []) ->
        arguments
        |> List.map (fun argument ->
            Option.bind argument assumption_term_of_expression)
        |> fun arguments ->
        if List.for_all Option.is_some arguments then
          Some
            (Type.Apply
               ( path,
                 arguments |> List.filter_map Fun.id
                 |> List.map (fun argument -> (argument, false)) ))
        else None
    | _ -> None
  in
  match expression with
  | Variable (path, []) -> Some (Type.Apply (path, []))
  | Apply _ | SourceApply _ -> application [] expression
  | Record fields | Module (_, fields) -> record fields
  | TypAnnotation (value, typ) ->
      Option.map
        (fun value ->
          Type.Error ("(" ^ render value ^ " : " ^ render typ ^ ")"))
        (assumption_term_of_expression value)
  | Cast (value, _)
  | RequiresAssumption (_, _, value)
  | PropagatedAssumption (_, _, value)
  | ErrorMessage (value, _) ->
      assumption_term_of_expression value
  | LetVar (_, name, [], value, body) ->
      Option.bind (assumption_term_of_expression value) (fun value ->
          Option.map
            (fun body -> Type.Let (name, value, body))
            (assumption_term_of_expression body))
  | _ -> None

(** Specialize generated type paths that escape through a local binding of an
    applied functor. Call-requirement propagation runs after module coercion, so
    this must happen while collecting the final requirements rather than only
    when the coercion expression is first constructed. *)
let specialize_assumption_for_application ?local_result (value : t)
    (result : Type.t) : Type.t =
  let application_term = assumption_term_of_expression value in
  let result =
    match (local_result, application_term) with
    | ( Some local_result,
        Some (Type.Apply (MixedPath.PathName functor_path, arguments)) )
      when arguments <> [] ->
        let arguments =
          arguments
          |> List.map (fun (argument, _) ->
              ( "",
                argument |> Type.to_coq None None
                |> SmartPrint.to_string 1_000_000 0 ))
        in
        Type.subst_mixed_path_root local_result
          (MixedPath.AppliedAccess (functor_path, arguments, []))
          result
    | _, _ -> result
  in
  let result =
    match value with
    | SourceApply (_, _, source_type) ->
        List.fold_left
          (fun result (source, target) ->
            Type.specialize_matched_type ~relaxed_constructors:true
              ~preserve_pattern_constructor:(fun _ -> false)
              source target result
            |> Option.value ~default:result)
          result source_type.module_substitutions
    | _ -> result
  in
  match application_term with
  | Some (Type.Apply (MixedPath.PathName functor_path, (_ :: _ as arguments)))
    ->
      let functor_names =
        functor_path.PathName.path @ [ functor_path.PathName.base ]
      in
      let build_fargs_path =
        {
          PathName.path = functor_names;
          base = Name.of_string_raw "Build_FArgs";
        }
      in
      let fargs =
        Type.Apply (MixedPath.PathName build_fargs_path, arguments)
        |> Type.to_coq None None
        |> SmartPrint.to_string 1_000_000 0
      in
      let application =
        arguments
        |> List.map (fun (argument, _) ->
            argument |> Type.to_coq None None
            |> SmartPrint.to_string 1_000_000 0)
      in
      Type.specialize_functor_paths ~application functor_names fargs result
  | _ -> result

(** If [value] is a functor application, project its internal generated type
    paths through the local result record bound by [name]. *)
let functor_application_head (value : t) : PathName.t option =
  let rec head = function
    | Apply (function_, _) | SourceApply (function_, _, _) -> head function_
    | TypAnnotation (function_, _)
    | Cast (function_, _)
    | ErrorMessage (function_, _) ->
        head function_
    | Variable (MixedPath.PathName path, []) -> Some path
    | _ -> None
  in
  head value

let existential_cast_value_type
    ({ new_typ_vars; bound_vars; _ } : match_existential_cast) : Type.t =
  let value_type =
    match List.map snd bound_vars with
    | [] -> Type.Apply (MixedPath.of_name (Name.of_string_raw "unit"), [])
    | [ typ ] -> typ
    | typs -> Type.Tuple typs
  in
  match new_typ_vars with
  | [] -> value_type
  | [ (name, Kind.Set) ] ->
      let safe_name =
        if String.starts_with ~prefix:"_" (Name.to_string name) then
          Name.of_string_raw "Rocq_existential"
        else name
      in
      let value_type =
        Type.subst_variables [ (name, Type.Variable safe_name) ] value_type
      in
      Type.Apply
        ( MixedPath.of_name (Name.of_string_raw "sigT"),
          [ (Type.FunTyps ([ safe_name ], value_type), false) ] )
  | _ :: _ ->
      failwith
        "an assumed existential package currently supports one Set witness"

(** Collect every trusted result requested by an expression. The result is used
    both to add polymorphic class parameters and to emit concrete, type-specific
    instances next to the translated definition. *)
let rec assumption_requirements (e : t) : assumption_requirement list =
  let collect es = List.concat_map assumption_requirements es in
  let collect_cases cases =
    cases
    |> List.concat_map (fun (_, existential_cast, body) ->
        let cast_requirements =
          match existential_cast with
          | Some
              ({
                 use_axioms = true;
                 enable = true;
                 cast_result;
                 return_typ;
                 bound_vars;
                 _;
               } as existential_cast) ->
              (if cast_result then [ (Unreachable, return_typ) ] else [])
              @
              if bound_vars = [] then []
              else
                [ (Unreachable, existential_cast_value_type existential_cast) ]
          | Some { cast_result = true; return_typ; _ } ->
              [ (Unreachable, return_typ) ]
          | Some _ | None -> []
        in
        cast_requirements @ assumption_requirements body)
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
  | TypAnnotation (e, _)
  | ErrorMessage (e, _) ->
      assumption_requirements e
  | Cast (e, typ) -> (Unreachable, typ) :: assumption_requirements e
  | Functor (name, parameter, body) ->
      assumption_requirements body
      |> List.map (fun (kind, result) ->
          (kind, Type.ForallModule (name, parameter, result)))
  | ConstructorVariant (_, None) -> []
  | ConstructorVariant (_, Some (_, e)) -> assumption_requirements e
  | Apply (f, args) | SourceApply (f, args, _) ->
      collect (f :: List.filter_map (fun argument -> argument) args)
  | InfixOperator (_, left, right) -> collect [ left; right ]
  | LetVar (_, name, _, value, body) ->
      let value_requirements = assumption_requirements value in
      let body_requirements = assumption_requirements body in
      let result_modules =
        match functor_application_head value with
        | Some functor_path ->
            body_requirements
            |> List.fold_left
                 (fun modules (_, result) ->
                   Name.Set.union modules
                     (Type.functor_accessed_modules functor_path result))
                 Name.Set.empty
        | None -> Name.Set.empty
      in
      let body_requirements =
        body_requirements
        |> List.map (fun (kind, result) ->
            let specialized =
              specialize_assumption_for_application ~local_result:name value
                result
            in
            let result =
              if compare specialized result <> 0 then specialized
              else
                match functor_application_head value with
                | Some functor_path ->
                    Type.project_functor_paths_to_result functor_path
                      result_modules name result
                | None -> result
            in
            (kind, result))
      in
      let body_requirements =
        match assumption_term_of_expression value with
        | None -> body_requirements
        | Some value ->
            body_requirements
            |> List.map (fun (kind, result) ->
                if Type.references_mixed_path_root name result then
                  (kind, Type.Let (name, value, result))
                else (kind, result))
      in
      value_requirements @ body_requirements
  | LetFun (definition, body) ->
      let definition_bodies =
        definition.cases |> List.filter_map (fun (_, body) -> body)
      in
      collect (body :: definition_bodies)
  | Match (scrutinee, _, cases, _)
  | MatchWithEquation (scrutinee, cases, _) ->
      assumption_requirements scrutinee @ collect_cases cases
  | MatchExtensible (scrutinee, result_typ, cases) ->
      let propagated_exception =
        if List.exists (fun (pattern, _) -> Option.is_none pattern) cases then
          []
        else [ (Unreachable, result_typ) ]
      in
      let payload_requirements =
        cases
        |> List.filter_map (function
          | Some (_, Pattern.Tuple [], _), _ | None, _ -> None
          | Some (_, _, typ), _ -> Some (Unreachable, typ))
      in
      assumption_requirements scrutinee
      @ collect (List.map snd cases)
      @ payload_requirements @ propagated_exception
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
      let payload_requirements =
        cases
        |> List.filter_map (function
          | Pattern.VariantCase (_, Pattern.Tuple [], _, _), _
          | Pattern.VariantDefault _, _ ->
              None
          | Pattern.VariantCase (_, _, typ, _), _ -> Some (Unreachable, typ))
      in
      assumption_requirements scrutinee
      @ collect (List.map snd cases)
      @ payload_requirements @ default
  | Record fields | Module (_, fields) ->
      collect (List.map (fun (_, _, value) -> value) fields)
  | IfThenElse (condition, then_, else_)
  | IfThenElseWithEquation (condition, then_, else_) ->
      collect [ condition; then_; else_ ]
  | Assert (typ, condition) ->
      (Unreachable, typ) :: assumption_requirements condition
  | Assumption (kind, typ, arguments) -> (kind, typ) :: collect arguments
  | RequiresAssumption (kind, typ, body) ->
      (kind, typ) :: assumption_requirements body
  | PropagatedAssumption (kind, typ, body) ->
      (kind, typ) :: assumption_requirements body

let assumption_requirements_raw = assumption_requirements

(** Normalize requirements after call propagation has finished. Structure
    closing can move requirements outside local module bindings, so repeat the
    OCaml-checked functor substitutions from those bindings before exposing the
    final requirement set. *)
let assumption_specializers ?external_fargs (expression : t) :
    (Type.t -> Type.t) list =
  let rec collect_specializers expression =
    let collect expressions =
      List.concat_map collect_specializers expressions
    in
    match expression with
    | Constant _ | Variable _ | Error _ | ErrorTyp _ | Ltac _ -> []
    | Tuple values | ErrorArray values -> collect values
    | Constructor (_, _, values) -> collect values
    | ConstructorExtensible (_, _, value)
    | ConstructorVariant (_, Some (_, value))
    | Return (_, value)
    | Function (_, _, value)
    | Functions (_, value)
    | LetTyp (_, _, _, value)
    | LetModuleUnpack (_, _, value)
    | Field (value, _)
    | ModulePack (_, value)
    | Cast (value, _)
    | TypAnnotation (value, _)
    | Assert (_, value)
    | RequiresAssumption (_, _, value)
    | PropagatedAssumption (_, _, value)
    | ErrorMessage (value, _) ->
        collect_specializers value
    | ConstructorVariant (_, None) -> []
    | Apply (function_, arguments) ->
        collect (function_ :: List.filter_map Fun.id arguments)
    | SourceApply (function_, arguments, source_type) ->
        let externalize_module_substitution source target =
          let target_is_local_associated_type =
            match target with
            | Type.Variable _ -> true
            | Type.Apply
                ( ( MixedPath.PathName { PathName.path = []; _ }
                  | MixedPath.Access ({ PathName.path = []; _ }, _)
                  | MixedPath.AppliedAccess ({ PathName.path = []; _ }, _, _) ),
                  _ ) ->
                true
            | _ -> false
          in
          match
            ( target_is_local_associated_type,
              external_fargs,
              functor_application_head expression,
              source )
          with
          | ( true,
              Some fargs_name,
              Some { PathName.path = functor_module_path; base = functor_name },
              Type.Apply
                ( MixedPath.Access
                    ({ PathName.path = []; base = module_name }, fields),
                  arguments ) ) ->
              let container =
                match List.rev functor_module_path with
                | module_base :: reversed_path
                  when String.equal (Name.to_string functor_name) "functor" ->
                    {
                      PathName.path = List.rev reversed_path;
                      base = module_base;
                    }
                | _ ->
                    { PathName.path = functor_module_path; base = functor_name }
              in
              let module_field =
                {
                  PathName.path = container.PathName.path @ [ container.base ];
                  base = module_name;
                }
              in
              let fargs_module =
                MixedPath.Access
                  ( { PathName.path = []; base = fargs_name },
                    module_field
                    :: List.map
                         (fun field ->
                           if
                             List.length field.PathName.path
                             >= List.length container.PathName.path
                             && List.for_all2 Name.equal container.PathName.path
                                  (List.take
                                     (List.length container.PathName.path)
                                     field.PathName.path)
                           then field
                           else
                             {
                               field with
                               PathName.path =
                                 container.PathName.path @ field.PathName.path;
                             })
                         fields )
              in
              Type.Apply (fargs_module, arguments)
          | _ -> target
        in
        let module_specializer typ =
          List.fold_left
            (fun typ (source, target) ->
              let target = externalize_module_substitution source target in
              Type.specialize_matched_type ~relaxed_constructors:true
                ~preserve_pattern_constructor:(fun _ -> false)
                source target typ
              |> Option.value ~default:typ)
            typ source_type.module_substitutions
        in
        module_specializer
        :: collect (function_ :: List.filter_map Fun.id arguments)
    | InfixOperator (_, left, right) -> collect [ left; right ]
    | LetVar (_, name, _, value, body) ->
        let local_specializers =
          if String.starts_with ~prefix:"opened_module_" (Name.to_string name)
          then
            [ specialize_assumption_for_application ~local_result:name value ]
          else []
        in
        local_specializers @ collect_specializers value
        @ collect_specializers body
    | LetFun (definition, body) ->
        collect
          (body :: (definition.cases |> List.filter_map (fun (_, body) -> body)))
    | Match (scrutinee, _, cases, _)
    | MatchWithEquation (scrutinee, cases, _) ->
        collect (scrutinee :: List.map (fun (_, _, body) -> body) cases)
    | MatchExtensible (scrutinee, _, cases) ->
        collect (scrutinee :: List.map snd cases)
    | MatchVariant (scrutinee, _, cases) ->
        collect (scrutinee :: List.map snd cases)
    | Record fields | Module (_, fields) ->
        collect (List.map (fun (_, _, value) -> value) fields)
    | IfThenElse (condition, then_, else_) ->
        collect [ condition; then_; else_ ]
    | IfThenElseWithEquation (condition, then_, else_) ->
        collect [ condition; then_; else_ ]
    | Functor (_, _, body) -> collect_specializers body
    | Assumption (_, _, arguments) -> collect arguments
  in
  collect_specializers expression

let specialize_assumption_type ?external_fargs (expression : t) (typ : Type.t) :
    Type.t =
  assumption_specializers ?external_fargs expression
  |> List.fold_left (fun typ specialize -> specialize typ) typ

let specialize_assumption_requirements ?external_fargs (expression : t)
    (requirements : assumption_requirement list) : assumption_requirement list =
  requirements
  |> List.map (fun (kind, typ) ->
      (kind, specialize_assumption_type ?external_fargs expression typ))

let assumption_requirements (expression : t) : assumption_requirement list =
  assumption_requirements_raw expression
  |> specialize_assumption_requirements expression

let assumption_class_type ((kind, typ) : assumption_requirement) : Type.t =
  match kind with
  | ModuleContext -> typ
  | Unreachable | Unimplemented ->
      let class_name =
        match kind with
        | Unreachable -> "Unreachable"
        | Unimplemented -> "Unimplemented"
        | ModuleContext -> assert false
      in
      let class_path =
        MixedPath.PathName
          {
            PathName.path =
              [ Name.of_string_raw "RocqOfOCaml"; Name.of_string_raw "Basics" ];
            base = Name.of_string_raw class_name;
          }
      in
      Type.Apply (class_path, [ (typ, false) ])

let rec assumption_requirement_of_class_type (typ : Type.t) :
    assumption_requirement option =
  match typ with
  | Type.ForallModule (name, parameter, result) ->
      assumption_requirement_of_class_type result
      |> Option.map (fun (kind, result) ->
          (kind, Type.ForallModule (name, parameter, result)))
  | Type.Let (name, value, result) ->
      assumption_requirement_of_class_type result
      |> Option.map (fun (kind, result) ->
          (kind, Type.Let (name, value, result)))
  | Type.Apply (MixedPath.PathName { PathName.base; _ }, [ (result_typ, _) ])
    -> (
      match Name.to_string base with
      | "Unreachable" -> Some (Unreachable, result_typ)
      | "Unimplemented" -> Some (Unimplemented, result_typ)
      | _ -> None)
  | Type.Apply (MixedPath.PathName { PathName.base; _ }, [])
    when String.equal (Name.to_string base) "FArgs" ->
      Some (ModuleContext, typ)
  | _ -> None

let concrete_assumption_requirements (_e : t) : assumption_requirement list = []

(** Turn a scoped assumption family from a definition binder into ordinary local
    class instances under the corresponding functor lambdas. Rocq's typeclass
    search uses the resulting [let]-bound class values, whereas it does not
    apply a hypothesis whose head is a dependent [forall] automatically. *)
let materialize_scoped_assumptions
    (assumptions : (Name.t * assumption_requirement) list) (expression : t) : t
    =
  let local_name binder =
    Name.of_string_raw ("_rocq_local_" ^ Name.to_string binder)
  in
  let variable name = Variable (MixedPath.of_name name, []) in
  let specialize kind provider argument =
    match kind with
    | ModuleContext -> Apply (provider, [ Some argument ])
    | Unreachable | Unimplemented ->
        let helper =
          match kind with
          | Unreachable -> "specialize_unreachable"
          | Unimplemented -> "specialize_unimplemented"
          | ModuleContext -> assert false
        in
        Apply
          ( Variable (MixedPath.of_name (Name.of_string_raw helper), []),
            [ Some provider; Some argument ] )
  in
  let rec install kind provider local requirement expression =
    match (requirement, expression) with
    | Type.ForallModule (expected, _, result), Functor (name, typ, body)
      when Name.equal expected name ->
        let provider = specialize kind provider (variable name) in
        let body =
          match result with
          | Type.ForallModule _ -> install kind provider local result body
          | _ -> LetVar (None, local, [], provider, body)
        in
        Functor (name, typ, body)
    | requirement, TypAnnotation (body, typ) ->
        TypAnnotation (install kind provider local requirement body, typ)
    | requirement, Cast (body, typ) ->
        Cast (install kind provider local requirement body, typ)
    | requirement, ErrorMessage (body, message) ->
        ErrorMessage (install kind provider local requirement body, message)
    | requirement, RequiresAssumption (required_kind, typ, body) ->
        RequiresAssumption
          (required_kind, typ, install kind provider local requirement body)
    | requirement, PropagatedAssumption (required_kind, typ, body) ->
        PropagatedAssumption
          (required_kind, typ, install kind provider local requirement body)
    | requirement, Return (operator, body) ->
        Return (operator, install kind provider local requirement body)
    | requirement, Apply (function_, arguments) ->
        Apply
          ( install kind provider local requirement function_,
            List.map
              (Option.map (install kind provider local requirement))
              arguments )
    | requirement, SourceApply (function_, arguments, result_typ) ->
        SourceApply
          ( install kind provider local requirement function_,
            List.map
              (Option.map (install kind provider local requirement))
              arguments,
            result_typ )
    | requirement, Tuple values ->
        Tuple (List.map (install kind provider local requirement) values)
    | requirement, Constructor (name, implicits, values) ->
        Constructor
          ( name,
            implicits,
            List.map (install kind provider local requirement) values )
    | requirement, Record fields ->
        Record
          (List.map
             (fun (name, arity, value) ->
               (name, arity, install kind provider local requirement value))
             fields)
    | requirement, Module (typ, fields) ->
        Module
          ( typ,
            List.map
              (fun (name, arity, value) ->
                (name, arity, install kind provider local requirement value))
              fields )
    | requirement, LetVar (operator, name, typ_vars, value, body) ->
        LetVar
          ( operator,
            name,
            typ_vars,
            install kind provider local requirement value,
            install kind provider local requirement body )
    | _ -> expression
  in
  List.fold_left
    (fun expression (binder, (kind, requirement)) ->
      match requirement with
      | Type.ForallModule _ ->
          install kind (variable binder) (local_name binder) requirement
            expression
      | _ -> expression)
    expression assumptions

(** A bare reference to a translated module value looks like an ordinary Gallina
    function application after module erasure, but its generated class binders
    use the [_rocq_module_assumption_N] namespace. Preserve that distinction
    until direct assumption applications are materialized. The marker is
    translator-internal and is always removed before emission. *)
let module_reference_marker = "_rocq_internal_module_reference"

let rec mark_module_reference = function
  | Variable (path, implicits) ->
      let implicits =
        if
          List.exists
            (fun (name, _) -> String.equal name module_reference_marker)
            implicits
        then implicits
        else (module_reference_marker, "") :: implicits
      in
      Variable (path, implicits)
  | Apply (head, arguments) -> Apply (mark_module_reference head, arguments)
  | SourceApply (head, arguments, source_type) ->
      SourceApply (mark_module_reference head, arguments, source_type)
  | TypAnnotation (head, typ) -> TypAnnotation (mark_module_reference head, typ)
  | Cast (head, typ) -> Cast (mark_module_reference head, typ)
  | ErrorMessage (head, message) ->
      ErrorMessage (mark_module_reference head, message)
  | RequiresAssumption (kind, typ, head) ->
      RequiresAssumption (kind, typ, mark_module_reference head)
  | PropagatedAssumption (kind, typ, head) ->
      PropagatedAssumption (kind, typ, mark_module_reference head)
  | expression -> expression

(** Supply ordinary (non-functor-scoped) exceptional assumptions explicitly at
    translated call sites. Keeping these applications explicit avoids relying on
    type-class conversion through large generated module aliases. *)
let materialize_direct_assumptions ?(projected_only = false)
    ?(excluded_heads = Name.Set.empty)
    ?(projected_root_requirements = fun (_ : MixedPath.t) -> [])
    ?(order_source_requirements = fun (_ : t) requirements -> requirements)
    ?(requirements_match =
      fun left right -> compare_assumption_requirement left right = 0)
    (assumptions : (Name.t * assumption_requirement) list) (expression : t) : t
    =
  let provider requirement =
    assumptions
    |> List.find_map (fun (name, candidate) ->
        if requirements_match candidate requirement then Some name else None)
  in
  let requirements_with_providers requirements =
    requirements
    |> List.fold_left
         (fun result requirement ->
           match (result, provider requirement) with
           | Some requirements, Some provider ->
               Some (requirements @ [ (requirement, provider) ])
           | Some _, None | None, _ -> None)
         (Some [])
  in
  let head_is_excluded head =
    let head = Name.to_string head |> String.lowercase_ascii in
    Name.Set.exists
      (fun excluded ->
        String.equal head (Name.to_string excluded |> String.lowercase_ascii))
      excluded_heads
  in
  let applications_of ~module_reference requirements =
    requirements
    |> List.mapi (fun index (_, provider) ->
        let prefix =
          if
            module_reference
            && String.starts_with ~prefix:"_rocq_module_assumption_"
                 (Name.to_string provider)
          then "_rocq_module_assumption_"
          else "_rocq_assumption_"
        in
        (prefix ^ string_of_int index, Name.to_string provider))
  in
  let requirement_is_in candidates (requirement, _) =
    List.exists
      (fun candidate -> requirements_match candidate requirement)
      candidates
  in
  let take_module_reference_marker implicits =
    let marked, implicits =
      List.partition
        (fun (name, _) -> String.equal name module_reference_marker)
        implicits
    in
    (marked <> [], implicits)
  in
  let projection_applications path requirements =
    let root_requirements = projected_root_requirements path in
    let _, projected =
      List.partition (requirement_is_in root_requirements) requirements
    in
    (* Rocq sections omit unused context variables, so the names and positions
       of a module value's generalized arguments cannot be reconstructed from
       its pre-generalization requirement list.  Leave those arguments to
       type-class inference and materialize only the selected field's own
       telescope. *)
    applications_of ~module_reference:false projected
  in
  let add_applications requirements = function
    | Variable (MixedPath.PathName root, implicits)
      when (not projected_only) && not (head_is_excluded root.PathName.base) ->
        let module_reference, implicits =
          take_module_reference_marker implicits
        in
        let applications = applications_of ~module_reference requirements in
        Some
          (Variable (MixedPath.AppliedAccess (root, applications, []), implicits))
    | Variable (MixedPath.AppliedAccess (root, existing, []), implicits)
      when (not projected_only) && not (head_is_excluded root.PathName.base) ->
        let module_reference, implicits =
          take_module_reference_marker implicits
        in
        let applications = applications_of ~module_reference requirements in
        Some
          (Variable
             ( MixedPath.AppliedAccess (root, existing @ applications, []),
               implicits ))
    | Variable (MixedPath.Access (root, fields), implicits) ->
        let path = MixedPath.Access (root, fields) in
        let projected_applications =
          projection_applications path requirements
        in
        Some (Variable (path, implicits @ projected_applications))
    | Variable
        (MixedPath.AppliedAccess (root, existing, (_ :: _ as fields)), implicits)
      ->
        let path = MixedPath.AppliedAccess (root, existing, fields) in
        let projected_applications =
          projection_applications path requirements
        in
        Some (Variable (path, implicits @ projected_applications))
    | Field (Variable (path, implicits), field) ->
        let projected =
          match path with
          | MixedPath.PathName root -> MixedPath.Access (root, [ field ])
          | MixedPath.Access (root, fields) ->
              MixedPath.Access (root, fields @ [ field ])
          | MixedPath.AppliedAccess (root, applications, fields) ->
              MixedPath.AppliedAccess (root, applications, fields @ [ field ])
        in
        let projected_applications =
          projection_applications projected requirements
        in
        Some (Variable (projected, implicits @ projected_applications))
    | Variable (MixedPath.PathName _, _)
    | Variable (MixedPath.AppliedAccess (_, _, _), _)
    | Constant _ | Tuple _ | Constructor _ | ConstructorExtensible _
    | ConstructorVariant _ | Apply _ | SourceApply _ | Return _
    | InfixOperator _ | Function _ | Functions _ | LetVar _ | LetFun _
    | LetTyp _ | LetModuleUnpack _ | Match _ | MatchWithEquation _
    | MatchExtensible _
    | MatchVariant _ | Record _ | IfThenElse _ | IfThenElseWithEquation _
    | Module _ | ModulePack _ | Functor _ | Field _ | Cast _ | TypAnnotation _
    | Assert _ | Assumption _ | RequiresAssumption _ | PropagatedAssumption _
    | Error _ | ErrorArray _ | ErrorTyp _ | ErrorMessage _ | Ltac _ ->
        None
  in
  let direct_materialization_enabled = ref true in
  let order_requirements head requirements =
    let ordered =
      order_source_requirements head (List.map fst requirements)
      |> List.filter_map (fun requirement ->
          requirements
          |> List.find_opt (fun (candidate, _) ->
              compare_assumption_requirement candidate requirement = 0))
    in
    if List.length ordered = List.length requirements then ordered
    else requirements
  in
  let rec recurse expression =
    let rec collect requirements = function
      | RequiresAssumption (kind, typ, body)
      | PropagatedAssumption (kind, typ, body) -> (
          let requirement = (kind, typ) in
          match provider requirement with
          | Some provider ->
              collect ((requirement, provider) :: requirements) body
          | None -> (List.rev requirements, body))
      | body -> (List.rev requirements, body)
    in
    let requirements, body = collect [] expression in
    if requirements <> [] then
      let requirements =
        requirements
        |> List.fold_left
             (fun unique ((requirement, _) as candidate) ->
               if
                 List.exists
                   (fun (existing, _) ->
                     compare_assumption_requirement existing requirement = 0)
                   unique
               then unique
               else unique @ [ candidate ])
             []
      in
      let preserve_wrapper () =
        match expression with
        | RequiresAssumption (kind, typ, body) ->
            RequiresAssumption (kind, typ, recurse body)
        | PropagatedAssumption (kind, typ, body) ->
            PropagatedAssumption (kind, typ, recurse body)
        | _ -> recurse body
      in
      if not !direct_materialization_enabled then preserve_wrapper ()
      else
        match body with
        | Apply (head, arguments) -> (
            let head = recurse head in
            let requirements = order_requirements head requirements in
            match add_applications requirements head with
            | Some head -> Apply (head, List.map (Option.map recurse) arguments)
            | None -> preserve_wrapper ())
        | SourceApply (head, arguments, result_typ) -> (
            let head = recurse head in
            let requirements = order_requirements head requirements in
            match add_applications requirements head with
            | Some head ->
                SourceApply
                  (head, List.map (Option.map recurse) arguments, result_typ)
            | None -> preserve_wrapper ())
        | Variable _ -> (
            let requirements = order_requirements body requirements in
            match add_applications requirements body with
            | Some body -> body
            | None -> preserve_wrapper ())
        | _ -> preserve_wrapper ()
    else
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
      | Apply (head, arguments) ->
          Apply (recurse head, List.map (Option.map recurse) arguments)
      | SourceApply (head, arguments, result_typ) ->
          let head = recurse head in
          let arguments = List.map (Option.map recurse) arguments in
          let materialized =
            Option.map
              (order_source_requirements head)
              result_typ.assumption_telescope
            |> fun requirements ->
            Option.bind requirements requirements_with_providers
            |> fun requirements ->
            Option.bind requirements (fun requirements ->
                if requirements = [] then None
                else add_applications requirements head)
          in
          SourceApply
            (Option.value materialized ~default:head, arguments, result_typ)
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
                (fun (pattern, cast, body) -> (pattern, cast, recurse body))
                cases,
              default )
      | MatchWithEquation (scrutinee, cases, default) ->
          MatchWithEquation
            ( recurse scrutinee,
              List.map
                (fun (pattern, cast, body) -> (pattern, cast, recurse body))
                cases,
              default )
      | MatchExtensible (scrutinee, typ, cases) ->
          MatchExtensible
            ( recurse scrutinee,
              typ,
              List.map (fun (pattern, body) -> (pattern, recurse body)) cases )
      | MatchVariant (scrutinee, typ, cases) ->
          MatchVariant
            ( recurse scrutinee,
              typ,
              List.map (fun (pattern, body) -> (pattern, recurse body)) cases )
      | Record fields ->
          Record
            (List.map
               (fun (name, arity, value) -> (name, arity, recurse value))
               fields)
      | Field (value, name) -> Field (recurse_projection value, name)
      | IfThenElse (condition, then_, else_) ->
          IfThenElse (recurse condition, recurse then_, recurse else_)
      | IfThenElseWithEquation (condition, then_, else_) ->
          IfThenElseWithEquation
            (recurse condition, recurse then_, recurse else_)
      | Module (typ, fields) ->
          Module
            ( typ,
              List.map
                (fun (name, arity, value) -> (name, arity, recurse value))
                fields )
      | ModulePack (arity, value) -> ModulePack (arity, recurse value)
      | Functor (name, typ, body) ->
          Functor (name, typ, recurse_without_direct body)
      | Cast (value, typ) -> Cast (recurse value, typ)
      | TypAnnotation (value, typ) -> TypAnnotation (recurse value, typ)
      | Assert (typ, condition) -> Assert (typ, recurse condition)
      | Assumption (kind, typ, arguments) ->
          Assumption (kind, typ, List.map recurse arguments)
      | RequiresAssumption (kind, typ, body) ->
          RequiresAssumption (kind, typ, recurse body)
      | PropagatedAssumption (kind, typ, body) ->
          PropagatedAssumption (kind, typ, recurse body)
      | ErrorArray values -> ErrorArray (List.map recurse values)
      | ErrorMessage (body, message) -> ErrorMessage (recurse body, message)
  and recurse_projection expression = recurse_without_direct expression
  and recurse_without_direct expression =
    let previous = !direct_materialization_enabled in
    direct_materialization_enabled := false;
    let result = recurse expression in
    direct_materialization_enabled := previous;
    result
  in
  let rec strip_outer_canonical seen = function
    | PropagatedAssumption (kind, typ, body) as expression ->
        let requirement = (kind, typ) in
        (* Structure closing adds one canonical copy of every requirement at
           the root.  Remove only that copy; a repeated marker belongs to the
           root call itself, and nested markers identify their consuming calls. *)
        if
          Option.is_some (provider requirement)
          && not
               (List.exists
                  (fun existing ->
                    compare_assumption_requirement existing requirement = 0)
                  seen)
        then strip_outer_canonical (requirement :: seen) body
        else expression
    | expression -> expression
  in
  recurse (strip_outer_canonical [] expression)

(** Rewrite only the types that participate in generated assumption
    requirements. Structure-level alias normalization uses this before
    propagating requirements, so a private manifest type and its public alias
    cannot become two class parameters for the same exceptional path. *)
let rec map_assumption_types (map_typ : Type.t -> Type.t) (expression : t) : t =
  let map_option f = Option.map f in
  let map = map_assumption_types map_typ in
  match expression with
  | Constant _ | Variable _ | Error _ | ErrorTyp _ | Ltac _ -> expression
  | Tuple values -> Tuple (List.map map values)
  | Constructor (name, implicits, values) ->
      Constructor (name, implicits, List.map map values)
  | ConstructorExtensible (tag, typ, value) ->
      ConstructorExtensible (tag, typ, map value)
  | ConstructorVariant (tag, value) ->
      ConstructorVariant
        (tag, Option.map (fun (typ, value) -> (typ, map value)) value)
  | Apply (function_, arguments) ->
      Apply (map function_, List.map (map_option map) arguments)
  | SourceApply (function_, arguments, result_typ) ->
      SourceApply
        ( map function_,
          List.map (map_option map) arguments,
          {
            callee = map_typ result_typ.callee;
            result = map_typ result_typ.result;
            specialization = map_typ result_typ.specialization;
            module_substitutions =
              List.map
                (fun (source, target) -> (map_typ source, map_typ target))
                result_typ.module_substitutions;
            module_assumption_telescope =
              Option.map
                (List.map (fun (kind, typ) -> (kind, map_typ typ)))
                result_typ.module_assumption_telescope;
            assumption_telescope =
              Option.map
                (List.map (fun (kind, typ) -> (kind, map_typ typ)))
                result_typ.assumption_telescope;
          } )
  | Return (operator, value) -> Return (operator, map value)
  | InfixOperator (operator, left, right) ->
      InfixOperator (operator, map left, map right)
  | Function (name, typ, body) -> Function (name, typ, map body)
  | Functions (names, body) -> Functions (names, map body)
  | LetVar (operator, name, parameters, value, body) ->
      LetVar (operator, name, parameters, map value, map body)
  | LetFun (definition, body) ->
      LetFun (map_definition_assumption_types map_typ definition, map body)
  | LetTyp (name, parameters, typ, body) ->
      LetTyp (name, parameters, typ, map body)
  | LetModuleUnpack (name, path, body) -> LetModuleUnpack (name, path, map body)
  | Match (scrutinee, dependent, cases, default) ->
      Match
        ( map scrutinee,
          dependent,
          List.map
            (fun (pattern, cast, body) -> (pattern, cast, map body))
            cases,
          default )
  | MatchWithEquation (scrutinee, cases, default) ->
      MatchWithEquation
        ( map scrutinee,
          List.map (fun (pattern, cast, body) -> (pattern, cast, map body)) cases,
          default )
  | MatchExtensible (scrutinee, result_typ, cases) ->
      MatchExtensible
        ( map scrutinee,
          map_typ result_typ,
          List.map (fun (pattern, body) -> (pattern, map body)) cases )
  | MatchVariant (scrutinee, result_typ, cases) ->
      MatchVariant
        ( map scrutinee,
          map_typ result_typ,
          List.map (fun (pattern, body) -> (pattern, map body)) cases )
  | Record fields ->
      Record
        (List.map (fun (name, arity, value) -> (name, arity, map value)) fields)
  | Field (value, name) -> Field (map value, name)
  | IfThenElse (condition, then_, else_) ->
      IfThenElse (map condition, map then_, map else_)
  | IfThenElseWithEquation (condition, then_, else_) ->
      IfThenElseWithEquation (map condition, map then_, map else_)
  | Module (typ, fields) ->
      Module
        ( typ,
          List.map (fun (name, arity, value) -> (name, arity, map value)) fields
        )
  | ModulePack (arity, value) -> ModulePack (arity, map value)
  | Functor (name, typ, body) -> Functor (name, typ, map body)
  | Cast (value, typ) -> Cast (map value, typ)
  | TypAnnotation (value, typ) -> TypAnnotation (map value, typ)
  | Assert (result_typ, condition) -> Assert (map_typ result_typ, map condition)
  | Assumption (kind, result_typ, arguments) ->
      Assumption (kind, map_typ result_typ, List.map map arguments)
  | RequiresAssumption (kind, result_typ, body) ->
      RequiresAssumption (kind, map_typ result_typ, map body)
  | PropagatedAssumption (kind, result_typ, body) ->
      PropagatedAssumption (kind, map_typ result_typ, map body)
  | ErrorArray values -> ErrorArray (List.map map values)
  | ErrorMessage (body, message) -> ErrorMessage (map body, message)

and map_definition_assumption_types (map_typ : Type.t -> Type.t)
    (definition : t option Definition.t) : t option Definition.t =
  let map_instance_typ typ =
    match assumption_requirement_of_class_type typ with
    | Some (kind, result_typ) -> assumption_class_type (kind, map_typ result_typ)
    | None -> typ
  in
  {
    definition with
    Definition.cases =
      definition.cases
      |> List.map (fun (header, body) ->
          ( {
              header with
              Header.instance_args =
                List.map
                  (fun (name, typ) -> (name, map_instance_typ typ))
                  header.Header.instance_args;
            },
            Option.map (map_assumption_types map_typ) body ));
  }

(** Rewrite every translated type annotation in a definition. This is kept
    separate from [map_definition_assumption_types], whose propagation-time
    callers intentionally touch only exceptional requirements. *)
let rec map_types_and_paths ?(map_implicit_value = Fun.id)
    ?(map_variable_implicits = fun _ implicits -> implicits)
    (map_typ : Type.t -> Type.t) (map_path : MixedPath.t -> MixedPath.t)
    (expression : t) : t =
  let map =
    map_types_and_paths ~map_implicit_value ~map_variable_implicits map_typ
      map_path
  in
  let map_implicits =
    List.map (fun (name, value) -> (name, map_implicit_value value))
  in
  let map_option = Option.map map in
  let map_cast cast =
    {
      cast with
      bound_vars =
        List.map (fun (name, typ) -> (name, map_typ typ)) cast.bound_vars;
      return_typ = map_typ cast.return_typ;
    }
  in
  let map_dependent dependent =
    {
      cast = map_typ dependent.cast;
      motive = map_typ dependent.motive;
      args = List.map map_typ dependent.args;
    }
  in
  match expression with
  | Constant _ | Error _ -> expression
  | Variable (path, implicits) ->
      Variable
        (map_path path, map_variable_implicits path (map_implicits implicits))
  | ErrorTyp typ -> ErrorTyp (map_typ typ)
  | Ltac _ -> expression
  | Tuple values -> Tuple (List.map map values)
  | Constructor (name, implicits, values) ->
      Constructor (name, map_implicits implicits, List.map map values)
  | ConstructorExtensible (tag, typ, value) ->
      ConstructorExtensible (tag, map_typ typ, map value)
  | ConstructorVariant (tag, value) ->
      ConstructorVariant
        (tag, Option.map (fun (typ, value) -> (map_typ typ, map value)) value)
  | Apply (head, arguments) -> Apply (map head, List.map map_option arguments)
  | SourceApply (head, arguments, source_type) ->
      SourceApply
        ( map head,
          List.map map_option arguments,
          {
            callee = map_typ source_type.callee;
            result = map_typ source_type.result;
            specialization = map_typ source_type.specialization;
            module_substitutions =
              List.map
                (fun (source, target) -> (map_typ source, map_typ target))
                source_type.module_substitutions;
            module_assumption_telescope =
              Option.map
                (List.map (fun (kind, typ) -> (kind, map_typ typ)))
                source_type.module_assumption_telescope;
            assumption_telescope =
              Option.map
                (List.map (fun (kind, typ) -> (kind, map_typ typ)))
                source_type.assumption_telescope;
          } )
  | Return (operator, value) -> Return (operator, map value)
  | InfixOperator (operator, left, right) ->
      InfixOperator (operator, map left, map right)
  | Function (name, typ, body) ->
      Function (name, Option.map map_typ typ, map body)
  | Functions (names, body) -> Functions (names, map body)
  | LetVar (operator, name, parameters, value, body) ->
      LetVar (operator, name, parameters, map value, map body)
  | LetFun (definition, body) ->
      LetFun
        ( map_definition_types_and_paths ~map_implicit_value
            ~map_variable_implicits map_typ map_path definition,
          map body )
  | LetTyp (name, parameters, typ, body) ->
      LetTyp (name, parameters, map_typ typ, map body)
  | LetModuleUnpack (name, path, body) -> LetModuleUnpack (name, path, map body)
  | Match (scrutinee, dependent, cases, default) ->
      Match
        ( map scrutinee,
          Option.map map_dependent dependent,
          List.map
            (fun (pattern, cast, body) ->
              (pattern, Option.map map_cast cast, map body))
            cases,
          default )
  | MatchWithEquation (scrutinee, cases, default) ->
      MatchWithEquation
        ( map scrutinee,
          List.map
            (fun (pattern, cast, body) ->
              (pattern, Option.map map_cast cast, map body))
            cases,
          default )
  | MatchExtensible (scrutinee, typ, cases) ->
      MatchExtensible
        ( map scrutinee,
          map_typ typ,
          List.map
            (fun (pattern, body) ->
              ( Option.map
                  (fun (tag, pattern, typ) -> (tag, pattern, map_typ typ))
                  pattern,
                map body ))
            cases )
  | MatchVariant (scrutinee, typ, cases) ->
      MatchVariant
        ( map scrutinee,
          map_typ typ,
          List.map (fun (pattern, body) -> (pattern, map body)) cases )
  | Record fields ->
      Record
        (List.map (fun (name, arity, value) -> (name, arity, map value)) fields)
  | Field (value, name) -> Field (map value, name)
  | IfThenElse (condition, then_, else_) ->
      IfThenElse (map condition, map then_, map else_)
  | IfThenElseWithEquation (condition, then_, else_) ->
      IfThenElseWithEquation (map condition, map then_, map else_)
  | Module (typ, fields) ->
      Module
        ( map_typ typ,
          List.map (fun (name, arity, value) -> (name, arity, map value)) fields
        )
  | ModulePack (arity, value) -> ModulePack (arity, map value)
  | Functor (name, typ, body) -> Functor (name, map_typ typ, map body)
  | Cast (value, typ) -> Cast (map value, map_typ typ)
  | TypAnnotation (value, typ) -> TypAnnotation (map value, map_typ typ)
  | Assert (typ, condition) -> Assert (map_typ typ, map condition)
  | Assumption (kind, typ, arguments) ->
      Assumption (kind, map_typ typ, List.map map arguments)
  | RequiresAssumption (kind, typ, body) ->
      RequiresAssumption (kind, map_typ typ, map body)
  | PropagatedAssumption (kind, typ, body) ->
      PropagatedAssumption (kind, map_typ typ, map body)
  | ErrorArray values -> ErrorArray (List.map map values)
  | ErrorMessage (body, message) -> ErrorMessage (map body, message)

and map_definition_types_and_paths ?(map_implicit_value = Fun.id)
    ?(map_variable_implicits = fun _ implicits -> implicits)
    (map_typ : Type.t -> Type.t) (map_path : MixedPath.t -> MixedPath.t)
    (definition : t option Definition.t) : t option Definition.t =
  {
    definition with
    Definition.cases =
      definition.Definition.cases
      |> List.map (fun (header, body) ->
          ( {
              header with
              Header.args =
                List.map
                  (fun (name, typ) -> (name, map_typ typ))
                  header.Header.args;
              Header.instance_args =
                List.map
                  (fun (name, typ) -> (name, map_typ typ))
                  header.Header.instance_args;
              Header.typ = map_typ header.Header.typ;
            },
            Option.map
              (map_types_and_paths ~map_implicit_value ~map_variable_implicits
                 map_typ map_path)
              body ));
  }

let map_types map_typ = map_types_and_paths map_typ Fun.id
let map_definition_types map_typ = map_definition_types_and_paths map_typ Fun.id

(** Add explicit class parameters for every exceptional result required by a
    translated definition. Keeping concrete requirements explicit is as
    important as keeping polymorphic ones explicit: synthesizing a local
    inhabitant would turn a source precondition into an axiom. *)
let add_assumption_instance_args ?(available : assumption_requirement list = [])
    ?(type_dependencies : (Name.t * assumption_requirement list) list = [])
    ?(type_requirements = fun (_ : Type.t) -> [])
    (definition : t option Definition.t) : t option Definition.t =
  let is_available requirement =
    List.exists
      (fun ((_, candidate_typ) as candidate) ->
        (match candidate_typ with Type.ForallModule _ -> false | _ -> true)
        && compare_assumption_requirement candidate requirement = 0)
      available
  in
  let rec close_type_requirements requirements =
    let expanded =
      requirements
      @ List.concat_map (fun (_, typ) -> type_requirements typ) requirements
      |> stable_uniq_assumptions
    in
    if List.length expanded = List.length requirements then expanded
    else close_type_requirements expanded
  in
  let case_requirements (header, body) =
    let call_typ =
      List.fold_right
        (fun (_, argument_typ) result_typ ->
          Type.Arrow (argument_typ, result_typ))
        header.Header.args header.Header.typ
    in
    let header_requirements =
      type_requirements call_typ
      @ (type_dependencies
        |> List.concat_map (fun (name, requirements) ->
            if Type.references_mixed_path_root name call_typ then requirements
            else []))
    in
    (header_requirements
    @ match body with None -> [] | Some body -> assumption_requirements body)
    |> close_type_requirements |> order_assumption_binders
    |> List.filter (fun requirement -> not (is_available requirement))
  in
  let shared_requirements =
    if definition.Definition.is_rec && List.length definition.cases > 1 then
      Some
        (definition.cases
        |> List.concat_map case_requirements
        |> order_assumption_binders)
    else None
  in
  let add_case (header, body) =
    match body with
    | None -> (header, body)
    | Some body ->
        let requirements =
          match shared_requirements with
          | Some requirements -> requirements
          | None -> case_requirements (header, Some body)
        in
        let generated_args =
          requirements
          |> List.mapi (fun index requirement ->
              ( Name.of_string_raw ("_rocq_assumption_" ^ string_of_int index),
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
        ( { header with Header.instance_args = existing_args @ generated_args },
          Some body )
  in
  { definition with Definition.cases = List.map add_case definition.cases }

type assumption_call_spec = {
  call_typ : Type.t;
  projected_types : Name.t Name.Map.t;
  result_typ : Type.t;
  requirements : assumption_requirement list;
}

type assumption_call_specs = assumption_call_spec Name.Map.t

(** Find the generated call specification named by a type constructor. Local
    module fields are stored in [assumption_call_specs] under flattened names
    such as [F_p_t], while their types retain the structured path [F_p.t]. *)
let assumption_call_spec_for_type (specs : assumption_call_specs) (typ : Type.t)
    : assumption_call_spec option =
  let rec suffixes = function
    | [] -> []
    | _ :: remaining as names -> names :: suffixes remaining
  in
  let find names =
    let minimum_length = if List.length names > 1 then 2 else 1 in
    names |> suffixes
    |> List.filter (fun suffix -> List.length suffix >= minimum_length)
    |> List.find_map (fun names ->
        names |> List.map Name.to_string |> String.concat "_"
        |> Name.of_string_raw
        |> fun name -> Name.Map.find_opt name specs)
  in
  let mixed_path_names = function
    | MixedPath.PathName { PathName.path; base } -> path @ [ base ]
    | MixedPath.Access ({ PathName.path; base }, fields)
    | MixedPath.AppliedAccess ({ PathName.path; base }, _, fields) ->
        path @ [ base ] @ List.map (fun field -> field.PathName.base) fields
  in
  let find_mixed_path path =
    match find (mixed_path_names path) with
    | Some _ as spec -> spec
    | None -> (
        match path with
        | MixedPath.PathName { PathName.path = []; base }
        | MixedPath.Access ({ PathName.path = []; base }, _)
        | MixedPath.AppliedAccess ({ PathName.path = []; base }, _, _) ->
            Name.Map.find_opt base specs
        | MixedPath.PathName _ | MixedPath.Access _ | MixedPath.AppliedAccess _
          ->
            None)
  in
  let rec find_type = function
    | Type.Variable name -> Name.Map.find_opt name specs
    | Type.Apply (path, _) -> find_mixed_path path
    | Type.Signature ({ PathName.path; base }, _) -> find (path @ [ base ])
    | Type.InferModule typ
    | Type.ExistTyps (_, typ)
    | Type.ForallTyps (_, typ)
    | Type.FunTyps (_, typ) ->
        find_type typ
    | Type.ForallModule (_, _, typ) | Type.Let (_, _, typ) -> find_type typ
    | Type.Kind _ | Type.String _ | Type.Error _ | Type.Arrow _ | Type.Tuple _
    | Type.Eq _ ->
        None
  in
  find_type typ

(** A projected type such as [F_p.t] also depends on the assumptions needed to
    elaborate its module-record root [F_p]. This lookup is used only to order an
    already known telescope; it must not add the root's requirements to every
    value that mentions the projection. *)
let assumption_root_call_spec_for_type (specs : assumption_call_specs)
    (typ : Type.t) : assumption_call_spec option =
  let find_root { PathName.path; base } =
    let rec suffixes = function
      | [] -> []
      | _ :: remaining as names -> names :: suffixes remaining
    in
    path @ [ base ] |> suffixes
    |> List.find_map (fun names ->
        names |> List.map Name.to_string |> String.concat "_"
        |> Name.of_string_raw
        |> fun name -> Name.Map.find_opt name specs)
  in
  let rec find = function
    | Type.Apply (MixedPath.Access (root, _), _)
    | Type.Apply (MixedPath.AppliedAccess (root, _, _), _) ->
        find_root root
    | Type.Apply (MixedPath.PathName { PathName.path = module_path; _ }, _) -> (
        match List.rev module_path with
        | base :: reversed_path ->
            find_root { PathName.path = List.rev reversed_path; PathName.base }
        | [] -> None)
    | Type.InferModule typ
    | Type.ExistTyps (_, typ)
    | Type.ForallTyps (_, typ)
    | Type.FunTyps (_, typ)
    | Type.ForallModule (_, _, typ)
    | Type.Let (_, _, typ) ->
        find typ
    | Type.Variable _ | Type.Kind _ | Type.String _ | Type.Error _
    | Type.Signature _ | Type.Arrow _ | Type.Tuple _ | Type.Eq _ ->
        None
  in
  find typ

(** Topologically refine the ordinary provider-before-projection order using the
    requirements of generated type definitions. This is necessary for a
    telescope containing, for example, [Unreachable F_p.t]: the assumptions
    required to elaborate [F_p.t] must already be in scope. *)
let order_assumption_binders_with_specs (specs : assumption_call_specs)
    (requirements : assumption_requirement list) : assumption_requirement list =
  let requirements = order_assumption_binders requirements in
  let find_requirement dependency =
    let dependency = normalize_assumption_requirement dependency in
    List.find_opt
      (fun requirement ->
        compare_normalized_assumption_requirement requirement dependency = 0)
      requirements
  in
  let visiting = ref [] in
  let emitted = ref [] in
  let contains requirement requirements =
    List.exists
      (fun candidate ->
        compare_normalized_assumption_requirement candidate requirement = 0)
      requirements
  in
  let rec dependency_specs typ =
    let direct =
      [
        assumption_call_spec_for_type specs typ;
        assumption_root_call_spec_for_type specs typ;
      ]
      |> List.filter_map Fun.id
    in
    let nested =
      match typ with
      | Type.Variable _ | Type.Kind _ | Type.String _ | Type.Error _ -> []
      | Type.Arrow (left, right) | Type.Eq (left, right) ->
          dependency_specs left @ dependency_specs right
      | Type.Tuple types -> List.concat_map dependency_specs types
      | Type.Apply (_, arguments) ->
          arguments
          |> List.concat_map (fun (argument, _) -> dependency_specs argument)
      | Type.Signature (_, parameters) ->
          parameters
          |> List.concat_map (fun (_, value) ->
              Option.fold ~none:[] ~some:dependency_specs value)
      | Type.InferModule value
      | Type.ExistTyps (_, value)
      | Type.ForallTyps (_, value)
      | Type.FunTyps (_, value) ->
          dependency_specs value
      | Type.ForallModule (_, parameter, result) ->
          dependency_specs parameter @ dependency_specs result
      | Type.Let (_, value, body) ->
          dependency_specs value @ dependency_specs body
    in
    direct @ nested
  in
  let rec visit requirement =
    if contains requirement !emitted || contains requirement !visiting then ()
    else (
      visiting := requirement :: !visiting;
      dependency_specs (snd requirement)
      |> List.concat_map (fun spec -> spec.requirements)
      (* Dependency cycles can arise between generated module projections.
         Traverse each adjacency set canonically: otherwise feeding the
         resulting telescope into the next closure pass rotates a cycle and
         prevents the translation from reaching a fixed point. *)
      |> order_assumption_binders
      |> List.iter (fun dependency ->
          Option.iter visit (find_requirement dependency));
      visiting :=
        List.filter
          (fun candidate ->
            compare_normalized_assumption_requirement candidate requirement <> 0)
          !visiting;
      emitted := requirement :: !emitted)
  in
  List.iter visit requirements;
  List.rev !emitted

(** Requirements needed merely to elaborate a generated type expression. Type
    constructors can occur below ordinary constructors such as [list] or
    [iarray], so inspect the complete type rather than only its head. *)
let assumption_requirements_for_type (specs : assumption_call_specs)
    (typ : Type.t) : assumption_requirement list =
  let direct typ =
    [
      assumption_call_spec_for_type specs typ;
      assumption_root_call_spec_for_type specs typ;
    ]
    |> List.filter_map Fun.id
    |> List.concat_map (fun spec -> spec.requirements)
  in
  let rec collect typ =
    let nested =
      match typ with
      | Type.Variable _ | Type.Kind _ | Type.String _ | Type.Error _ -> []
      | Type.Arrow (left, right) | Type.Eq (left, right) ->
          collect left @ collect right
      | Type.Tuple types -> List.concat_map collect types
      | Type.Apply (_, arguments) ->
          arguments |> List.concat_map (fun (argument, _) -> collect argument)
      | Type.Signature (_, parameters) ->
          parameters
          |> List.concat_map (fun (_, value) ->
              Option.fold ~none:[] ~some:collect value)
      | Type.InferModule value -> collect value
      | Type.ForallModule (_, parameter, result) ->
          collect parameter @ collect result
      | Type.ExistTyps (_, body)
      | Type.ForallTyps (_, body)
      | Type.FunTyps (_, body) ->
          collect body
      | Type.Let (_, value, body) -> collect value @ collect body
    in
    direct typ @ nested
  in
  collect typ |> order_assumption_binders_with_specs specs

(** Put a canonical requirement telescope around an expression. Existing inner
    markers are retained because they identify the calls at which the
    assumptions are used; the outer markers determine binder order when the
    enclosing module expression is rendered. *)
let canonicalize_assumption_requirement_order (specs : assumption_call_specs)
    (expression : t) : t =
  let requirements =
    expression |> assumption_requirements
    |> order_assumption_binders_with_specs specs
  in
  List.fold_right
    (fun (kind, typ) body -> PropagatedAssumption (kind, typ, body))
    requirements expression

let assumption_call_spec_for_field (specs : assumption_call_specs)
    (field : PathName.t) : assumption_call_spec option =
  match Name.Map.find_opt field.PathName.base specs with
  | Some spec -> Some spec
  | None ->
      let field_name = Name.to_string field.PathName.base in
      let operator_record_field_name definition_name =
        let marker = "_op_" in
        let marker_length = String.length marker in
        let rec find index =
          if index + marker_length > String.length definition_name then None
          else if String.sub definition_name index marker_length = marker then
            let module_path = String.sub definition_name 0 index in
            let operator =
              String.sub definition_name (index + marker_length)
                (String.length definition_name - index - marker_length)
            in
            Some ("op_" ^ module_path ^ "_" ^ operator)
          else find (index + 1)
        in
        find 0
      in
      specs |> Name.Map.bindings
      |> List.find_map (fun (name, spec) ->
          let name = Name.to_string name in
          if operator_record_field_name name = Some field_name then Some spec
          else None)

(** Add the extra binders needed when a generated module-record constructor
    stores translated functions that acquired assumption class parameters. A
    finalized field spec is authoritative: the field expression can expose only
    its enclosing module requirements while the field type also requires a local
    assumption, as with an exported partial standard-library alias. *)
let add_root_record_field_assumption_arities
    ?(available : assumption_requirement list = [])
    (specs : assumption_call_specs) (expression : t) : t =
  let is_available requirement =
    List.exists
      (fun candidate ->
        compare_assumption_requirement candidate requirement = 0)
      available
  in
  let update_field (field, arity, value) =
    let extra =
      match assumption_call_spec_for_field specs field with
      | Some spec -> List.length spec.requirements
      | None ->
          assumption_requirements value
          |> sort_uniq_assumptions
          |> List.filter (fun requirement -> not (is_available requirement))
          |> List.length
    in
    (field, arity + extra, value)
  in
  match expression with
  | Record _ -> expression
  | Module (typ, fields) -> Module (typ, List.map update_field fields)
  | expression -> expression

(** Requirements attached to the fields of a generated module record.

    These are read from the translated field expressions rather than
    reconstructed from flattened field names. This preserves requirements for
    values copied through module aliases after call propagation has specialized
    their result types. *)
let root_module_field_assumption_requirements (expression : t) :
    (Name.t * assumption_requirement list) list =
  let rec terminal = function
    | Module (_, fields) -> Some fields
    | TypAnnotation (body, _)
    | ErrorMessage (body, _)
    | LetVar (_, _, _, _, body)
    | LetFun (_, body)
    | LetTyp (_, _, _, body)
    | LetModuleUnpack (_, _, body) ->
        terminal body
    | _ -> None
  in
  match terminal expression with
  | None -> []
  | Some fields ->
      fields
      |> List.map (fun (field, _, value) ->
          ( field.PathName.base,
            assumption_requirements value |> sort_uniq_assumptions ))

(** The generated signature named by a terminal module-record expression. *)
let root_module_signature_name (expression : t) : Name.t option =
  let rec terminal = function
    | Module (Type.Signature (path, _), _) -> Some path.PathName.base
    | Module _ -> None
    | TypAnnotation (body, _)
    | ErrorMessage (body, _)
    | LetVar (_, _, _, _, body)
    | LetFun (_, body)
    | LetTyp (_, _, _, body)
    | LetModuleUnpack (_, _, body) ->
        terminal body
    | _ -> None
  in
  terminal expression

let assumption_call_specs_of_definition (definition : t option Definition.t) :
    assumption_call_specs =
  definition.cases
  |> List.fold_left
       (fun specs (header, _) ->
         let requirements =
           header.Header.instance_args
           |> List.filter_map (fun (_, typ) ->
               assumption_requirement_of_class_type typ)
           (* The metadata telescope is addressed by generated binder names,
              so retain the order used by [Header.instance_args] and by the
              rendered definition. *)
           |> stable_uniq_assumptions
         in
         match requirements with
         | [] -> specs
         | _ :: _ ->
             let call_typ =
               List.fold_right
                 (fun (_, argument_typ) result_typ ->
                   Type.Arrow (argument_typ, result_typ))
                 header.Header.args header.Header.typ
             in
             Name.Map.add header.Header.name
               {
                 call_typ;
                 projected_types = Name.Map.empty;
                 result_typ = Type.arrow_result call_typ;
                 requirements;
               }
               specs)
       Name.Map.empty

let rec remove_selected_fargs expression =
  let map = remove_selected_fargs in
  let map_option = Option.map map in
  match expression with
  | Constant _ | Error _ | ErrorTyp _ | Ltac _ -> expression
  | Variable (path, implicits) ->
      let path =
        match path with
        | MixedPath.AppliedAccess (root, applications, fields) -> (
            let applications =
              applications
              |> List.filter (fun (name, _) -> not (String.equal name "_fargs"))
            in
            match (applications, fields) with
            | [], [] -> MixedPath.PathName root
            | [], _ :: _ -> MixedPath.Access (root, fields)
            | _ :: _, _ -> MixedPath.AppliedAccess (root, applications, fields))
        | path -> path
      in
      Variable
        ( path,
          List.filter
            (fun (name, _) -> not (String.equal name "_fargs"))
            implicits )
  | Tuple values -> Tuple (List.map map values)
  | Constructor (name, implicits, values) ->
      Constructor (name, implicits, List.map map values)
  | ConstructorExtensible (tag, typ, value) ->
      ConstructorExtensible (tag, typ, map value)
  | ConstructorVariant (tag, value) ->
      ConstructorVariant
        (tag, Option.map (fun (typ, value) -> (typ, map value)) value)
  | Apply (function_, arguments) ->
      Apply (map function_, List.map map_option arguments)
  | SourceApply (function_, arguments, result_typ) ->
      SourceApply (map function_, List.map map_option arguments, result_typ)
  | Return (operator, value) -> Return (operator, map value)
  | InfixOperator (operator, left, right) ->
      InfixOperator (operator, map left, map right)
  | Function (name, typ, body) -> Function (name, typ, map body)
  | Functions (names, body) -> Functions (names, map body)
  | LetVar (operator, name, parameters, value, body) ->
      LetVar (operator, name, parameters, map value, map body)
  | LetFun (definition, body) ->
      LetFun (remove_definition_selected_fargs definition, map body)
  | LetTyp (name, parameters, typ, body) ->
      LetTyp (name, parameters, typ, map body)
  | LetModuleUnpack (name, path, body) -> LetModuleUnpack (name, path, map body)
  | Match (scrutinee, dependent, cases, default) ->
      Match
        ( map scrutinee,
          dependent,
          List.map
            (fun (pattern, cast, body) -> (pattern, cast, map body))
            cases,
          default )
  | MatchWithEquation (scrutinee, cases, default) ->
      MatchWithEquation
        ( map scrutinee,
          List.map (fun (pattern, cast, body) -> (pattern, cast, map body)) cases,
          default )
  | MatchExtensible (scrutinee, result_typ, cases) ->
      MatchExtensible
        ( map scrutinee,
          result_typ,
          List.map (fun (pattern, body) -> (pattern, map body)) cases )
  | MatchVariant (scrutinee, result_typ, cases) ->
      MatchVariant
        ( map scrutinee,
          result_typ,
          List.map (fun (pattern, body) -> (pattern, map body)) cases )
  | Record fields ->
      Record
        (List.map (fun (name, arity, value) -> (name, arity, map value)) fields)
  | Field (value, name) -> Field (map value, name)
  | IfThenElse (condition, then_, else_) ->
      IfThenElse (map condition, map then_, map else_)
  | IfThenElseWithEquation (condition, then_, else_) ->
      IfThenElseWithEquation (map condition, map then_, map else_)
  | Module (typ, fields) ->
      Module
        ( typ,
          List.map (fun (name, arity, value) -> (name, arity, map value)) fields
        )
  | ModulePack (arity, value) -> ModulePack (arity, map value)
  | Functor (name, typ, body) -> Functor (name, typ, map body)
  | Cast (value, typ) -> Cast (map value, typ)
  | TypAnnotation (value, typ) -> TypAnnotation (map value, typ)
  | Assert (result_typ, condition) -> Assert (result_typ, map condition)
  | Assumption (kind, result_typ, arguments) ->
      Assumption (kind, result_typ, List.map map arguments)
  | RequiresAssumption (kind, result_typ, body) ->
      RequiresAssumption (kind, result_typ, map body)
  | PropagatedAssumption (kind, result_typ, body) ->
      PropagatedAssumption (kind, result_typ, map body)
  | ErrorArray values -> ErrorArray (List.map map values)
  | ErrorMessage (body, message) -> ErrorMessage (map body, message)

and remove_definition_selected_fargs (definition : t option Definition.t) :
    t option Definition.t =
  {
    definition with
    Definition.cases =
      definition.cases
      |> List.map (fun (header, body) ->
          (header, Option.map remove_selected_fargs body));
  }

(** Propagate a callee's generated class requirements to a source-level call.
    Matching the callee's declared result against the typed call result
    instantiates polymorphic requirements without inventing a universal
    instance. *)
let propagate_call_assumptions
    ?(projected_callee = fun (_ : MixedPath.t) -> None)
    ?(bound = Name.Set.empty) (specs : assumption_call_specs) (expression : t) :
    t =
  let map_option f = Option.map f in
  let add_names bound names =
    List.fold_left (fun bound name -> Name.Set.add name bound) bound names
  in
  let add_header_bound bound (header : Header.t) =
    add_names bound
      (List.map fst header.Header.args
      @ List.map fst header.Header.instance_args)
  in
  let dynamic_pattern_bound = function
    | Pattern.VariantCase (_, pattern, _, whole) ->
        Name.Set.union
          (Pattern.get_free_vars pattern)
          (match whole with
          | Some whole -> Pattern.get_free_vars whole
          | None -> Name.Set.empty)
    | Pattern.VariantDefault pattern -> Pattern.get_free_vars pattern
  in
  let qualified_spec path base =
    let rec find_suffix = function
      | [] -> Name.Map.find_opt base specs
      | _ :: remaining as path -> (
          let flattened =
            path @ [ base ] |> List.map Name.to_string |> String.concat "_"
            |> Name.of_string_raw
          in
          match Name.Map.find_opt flattened specs with
          | Some spec -> Some spec
          | None -> (
              (* Structure-level specifications omit enclosing compilation-unit
               names, so retry successively shorter module suffixes.  Keep at
               least one module component to avoid confusing unrelated
               qualified values with the same final name. *)
              match remaining with
              | [] -> None
              | _ :: _ -> find_suffix remaining))
    in
    match find_suffix path with
    | Some spec -> Some spec
    | None -> (
        match path with
        | root :: _ :: _ ->
            let flattened =
              [ root; base ] |> List.map Name.to_string |> String.concat "_"
              |> Name.of_string_raw
            in
            Name.Map.find_opt flattened specs
        | [] | [ _ ] -> None)
  in
  let resolve_projected_alias aliases = function
    | MixedPath.PathName ({ PathName.path = []; base } as path) -> (
        match Name.Map.find_opt base aliases with
        | Some target -> MixedPath.PathName target
        | None -> MixedPath.PathName path)
    | MixedPath.Access (({ PathName.path = []; base } as root), fields) -> (
        match Name.Map.find_opt base aliases with
        | Some target -> MixedPath.Access (target, fields)
        | None -> MixedPath.Access (root, fields))
    | MixedPath.AppliedAccess
        (({ PathName.path = []; base } as root), applications, fields) -> (
        match Name.Map.find_opt base aliases with
        | Some target -> MixedPath.AppliedAccess (target, applications, fields)
        | None -> MixedPath.AppliedAccess (root, applications, fields))
    | path -> path
  in
  let merge_callee_requirements (primary : assumption_call_spec)
      (additional : assumption_call_spec option) : assumption_call_spec =
    match additional with
    | None -> primary
    | Some additional ->
        {
          primary with
          requirements =
            stable_uniq_assumptions
              (additional.requirements @ primary.requirements);
        }
  in
  let local_root_callee mixed_path =
    match mixed_path with
    | MixedPath.Access ({ PathName.path; base }, _)
    | MixedPath.AppliedAccess ({ PathName.path; base }, _, _) -> (
        match qualified_spec path base with
        | Some spec -> Some spec
        | None -> Name.Map.find_opt base specs)
    | MixedPath.PathName _ -> None
  in
  let local_projected_callee = function
    | MixedPath.Access ({ PathName.path = []; base }, fields)
    | MixedPath.AppliedAccess ({ PathName.path = []; base }, _, fields) -> (
        let find names =
          names |> List.map Name.to_string |> String.concat "_"
          |> Name.of_string_raw
          |> fun name -> Name.Map.find_opt name specs
        in
        let field_names = List.map (fun { PathName.base; _ } -> base) fields in
        match find (base :: field_names) with
        | Some spec -> Some spec
        | None -> (
            match List.rev field_names with
            | field :: _ -> find [ base; field ]
            | [] -> None))
    | MixedPath.PathName _ | MixedPath.Access _ | MixedPath.AppliedAccess _ ->
        None
  in
  let projected_with_local_root aliases mixed_path =
    let mixed_path = resolve_projected_alias aliases mixed_path in
    let root = local_root_callee mixed_path in
    match local_projected_callee mixed_path with
    | Some projected -> Some (merge_callee_requirements projected root)
    | None -> (
        match projected_callee mixed_path with
        | Some projected -> Some (merge_callee_requirements projected root)
        | None -> root)
  in
  let local_callee aliases bound expression =
    match expression with
    | Variable (MixedPath.PathName { PathName.path = []; base }, _)
      when Name.Set.mem base bound && not (Name.Map.mem base aliases) ->
        None
    | Variable ((MixedPath.PathName { PathName.path; base } as mixed_path), _)
      -> (
        match qualified_spec path base with
        | Some spec -> Some spec
        | None -> projected_with_local_root aliases mixed_path)
    | Variable (path, _) -> projected_with_local_root aliases path
    | _ -> None
  in
  let exact_callee aliases bound expression =
    match expression with
    | Variable (path, _) ->
        let path = resolve_projected_alias aliases path in
        let is_projection =
          match path with
          | MixedPath.Access (_, _ :: _) | MixedPath.AppliedAccess (_, _, _ :: _)
            ->
              true
          | MixedPath.PathName _
          | MixedPath.Access (_, [])
          | MixedPath.AppliedAccess (_, _, []) ->
              false
        in
        if is_projection then
          let fields =
            match path with
            | MixedPath.Access (_, fields)
            | MixedPath.AppliedAccess (_, _, fields) ->
                fields
            | MixedPath.PathName _ -> []
          in
          let needs_signature_telescope =
            fields
            |> List.exists (fun { PathName.path; base } ->
                path @ [ base ]
                |> List.exists (fun component ->
                    let component = Name.to_string component in
                    String.ends_with ~suffix:"_signature" component
                    || String.ends_with ~suffix:"_result" component))
          in
          if needs_signature_telescope then
            match projected_callee path with
            | Some spec -> Some spec
            | None -> local_projected_callee path
          else
            match local_projected_callee path with
            | Some spec -> Some spec
            | None -> projected_callee path
        else local_callee aliases bound expression
    | _ -> None
  in
  let projected_root_callee aliases expression =
    match expression with
    | Variable (path, _) -> (
        let path = resolve_projected_alias aliases path in
        match path with
        | MixedPath.Access (_, _ :: _) | MixedPath.AppliedAccess (_, _, _ :: _)
          ->
            local_root_callee path
        | MixedPath.PathName _
        | MixedPath.Access (_, [])
        | MixedPath.AppliedAccess (_, _, []) ->
            None)
    | _ -> None
  in
  let rec application_head = function
    | Apply (function_, _)
    | SourceApply (function_, _, _)
    | TypAnnotation (function_, _) ->
        application_head function_
    | function_ -> function_
  in
  let specialize_requirements ?declared_call ?actual_call
      ?(module_substitutions = []) declared_result actual_result requirements =
    let rec instantiate_call_type = function
      | Type.ForallTyps (_, body) | Type.FunTyps (_, body) ->
          instantiate_call_type body
      | typ -> typ
    in
    let matching_types =
      match (declared_call, actual_call) with
      | Some declared, Some actual ->
          (instantiate_call_type declared, instantiate_call_type actual)
      | _, _ -> (declared_result, actual_result)
    in
    let matching_declared, matching_actual = matching_types in
    let substitutions =
      match Type.match_variables matching_declared matching_actual with
      | Some substitutions -> substitutions
      | None -> []
    in
    List.map
      (fun (kind, required_typ) ->
        let required_typ =
          List.fold_left
            (fun required_typ (source, target) ->
              Type.specialize_matched_type ~relaxed_constructors:true
                ~preserve_pattern_constructor:(fun _ -> false)
                source target required_typ
              |> Option.value ~default:required_typ)
            required_typ module_substitutions
        in
        let required_typ =
          match
            Type.specialize_matched_type ~relaxed_constructors:true
              ~preserve_pattern_constructor:(fun _ -> false)
              matching_declared matching_actual required_typ
          with
          | Some specialized -> specialized
          | None -> Type.subst_variables substitutions required_typ
        in
        (kind, required_typ))
      requirements
  in
  let add_requirements ?declared_call ?actual_call ?(module_substitutions = [])
      declared_result actual_result requirements covered body =
    let body =
      if List.exists (fun (kind, _) -> kind = ModuleContext) requirements then
        remove_selected_fargs body
      else body
    in
    let requirements =
      specialize_requirements ?declared_call ?actual_call ~module_substitutions
        declared_result actual_result requirements
    in
    List.fold_right
      (fun ((kind, required_typ) as required) body ->
        if
          List.exists
            (fun requirement ->
              compare_assumption_requirement requirement required = 0)
            covered
        then body
        else PropagatedAssumption (kind, required_typ, body))
      requirements body
  in
  let rec map_definition aliases bound covered
      (definition : t option Definition.t) =
    let names =
      definition.Definition.cases
      |> List.map (fun (header, _) -> header.Header.name)
    in
    let recursive_bound =
      if definition.Definition.is_rec then add_names bound names else bound
    in
    {
      definition with
      Definition.cases =
        definition.cases
        |> List.map (fun (header, body) ->
            ( header,
              Option.map
                (transform aliases
                   (add_header_bound recursive_bound header)
                   false covered)
                body ));
    }
  and transform aliases bound suppress covered expression =
    let recurse = transform aliases bound false covered in
    match expression with
    | Constant _ | Error _ | ErrorTyp _ | Ltac _ -> expression
    | Variable _ when suppress -> expression
    | Variable _ -> (
        match local_callee aliases bound expression with
        | None -> expression
        | Some ({ call_typ; result_typ; requirements; _ } as callee) ->
            let exact_callee =
              exact_callee aliases bound expression
              |> Option.value ~default:callee
            in
            let root_callee = projected_root_callee aliases expression in
            let root_requirements =
              Option.map (fun spec -> spec.requirements) root_callee
            in
            let source_type =
              {
                callee = call_typ;
                result = call_typ;
                specialization = call_typ;
                module_substitutions = [];
                module_assumption_telescope = root_requirements;
                assumption_telescope = Some exact_callee.requirements;
              }
            in
            (* A function can escape as a first-class value without appearing
               in a source application. Preserve its exact generated class
               telescope as a zero-argument [SourceApply], so the final
               materialization pass supplies named providers instead of
               asking Rocq typeclass search to reconstruct a large dependent
               context. Rendering a zero-argument application is just the
               underlying value. *)
            let value =
              if
                exact_callee.requirements = []
                && Option.value ~default:[] root_requirements = []
              then expression
              else SourceApply (expression, [], source_type)
            in
            add_requirements ~declared_call:call_typ ~actual_call:call_typ
              result_typ result_typ requirements covered value)
    | Tuple values -> Tuple (List.map recurse values)
    | Constructor (name, implicits, values) ->
        Constructor (name, implicits, List.map recurse values)
    | ConstructorExtensible (tag, typ, value) ->
        ConstructorExtensible (tag, typ, recurse value)
    | ConstructorVariant (tag, value) ->
        ConstructorVariant
          (tag, Option.map (fun (typ, value) -> (typ, recurse value)) value)
    | Apply (f, arguments) -> (
        let callee = local_callee aliases bound (application_head f) in
        let application =
          Apply
            ( transform aliases bound true covered f,
              List.map (map_option recurse) arguments )
        in
        if suppress then application
        else
          match callee with
          | None -> application
          | Some { result_typ; requirements; _ } ->
              add_requirements result_typ result_typ requirements covered
                application)
    | SourceApply (f, arguments, result_typ) -> (
        let callee = local_callee aliases bound (application_head f) in
        let exact_callee = exact_callee aliases bound (application_head f) in
        let root_callee = projected_root_callee aliases (application_head f) in
        let f = transform aliases bound true covered f in
        let arguments = List.map (map_option recurse) arguments in
        let exact_assumption_telescope =
          Option.map
            (fun { call_typ; result_typ = declared_result; requirements; _ } ->
              specialize_requirements ~declared_call:call_typ
                ~actual_call:result_typ.callee
                ~module_substitutions:result_typ.module_substitutions
                declared_result result_typ.specialization requirements)
            exact_callee
        in
        let assumption_telescope = exact_assumption_telescope in
        let module_assumption_telescope =
          Option.map (fun spec -> spec.requirements) root_callee
        in
        let result_typ =
          { result_typ with module_assumption_telescope; assumption_telescope }
        in
        let application = SourceApply (f, arguments, result_typ) in
        if suppress then application
        else
          match callee with
          | None -> application
          | Some { call_typ; result_typ = declared_result; requirements; _ } ->
              add_requirements ~declared_call:call_typ
                ~actual_call:result_typ.callee
                ~module_substitutions:result_typ.module_substitutions
                declared_result result_typ.specialization requirements covered
                application)
    | Return (operator, value) -> Return (operator, recurse value)
    | InfixOperator (operator, left, right) ->
        InfixOperator (operator, recurse left, recurse right)
    | Function (name, typ, body) ->
        Function
          ( name,
            typ,
            transform aliases (Name.Set.add name bound) false covered body )
    | Functions (names, body) ->
        Functions
          (names, transform aliases (add_names bound names) false covered body)
    | LetVar (operator, name, typ_vars, value, body) ->
        let value = recurse value in
        let rec module_reference_target = function
          | Variable (target, implicits)
            when List.exists
                   (fun (label, _) ->
                     String.equal label module_reference_marker)
                   implicits ->
              Some target
          | Apply (head, _)
          | SourceApply (head, _, _)
          | TypAnnotation (head, _)
          | Cast (head, _)
          | ErrorMessage (head, _)
          | RequiresAssumption (_, _, head)
          | PropagatedAssumption (_, _, head) ->
              module_reference_target head
          | _ -> None
        in
        let module_reference_target = module_reference_target value in
        let aliases =
          match functor_application_head value with
          | Some target -> Name.Map.add name target aliases
          | None -> Name.Map.remove name aliases
        in
        let body =
          transform aliases (Name.Set.add name bound) false covered body
        in
        let body =
          (* A first-class local open is represented by a generated module
             binding such as [let opened_module = M in ...]. Requirements for
             projected calls are introduced by this pass, after the local-open
             translation has normalized requirements already present in the
             body. Normalize those newly introduced requirements as well. *)
          match module_reference_target with
          | Some target ->
              map_assumption_types (Type.subst_mixed_path_root name target) body
          | None
            when String.starts_with ~prefix:"opened_module_"
                   (Name.to_string name) -> (
              match value with
              | Variable (target, _) ->
                  map_assumption_types
                    (Type.subst_mixed_path_root name target)
                    body
              | _ ->
                  map_assumption_types
                    (specialize_assumption_for_application ~local_result:name
                       value)
                    body)
          | None -> body
        in
        LetVar (operator, name, typ_vars, value, body)
    | LetFun (definition, body) ->
        let names =
          definition.Definition.cases
          |> List.map (fun (header, _) -> header.Header.name)
        in
        LetFun
          ( map_definition aliases bound covered definition,
            transform aliases (add_names bound names) false covered body )
    | LetTyp (name, parameters, typ, body) ->
        LetTyp (name, parameters, typ, recurse body)
    | LetModuleUnpack (name, path, body) ->
        LetModuleUnpack
          ( name,
            path,
            transform aliases (Name.Set.add name bound) false covered body )
    | Match (scrutinee, dependent, cases, default) ->
        Match
          ( recurse scrutinee,
            dependent,
            List.map
              (fun (pattern, cast, body) ->
                let pattern_bound =
                  match cast with
                  | Some { bound_vars; _ } ->
                      add_names
                        (Pattern.get_free_vars pattern)
                        (List.map fst bound_vars)
                  | None -> Pattern.get_free_vars pattern
                in
                ( pattern,
                  cast,
                  transform aliases
                    (Name.Set.union bound pattern_bound)
                    false covered body ))
              cases,
            default )
    | MatchWithEquation (scrutinee, cases, default) ->
        MatchWithEquation
          ( recurse scrutinee,
            List.map
              (fun (pattern, cast, body) ->
                let pattern_bound =
                  match cast with
                  | Some { bound_vars; _ } ->
                      add_names
                        (Pattern.get_free_vars pattern)
                        (List.map fst bound_vars)
                  | None -> Pattern.get_free_vars pattern
                in
                ( pattern,
                  cast,
                  transform aliases
                    (Name.Set.union bound pattern_bound)
                    false covered body ))
              cases,
            default )
    | MatchExtensible (scrutinee, typ, cases) ->
        MatchExtensible
          ( recurse scrutinee,
            typ,
            List.map
              (fun (pattern, body) ->
                let pattern_bound =
                  match pattern with
                  | Some (_, pattern, _) -> Pattern.get_free_vars pattern
                  | None -> Name.Set.empty
                in
                ( pattern,
                  transform aliases
                    (Name.Set.union bound pattern_bound)
                    false covered body ))
              cases )
    | MatchVariant (scrutinee, typ, cases) ->
        MatchVariant
          ( recurse scrutinee,
            typ,
            List.map
              (fun (pattern, body) ->
                ( pattern,
                  transform aliases
                    (Name.Set.union bound (dynamic_pattern_bound pattern))
                    false covered body ))
              cases )
    | Record fields ->
        Record
          (List.map
             (fun (name, arity, value) -> (name, arity, recurse value))
             fields)
    | Field (value, name) -> Field (recurse value, name)
    | IfThenElse (condition, then_, else_) ->
        IfThenElse (recurse condition, recurse then_, recurse else_)
    | IfThenElseWithEquation (condition, then_, else_) ->
        IfThenElseWithEquation (recurse condition, recurse then_, recurse else_)
    | Module (typ, fields) ->
        Module
          ( typ,
            List.map
              (fun (name, arity, value) -> (name, arity, recurse value))
              fields )
    | ModulePack (arity, value) -> ModulePack (arity, recurse value)
    | Functor (name, typ, body) ->
        Functor
          ( name,
            typ,
            transform aliases (Name.Set.add name bound) false covered body )
    | Cast (value, typ) -> Cast (recurse value, typ)
    | TypAnnotation (value, typ) -> TypAnnotation (recurse value, typ)
    | Assert (typ, condition) -> Assert (typ, recurse condition)
    | Assumption (kind, typ, arguments) ->
        Assumption (kind, typ, List.map recurse arguments)
    | RequiresAssumption (kind, typ, body) ->
        RequiresAssumption (kind, typ, recurse body)
    | PropagatedAssumption (_, _, body) ->
        (* Rebuild call requirements from the current callee specifications on
           every fixed-point pass. *)
        transform aliases bound false [] body
    | ErrorArray values -> ErrorArray (List.map recurse values)
    | ErrorMessage (body, message) -> ErrorMessage (recurse body, message)
  in
  transform Name.Map.empty bound false [] expression

let propagate_definition_call_assumptions
    ?(projected_callee = fun (_ : MixedPath.t) -> None)
    (specs : assumption_call_specs) (definition : t option Definition.t) :
    t option Definition.t =
  let recursive_names =
    if definition.Definition.is_rec then
      List.map
        (fun (header, _) -> header.Header.name)
        definition.Definition.cases
    else []
  in
  let definition =
    {
      definition with
      Definition.cases =
        definition.cases
        |> List.map (fun (header, body) ->
            ( header,
              Option.map
                (propagate_call_assumptions ~projected_callee
                   ~bound:
                     (List.fold_left
                        (fun bound name -> Name.Set.add name bound)
                        Name.Set.empty
                        (recursive_names
                        @ List.map fst header.Header.args
                        @ List.map fst header.Header.instance_args))
                   specs)
                body ));
    }
  in
  add_assumption_instance_args definition

(** Render the exact generated class telescope recorded on typed source calls.
    The propagation pass records this telescope from the resolved callee, so
    nested partial operations cannot accidentally contribute arguments to an
    enclosing call. *)
let materialize_source_call_assumptions
    ?(order_source_requirements = fun (_ : t) requirements -> requirements)
    (assumptions : (Name.t * assumption_requirement) list) (expression : t) : t
    =
  let provider requirement =
    assumptions
    |> List.find_map (fun (name, candidate) ->
        if compare_assumption_requirement candidate requirement = 0 then
          Some name
        else None)
  in
  let applications prefix requirements =
    requirements
    |> List.mapi (fun index requirement ->
        Option.map
          (fun provider ->
            (prefix ^ string_of_int index, Name.to_string provider))
          (provider requirement))
    |> List.filter_map Fun.id
  in
  let append_applications existing added =
    List.fold_left
      (fun applications ((label, _) as application) ->
        if
          List.exists
            (fun (existing, _) -> String.equal label existing)
            applications
        then applications
        else applications @ [ application ])
      existing added
  in
  let add_root_applications added = function
    | MixedPath.PathName root ->
        if added = [] then MixedPath.PathName root
        else MixedPath.AppliedAccess (root, added, [])
    | MixedPath.Access (root, fields) ->
        if added = [] then MixedPath.Access (root, fields)
        else MixedPath.AppliedAccess (root, added, fields)
    | MixedPath.AppliedAccess (root, existing, fields) ->
        MixedPath.AppliedAccess
          (root, append_applications existing added, fields)
  in
  let add_to_head root_added field_added =
    let rec add = function
      | Variable (path, implicits) ->
          Variable
            ( add_root_applications root_added path,
              append_applications implicits field_added )
      | Apply (head, arguments) -> Apply (add head, arguments)
      | SourceApply (head, arguments, source_type) ->
          SourceApply (add head, arguments, source_type)
      | TypAnnotation (head, typ) -> TypAnnotation (add head, typ)
      | Cast (head, typ) -> Cast (add head, typ)
      | ErrorMessage (head, message) -> ErrorMessage (add head, message)
      | RequiresAssumption (kind, typ, head) ->
          RequiresAssumption (kind, typ, add head)
      | PropagatedAssumption (kind, typ, head) ->
          PropagatedAssumption (kind, typ, add head)
      | Field (Variable (path, implicits), field) ->
          let path =
            match path with
            | MixedPath.PathName root -> MixedPath.Access (root, [ field ])
            | MixedPath.Access (root, fields) ->
                MixedPath.Access (root, fields @ [ field ])
            | MixedPath.AppliedAccess (root, arguments, fields) ->
                MixedPath.AppliedAccess (root, arguments, fields @ [ field ])
          in
          Variable
            ( add_root_applications root_added path,
              append_applications implicits field_added )
      | head -> head
    in
    add
  in
  let rec map expression =
    let map_option = Option.map map in
    match expression with
    | Constant _ | Variable _ | Error _ | ErrorTyp _ | Ltac _ -> expression
    | Tuple values -> Tuple (List.map map values)
    | Constructor (name, implicits, values) ->
        Constructor (name, implicits, List.map map values)
    | ConstructorExtensible (tag, typ, value) ->
        ConstructorExtensible (tag, typ, map value)
    | ConstructorVariant (tag, value) ->
        ConstructorVariant
          (tag, Option.map (fun (typ, value) -> (typ, map value)) value)
    | Apply (head, arguments) -> Apply (map head, List.map map_option arguments)
    | SourceApply (head, arguments, source_type) ->
        let head = map head in
        let root_added =
          source_type.module_assumption_telescope
          |> Option.map (applications "_rocq_module_assumption_")
          |> Option.value ~default:[]
        in
        let field_added =
          source_type.assumption_telescope
          |> Option.map (order_source_requirements head)
          |> Option.map (applications "_rocq_assumption_")
          |> Option.value ~default:[]
        in
        let head =
          if root_added = [] && field_added = [] then head
          else add_to_head root_added field_added head
        in
        SourceApply (head, List.map map_option arguments, source_type)
    | Return (operator, value) -> Return (operator, map value)
    | InfixOperator (operator, left, right) ->
        InfixOperator (operator, map left, map right)
    | Function (name, typ, body) -> Function (name, typ, map body)
    | Functions (names, body) -> Functions (names, map body)
    | LetVar (operator, name, parameters, value, body) ->
        LetVar (operator, name, parameters, map value, map body)
    | LetFun (definition, body) ->
        let definition =
          {
            definition with
            Definition.cases =
              definition.Definition.cases
              |> List.map (fun (header, body) -> (header, Option.map map body));
          }
        in
        LetFun (definition, map body)
    | LetTyp (name, parameters, typ, body) ->
        LetTyp (name, parameters, typ, map body)
    | LetModuleUnpack (name, path, body) ->
        LetModuleUnpack (name, path, map body)
    | Match (scrutinee, dependent, cases, default) ->
        Match
          ( map scrutinee,
            dependent,
            List.map
              (fun (pattern, cast, body) -> (pattern, cast, map body))
              cases,
            default )
    | MatchWithEquation (scrutinee, cases, default) ->
        MatchWithEquation
          ( map scrutinee,
            List.map
              (fun (pattern, cast, body) -> (pattern, cast, map body))
              cases,
            default )
    | MatchExtensible (scrutinee, typ, cases) ->
        MatchExtensible
          ( map scrutinee,
            typ,
            List.map (fun (pattern, body) -> (pattern, map body)) cases )
    | MatchVariant (scrutinee, typ, cases) ->
        MatchVariant
          ( map scrutinee,
            typ,
            List.map (fun (pattern, body) -> (pattern, map body)) cases )
    | Record fields ->
        Record
          (List.map
             (fun (name, arity, value) -> (name, arity, map value))
             fields)
    | Field (value, name) -> Field (map value, name)
    | IfThenElse (condition, then_, else_) ->
        IfThenElse (map condition, map then_, map else_)
    | IfThenElseWithEquation (condition, then_, else_) ->
        IfThenElseWithEquation (map condition, map then_, map else_)
    | Module (typ, fields) ->
        Module
          ( typ,
            List.map
              (fun (name, arity, value) -> (name, arity, map value))
              fields )
    | ModulePack (arity, value) -> ModulePack (arity, map value)
    | Functor (name, typ, body) -> Functor (name, typ, map body)
    | Cast (value, typ) -> Cast (map value, typ)
    | TypAnnotation (value, typ) -> TypAnnotation (map value, typ)
    | Assert (typ, condition) -> Assert (typ, map condition)
    | Assumption (kind, typ, arguments) ->
        Assumption (kind, typ, List.map map arguments)
    | RequiresAssumption (kind, typ, body) ->
        RequiresAssumption (kind, typ, map body)
    | PropagatedAssumption (kind, typ, body) ->
        PropagatedAssumption (kind, typ, map body)
    | ErrorArray values -> ErrorArray (List.map map values)
    | ErrorMessage (body, message) -> ErrorMessage (map body, message)
  in
  map expression

let materialize_definition_source_call_assumptions
    ?(order_source_requirements = fun (_ : t) requirements -> requirements)
    (definition : t option Definition.t) : t option Definition.t =
  {
    definition with
    Definition.cases =
      definition.Definition.cases
      |> List.map (fun (header, body) ->
          let assumptions =
            header.Header.instance_args
            |> List.filter_map (fun (name, typ) ->
                Option.map
                  (fun requirement -> (name, requirement))
                  (assumption_requirement_of_class_type typ))
          in
          ( header,
            Option.map
              (materialize_source_call_assumptions ~order_source_requirements
                 assumptions)
              body ));
  }

(** Infer the instantiated OCaml type parameters of a polymorphic value
    projected from a translated module record.

    Rocq usually infers these parameters. That is not reliable when an argument
    is typed through a local associated-type alias: unification may commit to
    the alias's argument before unfolding its body. The typed OCaml tree already
    records the intended instantiation, so preserve it as named Rocq arguments
    on record projections. *)
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
      Variable ((MixedPath.Access _ as path), []) ) -> (
      let parent_and_field =
        match source_path with
        | Path.Pdot (parent, field) -> Some (parent, field)
        | Path.Pextra_ty (Path.Pdot (parent, field), _) -> Some (parent, field)
        | _ -> None
      in
      let* projection_type =
        match parent_and_field with
        | None -> return None
        | Some (parent, field) -> (
            let* signature_path = MixedPath.get_signature_path parent in
            match signature_path with
            | None -> return None
            | Some signature_path -> (
                let* module_type = get_module_type_hint signature_path in
                match
                  Option.map (Env.scrape_alias source.exp_env) module_type
                with
                | Some (Mty_signature signature) ->
                    return
                      (signature
                      |> List.find_map (function
                        | Types.Sig_value (ident, description, _)
                          when String.equal (Ident.name ident) field ->
                            Some description.Types.val_type
                        | _ -> None))
                | _ -> return None))
      in
      match projection_type with
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
                     (fun actual_typ_vars (original_parameter, copied_parameter)
                        ->
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
                |> Monad.List.filter_map
                     (fun (generic_parameter, actual_parameter) ->
                       let* source_name =
                         type_variable_source_name generic_parameter
                       in
                       match
                         Name.Map.find_opt source_name projection_name_map
                       with
                       | None -> return None
                       | Some generated_name
                         when not
                                (List.mem_assoc generated_name projection_vars)
                         ->
                           return None
                       | Some generated_name ->
                           let* actual_type, _, _ =
                             Type.of_typ_expr true actual_typ_vars
                               actual_parameter
                           in
                           let rendered_type =
                             SmartPrint.to_string 1_000_000 0
                               (Type.to_coq None None actual_type)
                           in
                           return
                             (Some (Name.to_string generated_name, rendered_type)))
              in
              return (Variable (path, implicits)))
  | _ -> return translated

(** Import an OCaml expression. *)
let names_bound_by_pattern (pattern : value general_pattern) :
    Name.t list Monad.t =
  Typedtree.pat_bound_idents_full pattern
  |> Monad.List.map (fun (ident, _, _, _) -> Name.of_ident true ident)

let mixed_path_of_dotted_name (name : string) : MixedPath.t =
  match List.rev (String.split_on_char '.' name) with
  | [] -> failwith "empty configured Rocq path"
  | base :: path -> MixedPath.PathName (PathName.__make (List.rev path) base)

let signature_record_operation
    (label_description : Data_types.label_description) (is_constructor : bool) :
    MixedPath.t option Monad.t =
  match Types.get_desc label_description.lbl_res with
  | Tconstr (record_path, _, _) -> (
      let rec root_and_fields path fields =
        match path with
        | Path.Pdot (parent, field) -> root_and_fields parent (field :: fields)
        | Path.Pextra_ty (parent, Path.Pext_ty) -> root_and_fields parent fields
        | Path.Pextra_ty (parent, Path.Pcstr_ty field) ->
            root_and_fields parent (field :: fields)
        | (Path.Pident _ | Path.Papply _) as root -> (root, fields)
      in
      let root, fields = root_and_fields record_path [] in
      match (root, List.rev fields) with
      | Path.Pident _, type_name :: reversed_prefix -> (
          let prefix = List.rev reversed_prefix in
          let* signature = get_signature_hint root in
          match signature with
          | None -> return None
          | Some signature ->
              let* env = get_env in
              let declaration = Env.find_type record_path env in
              let is_record =
                match declaration.Types.type_kind with
                | Type_record _ -> true
                | Type_abstract _ | Type_variant _ | Type_open -> false
                | exception Not_found -> false
              in
              (* A strengthened functor application can expose a concrete
                 nominal record through a manifest.  Its canonical Rocq
                 projection remains available, whereas an abstract record in
                 a functor parameter must use the generated interface getter. *)
              if
                (not is_record)
                || Option.is_some declaration.Types.type_manifest
              then return None
              else
                let operation =
                  if is_constructor then "_rocq_record_make"
                  else "_rocq_record_get_" ^ label_description.lbl_name
                in
                let* operation =
                  Name.of_strings true (prefix @ [ type_name; operation ])
                in
                let* base = PathName.of_path_with_convert false root in
                let* field =
                  PathName.of_path_and_name_with_convert signature operation
                in
                return (Some (MixedPath.Access (base, [ field ]))))
      | (Path.Pident _ | Path.Papply _), []
      | Path.Papply _, _
      | (Path.Pdot _ | Path.Pextra_ty _), _ ->
          return None)
  | _ -> return None

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
              let is_unsupported_equality =
                String.equal (MixedPath.to_string x) "equiv_decb"
                && not (equality_argument_has_rocq_eq_dec e)
              in
              let* equality_override =
                if not is_unsupported_equality then return None
                else
                  let* configuration = get_configuration in
                  let* definition_path = get_definition_path in
                  return
                    (Configuration.get_equality_override configuration
                       definition_path)
              in
              let x =
                match equality_override with
                | Some target -> mixed_path_of_dotted_name target
                | None when is_unsupported_equality ->
                    MixedPath.PathName
                      (PathName.__make
                         [ "RocqOfOCaml"; "Basics"; "Stdlib" ]
                         "polymorphic_equal")
                | None
                  when String.equal (MixedPath.to_string x) "nequiv_decb"
                       && not (equality_argument_has_rocq_eq_dec e) ->
                    MixedPath.PathName
                      (PathName.__make
                         [ "RocqOfOCaml"; "Basics"; "Stdlib" ]
                         "polymorphic_not_equal")
                | None -> x
              in
              let variable = Variable (x, implicits) in
              if not (is_partial_operation_path path) then return variable
              else
                let* expanded_typ = Type.fully_expand_aliases e.exp_type in
                let* typ, _, _ = Type.of_typ_expr false typ_vars expanded_typ in
                let required_typ = Type.arrow_result typ in
                let* () =
                  warn
                    "a partial OCaml library operation requires an Unreachable \
                     result; prove that its exceptional precondition cannot \
                     occur"
                in
                return
                  (RequiresAssumption (Unreachable, required_typ, variable))
          | Texp_constant constant ->
              Constant.of_constant constant >>= fun constant ->
              return (Constant constant)
          | Texp_let (is_rec, cases, e2) ->
              let* bound_names =
                cases
                |> Monad.List.concat_map (fun { vb_pat; _ } ->
                    names_bound_by_pattern vb_pat)
              in
              push_term_environment
                (List.map Name.to_string bound_names)
                (of_expression typ_vars e2)
              >>= fun e2 -> of_let typ_vars is_rec cases e2
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
                    | Tparam_pat pattern | Tparam_optional_default (pattern, _)
                      ->
                        names_bound_by_pattern pattern)
              in
              let of_param body { fp_kind; _ } =
                let of_pat pat =
                  let is_module_unpack = Pattern.has_unpack_marker pat in
                  match (is_module_unpack, pat.pat_desc) with
                  | ( true,
                      ( Tpat_var (x, _, _)
                      | Tpat_alias ({ pat_desc = Tpat_any; _ }, x, _, _, _) ) )
                    ->
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
                      | Tpat_alias ({ pat_desc = Tpat_any; _ }, x, _, _, _) ) )
                    ->
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
                | Tparam_optional_default (pat, default) -> (
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
                      | Tpat_alias ({ pat_desc = Tpat_any; _ }, ident, _, _, _)
                        ->
                          Name.of_string_raw (Ident.name ident ^ "_optional")
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
                    match pattern with
                    | None ->
                        raise body Unexpected
                          "An optional-default parameter has an impossible \
                           pattern"
                    | Some pattern ->
                        let default_branch =
                          Match (default, None, [ (pattern, None, body) ], false)
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
                                      ({ pat_desc = Tpat_any; _ }, x, _, _, _) );
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
                              match extra with
                              | Tpat_unpack -> true
                              | _ -> false)
                            pat_extra) ->
                    let* x = Name.of_ident true x in
                    let* typ, _, _ = Type.of_typ_expr true typ_vars pat_type in
                    push_term_environment
                      (List.map Name.to_string (x :: parameter_names))
                      (of_expression typ_vars e)
                    >>= fun e -> return (Function (x, Some typ, e))
                | Tfunction_cases { cases; _ } ->
                    let* x, typ, e =
                      open_cases typ_vars cases is_gadt_match is_tagged_match
                        do_cast_results is_with_default_case
                        is_grab_existentials
                    in
                    return (Function (x, typ, e))
              in
              List.fold_right
                (fun param body -> body >>= fun body -> of_param body param)
                params (return body)
          | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, e_xs)
            when List.mem (Path.name path)
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
              let* typ, _, _ = Type.of_typ_expr false typ_vars e.exp_type in
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
                | ModuleContext -> assert false
              in
              return (Assumption (kind, typ, arguments))
          | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, e_xs)
            when Option.is_some (constructor_equality_application path e_xs)
            -> (
              match constructor_equality_application path e_xs with
              | Some { negate; scrutinee; constructor; payloads; exhaustive } ->
                  let* scrutinee = of_expression typ_vars scrutinee in
                  let* payloads =
                    Monad.List.map (of_expression typ_vars) payloads
                  in
                  let* constructor =
                    PathName.of_constructor_description constructor
                  in
                  let actual_names =
                    List.mapi
                      (fun index _ ->
                        Name.of_string_raw
                          ("_rocq_eq_actual_" ^ string_of_int index))
                      payloads
                  in
                  let expected_names =
                    List.mapi
                      (fun index _ ->
                        Name.of_string_raw
                          ("_rocq_eq_expected_" ^ string_of_int index))
                      payloads
                  in
                  let variable name = Variable (MixedPath.of_name name, []) in
                  let true_value =
                    Variable (MixedPath.PathName PathName.true_value, [])
                  in
                  let false_value =
                    Variable (MixedPath.PathName PathName.false_value, [])
                  in
                  let payload_equal actual expected =
                    Apply
                      ( variable (Name.of_string_raw "equiv_decb"),
                        [ Some (variable actual); Some (variable expected) ] )
                  in
                  let equal_payloads =
                    List.map2 payload_equal actual_names expected_names
                    |> List.fold_left
                         (fun result equality ->
                           Apply
                             ( variable (Name.of_string_raw "andb"),
                               [ Some result; Some equality ] ))
                         true_value
                  in
                  let branches =
                    [
                      ( Pattern.Constructor
                          ( constructor,
                            List.map
                              (fun name -> Pattern.Variable name)
                              actual_names ),
                        None,
                        equal_payloads );
                    ]
                    @
                    if exhaustive then []
                    else [ (Pattern.Any, None, false_value) ]
                  in
                  let equality = Match (scrutinee, None, branches, false) in
                  let equality =
                    List.fold_right2
                      (fun name payload body ->
                        LetVar (None, name, [], payload, body))
                      expected_names payloads equality
                  in
                  if negate then
                    return
                      (Apply
                         ( variable (Name.of_string_raw "negb"),
                           [ Some equality ] ))
                  else return equality
              | None ->
                  failwith
                    "constructor equality application disappeared after its \
                     guard")
          | Texp_apply (source_e_f, e_xs) ->
              let partial_operation =
                match source_e_f.exp_desc with
                | Texp_ident (path, _, _) -> is_partial_operation_path path
                | _ -> false
              in
              (match specialized_integer_comparison source_e_f with
                | Some target -> return (z_comparison_variable target)
                | None -> of_expression typ_vars source_e_f)
              >>= fun e_f ->
              let rec peel_requirements requirements = function
                | RequiresAssumption (kind, typ, body)
                | PropagatedAssumption (kind, typ, body) ->
                    peel_requirements ((kind, typ) :: requirements) body
                | body -> (List.rev requirements, body)
              in
              let inherited_requirements, e_f = peel_requirements [] e_f in
              let partial_operation_already_warned =
                partial_operation && inherited_requirements <> []
              in
              infer_projection_implicits typ_vars source_e_f e_f >>= fun e_f ->
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
              let* application_callee_typ, _, _ =
                Type.of_typ_expr false typ_vars source_e_f.exp_type
              in
              let* expanded_application_source_typ =
                Type.fully_expand_aliases e.exp_type
              in
              let* expanded_application_typ, _, _ =
                Type.of_typ_expr false typ_vars expanded_application_source_typ
              in
              let source_application_type =
                {
                  callee = application_callee_typ;
                  result = application_typ;
                  specialization = expanded_application_typ;
                  module_substitutions = [];
                  module_assumption_telescope = None;
                  assumption_telescope = None;
                }
              in
              let apply =
                match List.find_map (fun x -> x) applies with
                | Some apply -> apply
                | None ->
                    let application =
                      SourceApply (e_f, e_xs, source_application_type)
                    in
                    if is_ocaml_format_function e_f then
                      TypAnnotation (application, application_typ)
                    else application
              in
              let apply =
                List.fold_right
                  (fun (kind, typ) body -> RequiresAssumption (kind, typ, body))
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
                     (Unreachable, expanded_application_typ, apply))
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
                    List.mem constructor_description.cstr_name [ "Ok"; "Error" ]
                  then
                    let* typ, _, _ = Type.of_typ_expr true typ_vars typ in
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
              let* signature_constructor =
                match (extended_expression, Array.to_list fields) with
                | None, (label_description, Overridden _) :: _ ->
                    signature_record_operation label_description true
                | None, (_, Kept _) :: _ | None, [] | Some _, _ -> return None
              in
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
              match (extended_expression, signature_constructor) with
              | None, Some constructor ->
                  return
                    (Apply
                       ( Variable (constructor, []),
                         fields |> List.map (fun (_, _, value) -> Some value) ))
              | None, None -> return (Record fields)
              | Some extended_expression, _ ->
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
          | Texp_field (e, _, label_description) -> (
              let* signature_projection =
                signature_record_operation label_description false
              in
              of_expression typ_vars e >>= fun e ->
              match signature_projection with
              | Some projection ->
                  return (Apply (Variable (projection, []), [ Some e ]))
              | None ->
                  let* x = PathName.of_label_description label_description in
                  return (Field (e, x)))
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
              let exception_name = Name.of_string_raw "_exception_value" in
              let exception_value =
                Variable (MixedPath.of_name exception_name, [])
              in
              let* error_handler =
                of_match_extensible typ_vars exception_value cases
              in
              return
                (Apply
                   ( Variable
                       (MixedPath.of_name (Name.of_string_raw "try_with"), []),
                     [
                       Some (Function (Name.Nameless, None, e));
                       Some (Function (exception_name, None, error_handler));
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
              PathName.of_path_with_convert false path >>= fun path_name ->
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
                | IsFirstClassModule.Not_found _ -> (
                    let rec root_functor_path module_expr =
                      match module_expr.mod_desc with
                      | Tmod_ident (path, _) -> Some path
                      | Tmod_apply (functor_expr, _, _)
                      | Tmod_apply_unit functor_expr
                      | Tmod_constraint (functor_expr, _, _, _) ->
                          root_functor_path functor_expr
                      | Tmod_structure _ | Tmod_functor _ | Tmod_unpack _
                      | Tmod_typed_hole ->
                          None
                    in
                    match root_functor_path module_expr with
                    | Some functor_path -> (
                        let* result_signature =
                          get_functor_result_signature functor_path
                        in
                        match result_signature with
                        | Some signature_path ->
                            return (IsFirstClassModule.Found signature_path)
                        | None -> return classification)
                    | None -> return classification)
              in
              push_env
                ( of_module_expr typ_vars module_expr None >>= fun value ->
                  set_env e.exp_env
                    (push_env
                       ( (match (x_ident, module_signature) with
                           | Some ident, IsFirstClassModule.Found signature_path
                             ->
                               set_signature_hint (Path.Pident ident)
                                 signature_path (of_expression typ_vars e)
                           | None, IsFirstClassModule.Found _
                           | _, IsFirstClassModule.Not_found _ ->
                               of_expression typ_vars e)
                       >>= fun e -> return (LetVar (None, x, [], value, e)) ))
                )
          | Texp_letexception _ ->
              error_message (Error "let_exception") SideEffect
                "Let of exception is not handled"
          | Texp_assert (e', _) ->
              Type.of_typ_expr false typ_vars e.exp_type >>= fun (typ, _, _) ->
              of_expression typ_vars e' >>= fun e' ->
              warn
                "an OCaml assertion failure is represented by an Unreachable \
                 result; prove that the assertion cannot fail"
              >>= fun () -> return (Assert (typ, e'))
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
              let* typ, _, _ = Type.of_typ_expr false typ_vars e.exp_type in
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
          | Texp_open (open_declaration, e) -> (
              let { open_expr; open_bound_items; _ } = open_declaration in
              let rec raw_module_expr_path (module_expr : Typedtree.module_expr)
                  : Path.t option =
                match module_expr.mod_desc with
                | Tmod_ident (path, _) -> Some path
                | Tmod_apply (functor_expr, argument_expr, _) ->
                    Option.bind (raw_module_expr_path functor_expr)
                      (fun functor_path ->
                        Option.map
                          (fun argument_path ->
                            Path.Papply (functor_path, argument_path))
                          (raw_module_expr_path argument_expr))
                | Tmod_constraint (inner, _, _, _) -> raw_module_expr_path inner
                | Tmod_structure _ | Tmod_functor _ | Tmod_apply_unit _
                | Tmod_unpack _ | Tmod_typed_hole ->
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
                | IsFirstClassModule.Not_found _ -> (
                    let rec root_functor_path module_expr =
                      match module_expr.mod_desc with
                      | Tmod_ident (path, _) -> Some path
                      | Tmod_apply (functor_expr, _, _)
                      | Tmod_apply_unit functor_expr
                      | Tmod_constraint (functor_expr, _, _, _) ->
                          root_functor_path functor_expr
                      | Tmod_structure _ | Tmod_functor _ | Tmod_unpack _
                      | Tmod_typed_hole ->
                          None
                    in
                    match root_functor_path open_expr with
                    | Some functor_path -> (
                        let* result_signature =
                          get_functor_result_signature functor_path
                        in
                        match result_signature with
                        | Some signature_path ->
                            return (IsFirstClassModule.Found signature_path)
                        | None -> return classification)
                    | None -> return classification)
              in
              let translate_body (opened_path : Path.t) =
                List.fold_right
                  (fun signature_item body ->
                    let ident = Types.signature_item_id signature_item in
                    set_module_path_alias (Path.Pident ident)
                      (Path.Pdot (opened_path, Ident.name ident))
                      body)
                  open_bound_items (of_expression typ_vars e)
              in
              match opened_signature with
              | IsFirstClassModule.Found signature_path -> (
                  match open_expr.mod_desc with
                  | Tmod_ident (opened_path, _) ->
                      (* A named module already has a stable Gallina path.  Use
                         it directly instead of introducing a local alias.
                         Besides producing simpler terms, this preserves the
                         indices of dependent module records in types captured
                         by generated well-founded recursive definitions. *)
                      set_signature_hint opened_path signature_path
                        (translate_body opened_path)
                  | _ ->
                      let opened_ident =
                        Ident.create_local
                          ("opened_module_"
                          ^ string_of_int
                              open_declaration.open_loc.loc_start.pos_cnum)
                      in
                      let opened_path = Path.Pident opened_ident in
                      let* opened_name = Name.of_ident false opened_ident in
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
                            set_module_path_alias source_path opened_path body)
                          source_paths body
                      in
                      let* body =
                        set_signature_hint opened_path signature_path body
                      in
                      let* body =
                        match raw_module_expr_path open_expr with
                        | Some ((Path.Pident _ | Path.Pdot _) as source_path) ->
                            let* source_path =
                              MixedPath.of_path false source_path
                            in
                            return
                              (map_assumption_types
                                 (Type.subst_mixed_path_root opened_name
                                    source_path)
                                 body)
                        | Some (Path.Papply _ | Path.Pextra_ty _) | None ->
                            return body
                      in
                      return
                        (LetVar (None, opened_name, [], opened_value, body)))
              | IsFirstClassModule.Not_found _ -> (
                  match ModulePathAliases.module_expr_path open_expr with
                  | Some opened_path -> translate_body opened_path
                  | None ->
                      error_message (Error "local_open") NotSupported
                        "A local open of an anonymous namespace is not \
                         supported."))
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

and of_match : type k.
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
  let rec variant_labels : type kind. kind general_pattern -> string list =
   fun pattern ->
    match pattern.pat_desc with
    | Tpat_variant (label, _, _) -> [ label ]
    | Tpat_alias (pattern, _, _, _, _) -> variant_labels pattern
    | Tpat_or (left, right, _) -> variant_labels left @ variant_labels right
    | Tpat_value pattern -> variant_labels (pattern :> value general_pattern)
    | _ -> []
  in
  let rec pattern_is_catch_all : type kind. kind general_pattern -> bool =
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
    | { c_lhs = { pat_type; _ } as c_lhs; _ } :: _ -> (
        let typ =
          try Ctype.full_expand ~may_forget_scope:false c_lhs.pat_env pat_type
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
              List.exists (fun { c_lhs; _ } -> pattern_is_catch_all c_lhs) cases
            in
            return
              ((not source_has_default)
              && ((not (Types.row_closed row_desc))
                 || (not
                       (Configuration.variant_row_is_exact configuration labels))
                 || not
                      (List.equal String.equal covered_labels
                         (List.sort_uniq String.compare labels))))
        | _ -> return false)
  in
  let* match_result_typ =
    match cases with
    | [] -> return (Type.Error "empty_match")
    | { c_rhs; _ } :: _ ->
        let* typ, _, _ = Type.of_typ_expr false typ_vars c_rhs.exp_type in
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
                 Type.local_typ_constructors_of_typs (List.map snd bound_vars)
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
               let* typ, _, _ = Type.of_typ_expr true typ_vars c_rhs.exp_type in
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
          let is_guarded = match guard with Some _ -> true | None -> false in
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
              (Pattern.Any, None, Assumption (Unreachable, match_result_typ, []));
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
    let t =
      if is_with_default_case && Option.is_none dep_match then
        RequiresAssumption (Unreachable, match_result_typ, t)
      else t
    in
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
and of_match_extensible : type kind.
    Name.t Name.Map.t -> t -> kind case list -> t Monad.t =
 fun (typ_vars : Name.t Name.Map.t) (e : t) (cases : kind case list) ->
  let* result_typ =
    match cases with
    | [] -> return (Type.Error "empty_extensible_match")
    | { c_rhs; _ } :: _ ->
        let* typ, _, _ = Type.of_typ_expr false typ_vars c_rhs.exp_type in
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
        "an unmatched OCaml exception is represented by an Unreachable result; \
         prove that this propagation path cannot occur"
  in
  return (MatchExtensible (e, result_typ, cases))

and of_match_variant : type kind.
    Name.t Name.Map.t -> t -> kind case list -> t Monad.t =
 fun (typ_vars : Name.t Name.Map.t) (e : t) (cases : kind case list) ->
  let* result_typ =
    match cases with
    | [] -> return (Type.Error "empty_dynamic_variant_match")
    | { c_rhs; _ } :: _ ->
        let* typ, _, _ = Type.of_typ_expr false typ_vars c_rhs.exp_type in
        return typ
  in
  let* nested_cases =
    cases
    |> Monad.List.map (fun { c_lhs; c_guard; c_rhs; _ } ->
        set_loc c_lhs.pat_loc
          (let* patterns = Pattern.of_dynamic_variant_patterns c_lhs in
           let* body = of_expression typ_vars c_rhs in
           match c_guard with
           | None -> return (List.map (fun pattern -> (pattern, body)) patterns)
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

(** Generate a variable and a "match" on this variable from a list of patterns.
*)
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
    | Tpat_any | Tpat_var _ | Tpat_alias ({ pat_desc = Tpat_any; _ }, _, _, _, _)
      ->
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
    | Tpat_var (ident, _, _) | Tpat_alias (_, ident, _, _, _) ->
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
               "@rocq.partial changes the translated result type to an \
                explicit partial computation; callers must preserve or \
                discharge its convergence requirement."
           in
           let definition_name =
             match source_binding_name case.vb_pat with
             | Some name ->
                 String.concat "." (enclosing_definition_path @ [ name ])
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
             let definition_name =
               match source_binding_name case.vb_pat with
               | Some name ->
                   String.concat "." (enclosing_definition_path @ [ name ])
               | None -> "anonymous"
             in
             let certificate =
               Configuration.get_termination_certificate configuration
                 (enclosing_definition_path
                 @ Option.to_list (source_binding_name case.vb_pat))
               |> Option.map (fun (measure, tactic) ->
                   { Definition.measure; tactic })
             in
             let* () =
               match certificate with
               | Some _ -> return ()
               | None ->
                   warn
                     "@rocq.wf introduces an abstract measure and admitted \
                      well-founded decrease obligations; replace both before \
                      relying on this definition."
             in
             return (Definition.WellFounded { definition_name; certificate }))
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
                   String.concat "." (enclosing_definition_path @ [ name ])
               | None -> "anonymous"
             in
             return (Definition.Convergent definition_name))
    | None, None, None -> return Definition.Structural
  in
  let* destructuring_cases =
    cases_with_attributes
    |> Monad.List.concat_map (fun ({ vb_pat; vb_expr; _ }, attributes) ->
        if is_simple_binding_pattern vb_pat then return []
        else
          set_env vb_expr.exp_env
            (set_loc vb_pat.pat_loc
               (let* pattern = Pattern.of_pattern vb_pat in
                match pattern with
                | None | Some Pattern.Any -> return []
                | Some pattern ->
                    let* translated_expression =
                      if Attribute.has_axiom_with_reason attributes then
                        return None
                      else
                        let* expression = of_expression typ_vars vb_expr in
                        return (Some expression)
                    in
                    let predefined_variables =
                      List.map snd (Name.Map.bindings typ_vars)
                    in
                    Typedtree.pat_bound_idents_full vb_pat
                    |> Monad.List.map (fun (ident, _, source_typ, _) ->
                        let* name = Name.of_ident true ident in
                        let* typ, _, new_typ_vars =
                          Type.of_typ_expr true typ_vars source_typ
                        in
                        let* typ =
                          Type.decode_var_tags new_typ_vars false typ
                        in
                        let new_typ_vars =
                          VarEnv.remove predefined_variables new_typ_vars
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
                                      Variable (MixedPath.of_name name, []) );
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
           (let source_name = source_binding_name p in
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
                      | Some name -> push_definition_path name translation
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
                        let* typ, _, _ = Type.of_typ_expr true typ_vars typ in
                        Type.decode_var_tags all_new_typ_vars false typ
                      in
                      let* argument_types =
                        Monad.List.map translate_segment argument_types
                      in
                      let* result_type = translate_segment result_type in
                      return (argument_types, result_type)
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
                  Option.map
                    (rewrite_sequence_calls
                       ~discharge_partial:
                         (match recursion_strategy with
                         | Definition.WellFounded _ | Definition.Convergent _ ->
                             true
                         | Definition.Partial _ | Definition.Structural -> false)
                       partial_definitions)
                    e_body
                in
                let e_body_typ =
                  match recursion_strategy with
                  | Definition.Partial _ -> Type.partialize e_body_typ
                  | Definition.WellFounded _ | Definition.Convergent _ ->
                      e_body_typ
                  | Definition.Structural ->
                      if
                        Option.fold ~none:false
                          ~some:(fun body ->
                            has_partial_recursion body
                            || has_partial_reference partial_definitions body)
                          e_body
                      then Type.partialize e_body_typ
                      else e_body_typ
                in
                let structs, instance_args =
                  match recursion_strategy with
                  | Definition.WellFounded _ | Definition.Partial _ -> ([], [])
                  | Definition.Structural | Definition.Convergent _ -> (
                      match (source_structs, is_rec) with
                      | [], true
                        when Configuration.is_without_guard_checking
                               configuration ->
                          let guard = Name.of_string_raw "_rocq_guard" in
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
                  | Definition.WellFounded _ | Definition.Partial _ -> return ()
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
                    is_notation = Attribute.has_mutual_as_notation attributes;
                  }
                in
                return (Some (header, e_body)))))
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
                  String.concat "." (enclosing_definition_path @ [ name ])
              | None -> "anonymous")
          | [] -> "anonymous"
        in
        let recursion =
          match recursion_strategy with
          | Definition.Structural when is_rec ->
              Definition.WellFoundedTerminates definition_name
          | Definition.Structural -> Definition.StructurallyTerminates
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
      term_environment =
        term_environment
        |> List.filter (fun value ->
            not (MixedPath.is_fargs_field_marker value))
        |> List.map Name.of_string_raw;
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
              let* p_typ = Type.of_type_expr_without_free_vars p.pat_type in
              let* e1_typ = Type.of_type_expr_without_free_vars e1.exp_type in
              return (Some { cast = p_typ; args = []; motive = e1_typ })
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
          | Tmod_structure _ | Tmod_functor _ | Tmod_unpack _ | Tmod_typed_hole
            ->
              None
        in
        let rec applied_functor_argument_count
            (module_expr : Typedtree.module_expr) : int =
          match module_expr.mod_desc with
          | Tmod_apply (functor_expr, _, _) ->
              1 + applied_functor_argument_count functor_expr
          | Tmod_constraint (functor_expr, _, _, _) ->
              applied_functor_argument_count functor_expr
          | Tmod_ident _ | Tmod_apply_unit _ | Tmod_structure _ | Tmod_functor _
          | Tmod_unpack _ | Tmod_typed_hole ->
              0
        in
        let rec applied_functor_arguments (module_expr : Typedtree.module_expr)
            : Typedtree.module_expr list =
          match module_expr.mod_desc with
          | Tmod_apply (functor_expr, argument, _) ->
              applied_functor_arguments functor_expr @ [ argument ]
          | Tmod_constraint (inner, _, _, _) -> applied_functor_arguments inner
          | Tmod_ident _ | Tmod_apply_unit _ | Tmod_structure _ | Tmod_functor _
          | Tmod_unpack _ | Tmod_typed_hole ->
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
        let rec cast_path ?source_signature_path ?source_classification path
            module_type module_type_path =
          let source_signature =
            match source_classification with
            | Some classification -> classification
            | None -> (
                match source_signature_path with
                | Some path -> IsFirstClassModule.Found path
                | None -> is_local_module_typ_first_class)
          in
          let* values = ModuleTypValues.get typ_vars module_type in
          let* module_typ_params_arity =
            ModuleTypParams.get_module_typ_typ_params_arity module_type
          in
          let typ_param_of_path (associated_path : string list) : Type.t Monad.t
              =
            match source_signature with
            | Found local_module_type_path ->
                let* base = PathName.of_path_with_convert false path in
                let* field_name = Name.of_strings false associated_path in
                let* field =
                  PathName.of_path_and_name_with_convert local_module_type_path
                    field_name
                in
                return (Type.Apply (MixedPath.Access (base, [ field ]), []))
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
          let mixed_path_of_value_or_typ (name : Name.t) (_ : Name.t list) :
              MixedPath.t Monad.t =
            match source_signature with
            | Found local_module_type_path ->
                let* base = PathName.of_path_with_convert false path in
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
          let field_value
              ({ ModuleTypValues.nested_module; record_operation; _ } :
                ModuleTypValues.t) mixed_path =
            match (record_operation, nested_module) with
            | Some operation, _ ->
                record_operation_expression ~source_root:path operation
            | None, None -> return (Variable (mixed_path, []))
            | None, Some { source_fields; target_type; target_signature } ->
                let source_path =
                  List.fold_left
                    (fun path field -> Path.Pdot (path, field))
                    path source_fields
                in
                let* env = get_env in
                let source_type =
                  (Env.find_module source_path env).Types.md_type
                in
                let* source_classification =
                  IsFirstClassModule.is_module_typ_first_class source_type
                    (Some source_path)
                in
                cast_path ~source_classification source_path target_type
                  target_signature
          in
          build_module ~typ_param_of_path ~field_value module_typ_params_arity
            values module_type_path mixed_path_of_value_or_typ
        in
        let signature_path_of_module_type ?signature_hint
            (module_type : Types.module_type) : Path.t Monad.t =
          let* classification =
            IsFirstClassModule.is_module_typ_first_class module_type None
          in
          match classification with
          | IsFirstClassModule.Found signature_path -> return signature_path
          | IsFirstClassModule.Not_found reason -> (
              match signature_hint with
              | Some signature_path -> return signature_path
              | None ->
                  raise
                    (Path.Pident
                       (Ident.create_local "module_coercion_signature_error"))
                    Unexpected
                    ("A module coercion requires a named Rocq signature.\n\n"
                   ^ reason))
        in
        let cast_module_expression ~(source_signature_path : Path.t)
            ~(target_signature_path : Path.t)
            (target_module_type : Types.module_type) (expression : t) :
            t Monad.t =
          if Path.same source_signature_path target_signature_path then
            return expression
          else
            let binding_ident = Ident.create_local "module_coercion" in
            let* binding_name = Name.of_ident false binding_ident in
            let* casted =
              cast_path ~source_signature_path (Path.Pident binding_ident)
                target_module_type target_signature_path
            in
            return (LetVar (None, binding_name, [], expression, casted))
        in
        let qualify_typed_path (typed_type : FunctorParameterHint.t option)
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
                    if Ident.same candidate ident then Some target else None)
                |> Option.value ~default:path
            | Path.Pdot (prefix, field) -> Path.Pdot (qualify prefix, field)
            | Path.Papply (functor_path, argument_path) ->
                Path.Papply (qualify functor_path, qualify argument_path)
            | Path.Pextra_ty (prefix, extra) ->
                Path.Pextra_ty (qualify prefix, extra)
          in
          qualify path
        in
        let rec coerce_functor_expression (source_functor_path : Path.t option)
            (source_result_signature : Path.t option)
            (target_typed_type : FunctorParameterHint.t option)
            (target_path_substitution : Subst.t) (expression : t)
            (source_type : Types.module_type) (target_type : Types.module_type)
            : t Monad.t =
          let* env = get_env in
          match
            (Env.scrape_alias env source_type, Env.scrape_alias env target_type)
          with
          | ( Mty_functor (Named (source_ident, source_parameter), source_result),
              Mty_functor (Named (target_ident, target_parameter), target_result)
            ) ->
              let target_typed_parameter, target_typed_result =
                match target_typed_type with
                | Some
                    {
                      FunctorParameterHint.module_type =
                        {
                          mty_desc =
                            Tmty_functor (Named (_, _, parameter), result);
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
              let typed_target_parameter_signature =
                Option.bind target_typed_parameter (fun parameter ->
                    ModuleTyp.get_module_typ_path_name
                      parameter.FunctorParameterHint.module_type)
                |> Option.map (Subst.module_path target_path_substitution)
                |> Option.map (qualify_typed_path target_typed_parameter)
              in
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
                let signature_hint =
                  match signature_hint with
                  | Some _ as hint -> hint
                  | None
                    when IsFirstClassModule.module_type_includes env
                           source_parameter target_parameter
                         && IsFirstClassModule.module_type_includes env
                              target_parameter source_parameter ->
                      (* Higher-order functor coercions can erase the path of
                         an otherwise identical named parameter signature.
                         The expected typed functor retains that path. *)
                      typed_target_parameter_signature
                  | None -> None
                in
                signature_path_of_module_type ?signature_hint source_parameter
              in
              let* target_parameter_signature =
                signature_path_of_module_type
                  ?signature_hint:typed_target_parameter_signature
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
              let application = Apply (expression, [ Some source_argument ]) in
              let source_result =
                match source_ident with
                | Some source_ident ->
                    Subst.modtype Subst.Keep
                      (Subst.add_module source_ident (Path.Pident target_ident)
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
                  (set_signature_hint (Path.Pident target_ident)
                     target_parameter_signature
                     (coerce_functor_expression source_functor_path
                        source_result_signature target_typed_result
                        target_path_substitution application source_result
                        target_result))
              in
              return (Functor (target_name, target_parameter_type, body))
          | Mty_functor _, _ | _, Mty_functor _ ->
              raise (Error "module_coercion_functor_shape") Unexpected
                "A module coercion cannot convert a functor to a non-functor."
          | _ ->
              let typed_target_signature =
                Option.bind target_typed_type (fun parameter ->
                    ModuleTyp.get_module_typ_path_name
                      parameter.FunctorParameterHint.module_type)
              in
              let source_signature_hint =
                match source_result_signature with
                | Some _ as hint -> hint
                | None
                  when IsFirstClassModule.module_type_includes env source_type
                         target_type
                       && IsFirstClassModule.module_type_includes env target_type
                            source_type ->
                    (* A higher-order functor parameter may have no path-based
                       result hint of its own, even though its declared result
                       is the same named signature as the expected functor.
                       Reuse the expected name only for mutually compatible
                       terminal module types; anonymous source results with
                       extra fields must still use their own record type. *)
                    typed_target_signature
                | None -> None
              in
              let* source_signature_path =
                signature_path_of_module_type
                  ?signature_hint:source_signature_hint source_type
              in
              let* target_signature_path =
                signature_path_of_module_type
                  ?signature_hint:typed_target_signature
                  target_type
              in
              let target_signature_path =
                Subst.module_path target_path_substitution target_signature_path
                |> qualify_typed_path target_typed_type
              in
              let* casted =
                cast_module_expression ~source_signature_path
                  ~target_signature_path target_type expression
              in
              let rec application arguments = function
                | Apply (function_, arguments')
                | SourceApply (function_, arguments', _) ->
                    application (arguments' @ arguments) function_
                | Variable (path, []) -> Some (path, arguments)
                | _ -> None
              in
              let* casted =
                match (source_functor_path, application [] expression) with
                | Some functor_path, Some (function_path, arguments)
                  when String.equal
                         (MixedPath.to_string function_path)
                         (Path.name functor_path)
                       && List.for_all Option.is_some arguments ->
                    let* functor_path_name =
                      PathName.of_path_with_convert false functor_path
                    in
                    let build_fargs_path =
                      {
                        PathName.path =
                          functor_path_name.PathName.path
                          @ [ functor_path_name.PathName.base ];
                        base = Name.of_string_raw "Build_FArgs";
                      }
                    in
                    let rec expression_as_type = function
                      | Variable (path, []) -> Some (Type.Apply (path, []))
                      | TypAnnotation (value, _) -> expression_as_type value
                      | _ -> None
                    in
                    let argument_types =
                      arguments |> List.filter_map Fun.id
                      |> List.map expression_as_type
                    in
                    if List.for_all Option.is_some argument_types then
                      let argument_types =
                        List.filter_map Fun.id argument_types
                      in
                      let fargs =
                        Type.Apply
                          ( MixedPath.PathName build_fargs_path,
                            List.map (fun typ -> (typ, false)) argument_types )
                        |> Type.to_coq None None
                        |> SmartPrint.to_string 1_000_000 0
                      in
                      let functor_names =
                        functor_path_name.PathName.path
                        @ [ functor_path_name.PathName.base ]
                      in
                      let application =
                        argument_types
                        |> List.map (fun argument ->
                            argument |> Type.to_coq None None
                            |> SmartPrint.to_string 1_000_000 0)
                      in
                      return
                        (map_assumption_types
                           (Type.specialize_functor_paths ~application
                              functor_names fargs)
                           casted)
                    else return casted
                | _ -> return casted
              in
              return casted
        in
        let apply_mod e1 e2 argument_coercion =
          let e1_mod_type = e1.mod_type in
          let expected_module_typ_for_e2 =
            match e1_mod_type with
            | Mty_functor (Named (_, module_typ_arg), _) -> Some module_typ_arg
            | _ -> None
          in
          let* expected_signature_path_for_e2 =
            expected_anonymous_signature e1 e1_mod_type
          in
          let* expected_typed_module_type_for_e2 =
            match root_functor_path e1 with
            | Some functor_path ->
                let parameter_index = applied_functor_argument_count e1 in
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
                            Subst.add_module ident argument_path substitution
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
            | _ -> (
                match e2 with
                | None ->
                    raise [] Unexpected
                      "Tmod_apply_unit was used with a non-generative functor"
                | Some e2 ->
                    let* e2 =
                      match (argument_coercion, expected_module_typ_for_e2) with
                      | Tcoerce_functor _, Some expected_module_type ->
                          let source_functor_path = root_functor_path e2 in
                          let* source_result_signature =
                            match source_functor_path with
                            | Some functor_path ->
                                get_functor_result_signature functor_path
                            | None -> return None
                          in
                          let* expression = of_module_expr typ_vars e2 None in
                          coerce_functor_expression source_functor_path
                            source_result_signature
                            expected_typed_module_type_for_e2
                            expected_typed_module_path_substitution expression
                            e2.mod_type expected_module_type
                      | _ ->
                          of_module_expr
                            ?expected_signature_path:
                              expected_signature_path_for_e2 typ_vars e2
                            expected_module_typ_for_e2
                    in
                    return [ Some (annotate_terminal_module e2) ])
          in
          let rec terminal_signature = function
            | TypAnnotation (_, Type.Signature (signature, parameters)) ->
                Some (signature, parameters)
            | Module (Type.Signature (signature, parameters), _) ->
                Some (signature, parameters)
            | LetVar (_, _, _, _, body)
            | LetFun (_, body)
            | LetTyp (_, _, _, body)
            | LetModuleUnpack (_, _, body)
            | ErrorMessage (body, _) ->
                terminal_signature body
            | _ -> None
          in
          let* current_module_substitutions =
            match (e1_mod_type, es) with
            | Mty_functor (Named (Some formal_ident, _), _), [ Some argument ]
              -> (
                match terminal_signature argument with
                | Some (signature, parameters) ->
                    let* formal_name = Name.of_ident false formal_ident in
                    return
                      (parameters
                      |> List.concat_map (fun (name, target) ->
                          match target with
                          | None -> []
                          | Some target ->
                              let signature_paths =
                                [
                                  signature.PathName.path
                                  @ [ signature.PathName.base ];
                                  [ signature.PathName.base ];
                                ]
                                |> List.sort_uniq compare
                              in
                              signature_paths
                              |> List.map (fun signature_path ->
                                  let field =
                                    {
                                      PathName.path = signature_path;
                                      base = name;
                                    }
                                  in
                                  let source =
                                    Type.Apply
                                      ( MixedPath.Access
                                          ( PathName.of_name [] formal_name,
                                            [ field ] ),
                                        [] )
                                  in
                                  (source, target))))
                | None -> return [])
            | Mty_functor (Named (None, _), _), _
            | Mty_functor (Unit, _), _
            | _, _ ->
                return []
          in
          let inherited_module_substitutions =
            match e1 with
            | SourceApply (_, _, source_type) ->
                source_type.module_substitutions
            | _ -> []
          in
          let module_substitutions =
            inherited_module_substitutions @ current_module_substitutions
          in
          let module_application_type =
            let placeholder = Type.Error "module_application" in
            {
              callee = placeholder;
              result = placeholder;
              specialization = placeholder;
              module_substitutions;
              module_assumption_telescope = None;
              assumption_telescope = None;
            }
          in
          let application = SourceApply (e1, es, module_application_type) in
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
            let* applied_child = get_applied_functor_child path in
            let* mixed_path =
              match applied_child with
              | None -> MixedPath.of_path false path
              | Some (target, parent_application) ->
                  let* target = PathName.of_path_with_convert false target in
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
                       (target, [ ("_fargs", parent_fargs) ], []))
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
        | Tmod_apply (e1, e2, coercion) -> apply_mod e1 (Some e2) coercion
        | Tmod_apply_unit e1 -> apply_mod e1 None Tcoerce_none
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
  let wrap_include_module_signature_hints (item : Typedtree.structure_item)
      (translation : t Monad.t) : t Monad.t =
    match item.str_desc with
    | Tstr_include { incl_mod; incl_type; _ } -> (
        let include_path =
          match incl_mod.mod_desc with
          | Tmod_ident (path, _)
          | Tmod_constraint ({ mod_desc = Tmod_ident (path, _); _ }, _, _, _) ->
              Some path
          | _ -> None
        in
        match (include_path, Env.scrape_alias item.str_env module_type) with
        | Some include_path, Mty_signature target_signature ->
            List.fold_right
              (fun source_item translation ->
                match source_item with
                | Types.Sig_module (source_ident, _, source_declaration, _, _)
                  -> (
                    let target =
                      target_signature
                      |> List.find_map (function
                        | Types.Sig_module
                            (target_ident, _, target_declaration, _, _)
                          when String.equal (Ident.name target_ident)
                                 (Ident.name source_ident) ->
                            Some (target_ident, target_declaration)
                        | _ -> None)
                    in
                    match target with
                    | None -> translation
                    | Some (target_ident, target_declaration) ->
                        let local_path = Path.Pident source_ident in
                        let source_path =
                          Path.Pdot (include_path, Ident.name source_ident)
                        in
                        let hinted_translation =
                          let* target_classification =
                            IsFirstClassModule.is_module_typ_first_class
                              target_declaration.Types.md_type
                              (Some (Path.Pident target_ident))
                          in
                          match target_classification with
                          | IsFirstClassModule.Found target_signature ->
                              set_signature_hint local_path target_signature
                                translation
                          | IsFirstClassModule.Not_found _ -> (
                              let* known_source_signature =
                                let* result =
                                  get_functor_result_signature source_path
                                in
                                match result with
                                | Some _ -> return result
                                | None -> get_signature_hint source_path
                              in
                              let* source_classification =
                                match known_source_signature with
                                | Some source_signature ->
                                    return
                                      (IsFirstClassModule.Found source_signature)
                                | None ->
                                    IsFirstClassModule.is_module_typ_first_class
                                      source_declaration.Types.md_type
                                      (Some source_path)
                              in
                              match source_classification with
                              | IsFirstClassModule.Found source_signature ->
                                  set_signature_hint local_path source_signature
                                    translation
                              | IsFirstClassModule.Not_found _ -> translation)
                        in
                        let aliased_translation =
                          set_module_path_alias local_path source_path
                            hinted_translation
                        in
                        let* local_name = Name.of_ident false source_ident in
                        let* source_mixed =
                          MixedPath.of_path false source_path
                        in
                        let* expression = aliased_translation in
                        return
                          (map_assumption_types
                             (Type.subst_mixed_path_root local_name source_mixed)
                             expression))
                | _ -> translation)
              incl_type translation
        | Some _, (Mty_ident _ | Mty_alias _ | Mty_functor _ | Mty_for_hole)
        | None, _ ->
            translation)
    | _ -> translation
  in
  match items with
  | [] ->
      set_env final_env
        ( ModuleTypParams.get_module_typ_typ_params_arity module_type
        >>= fun module_typ_params_arity ->
          let* values = ModuleTypValues.get typ_vars module_type in
          let local_mixed_path (access : Name.t list) =
            match List.rev access with
            | [] -> MixedPath.of_name (Name.of_string_raw "missing_access")
            | base :: rev_path ->
                MixedPath.PathName (PathName.of_name (List.rev rev_path) base)
          in
          let included_module (access : Name.t list) =
            match access with
            | [] -> return None
            | root :: _ -> (
                let longident = Longident.Lident (Name.to_string root) in
                let local_path =
                  try
                    Some
                      (fst
                         (Env.lookup_module ~use:false ~loc:Location.none
                            longident final_env))
                  with Not_found | Env.Error _ -> None
                in
                match local_path with
                | None -> return None
                | Some local_path -> (
                    let* source = get_module_path_alias local_path in
                    match source with
                    | None -> return None
                    | Some source ->
                        let* signature = get_signature_hint local_path in
                        let* signature =
                          match signature with
                          | Some _ -> return signature
                          | None -> (
                              let* result =
                                get_functor_result_signature source
                              in
                              match result with
                              | Some _ -> return result
                              | None -> get_signature_hint source)
                        in
                        return (Some (root, source, signature))))
          in
          let flattened_target_field_name root field =
            let field = Name.to_string field in
            let module_prefix = Name.to_string root ^ "_" in
            match
              Str.search_forward (Str.regexp_string module_prefix) field 0
            with
            | index ->
                String.sub field 0 index
                ^ String.sub field
                    (index + String.length module_prefix)
                    (String.length field - index - String.length module_prefix)
            | exception Not_found -> field
          in
          let source_field_name root field source_signature access =
            let strip_value_suffix name =
              let suffix = "_value" in
              if String.ends_with ~suffix name then
                String.sub name 0 (String.length name - String.length suffix)
              else name
            in
            let access_fields =
              match access with [] -> [] | _ :: fields -> fields
            in
            let join fields =
              fields |> List.map Name.to_string |> String.concat "_"
            in
            let candidates =
              [
                join access_fields;
                access_fields
                |> List.map (fun name ->
                    Name.of_string_raw
                      (strip_value_suffix (Name.to_string name)))
                |> join;
                flattened_target_field_name root field;
              ]
              |> List.filter (fun name -> not (String.equal name ""))
              |> List.sort_uniq String.compare
            in
            let* module_type = get_module_type_hint source_signature in
            let* public_fields =
              match module_type with
              | Some module_type -> (
                  match Env.scrape_alias final_env module_type with
                  | Mty_signature signature ->
                      signature
                      |> Monad.List.map (fun item ->
                          let is_value =
                            match item with
                            | Types.Sig_value _ -> true
                            | _ -> false
                          in
                          let* name =
                            Name.of_ident is_value
                              (Types.signature_item_id item)
                          in
                          return (Name.to_string name))
                  | Mty_ident _ | Mty_alias _ | Mty_functor _ | Mty_for_hole ->
                      return [])
              | None -> return []
            in
            return
              (candidates
              |> List.find_opt (fun candidate ->
                  List.mem candidate public_fields)
              |> Option.value ~default:(flattened_target_field_name root field)
              )
          in
          let mixed_path_of_value_or_typ (field : Name.t) (access : Name.t list)
              : MixedPath.t Monad.t =
            let* included = included_module access in
            match (included, access) with
            | Some (root, _, Some source_signature), _ :: _ ->
                let* source_field =
                  source_field_name root field source_signature access
                in
                let* source_signature =
                  PathName.of_path_with_convert false source_signature
                in
                let projection =
                  {
                    PathName.path =
                      source_signature.PathName.path
                      @ [ source_signature.PathName.base ];
                    base = Name.of_string_raw source_field;
                  }
                in
                return
                  (MixedPath.Access (PathName.of_name [] root, [ projection ]))
            | Some (_, source, None), _ :: fields ->
                let source =
                  List.fold_left
                    (fun path field -> Path.Pdot (path, Name.to_string field))
                    source fields
                in
                MixedPath.of_path true source
            | None, _ | Some _, [] -> (
                match List.rev access with
                | [] ->
                    raise
                      (MixedPath.of_name (Name.of_string_raw "missing_access"))
                      Unexpected "A module field has an empty local access path"
                | _ :: _ -> return (local_mixed_path access))
          in
          let field_value
              ({ ModuleTypValues.access; nested_module; record_operation; _ } :
                ModuleTypValues.t) mixed_path =
            match (record_operation, nested_module) with
            | Some operation, _ -> (
                let* included = included_module access in
                match included with
                | Some (root, source, _) ->
                    let strip_root path =
                      match path with
                      | first :: remaining
                        when String.equal first (Name.to_string root) ->
                          remaining
                      | _ -> path
                    in
                    let operation =
                      match operation with
                      | ModuleTypValues.RecordMake
                          (path, parameter_count, fields, canonical_type_path)
                        ->
                          ModuleTypValues.RecordMake
                            ( strip_root path,
                              parameter_count,
                              fields,
                              canonical_type_path )
                      | ModuleTypValues.RecordGet
                          (path, parameter_count, field, canonical_type_path) ->
                          ModuleTypValues.RecordGet
                            ( strip_root path,
                              parameter_count,
                              field,
                              canonical_type_path )
                    in
                    record_operation_expression ~source_root:source operation
                | None -> record_operation_expression operation)
            | None, Some _ when List.length access = 1 ->
                return (Variable (local_mixed_path access, []))
            | None, Some _ | None, None -> return (Variable (mixed_path, []))
          in
          build_module ~field_value module_typ_params_arity values
            signature_path mixed_path_of_value_or_typ )
  | item :: items ->
      set_env item.str_env
        (set_loc item.str_loc
           ( wrap_include_module_signature_hints item
               (of_structure typ_vars signature_path module_type items final_env)
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
                 let expected_module_type =
                   match (mb_id, Env.scrape_alias item.str_env module_type) with
                   | Some ident, Mty_signature target_signature ->
                       target_signature
                       |> List.find_map (function
                         | Types.Sig_module
                             (target_ident, _, target_declaration, _, _)
                           when String.equal (Ident.name target_ident)
                                  (Ident.name ident) ->
                             Some target_declaration.Types.md_type
                         | _ -> None)
                       |> Option.value ~default:mb_expr.mod_type
                   | ( None,
                       ( Mty_ident _ | Mty_alias _ | Mty_signature _
                       | Mty_functor _ | Mty_for_hole ) )
                   | ( Some _,
                       (Mty_ident _ | Mty_alias _ | Mty_functor _ | Mty_for_hole)
                     ) ->
                       mb_expr.mod_type
                 in
                 of_module_expr typ_vars mb_expr (Some expected_module_type)
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
                 (* Each following structure item carries the environment
                    produced by the open, so no Gallina term is needed. *)
                 return e_next
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
                   | Some (Path.Pident ident) -> get_included_record_alias ident
                   | Some _ -> return None
                   | None -> return None
                 in
                 match included_record_alias with
                 | Some alias ->
                     of_include_record_alias typ_vars alias incl_type e_next
                 | None -> (
                     let incl_module_type = Types.Mty_signature incl_type in
                     let* is_first_class =
                       IsFirstClassModule.is_module_typ_first_class
                         incl_module_type path
                     in
                     match is_first_class with
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
                               (LetVar (None, name, [], included_module, e_next))
                         )
                     | Not_found reason -> (
                         match path with
                         | Some path ->
                             let* env = get_env in
                             let required_names =
                               match Env.scrape_alias env module_type with
                               | Mty_signature signature ->
                                   signature
                                   |> List.map Types.signature_item_id
                                   |> List.map Ident.name
                               | Mty_ident _ | Mty_alias _ | Mty_functor _
                               | Mty_for_hole ->
                                   []
                             in
                             let required_items =
                               incl_type
                               |> List.filter (fun item ->
                                   List.mem
                                     (Ident.name (Types.signature_item_id item))
                                     required_names)
                             in
                             of_include_namespace typ_vars path module_type
                               required_items e_next
                         | None ->
                             raise
                               (ErrorMessage
                                  (e_next, "include_without_named_signature"))
                               NotSupported
                               ("We did not find a signature name for the \
                                 include of this module\n\n" ^ reason))))
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
                >>= fun (_, _, new_typ_vars) ->
                return (List.map fst new_typ_vars)
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

and build_namespace_signature (typ_vars : Name.t Name.Map.t)
    (source_root : Path.t) (source_signature : Path.t option)
    (target_module_type : Types.module_type) (target_signature : Path.t) :
    t Monad.t =
  let append_fields root fields =
    List.fold_left (fun path field -> Path.Pdot (path, field)) root fields
  in
  let* typ_params_arity =
    ModuleTypParams.get_module_typ_typ_params_arity target_module_type
  in
  let* values = ModuleTypValues.get typ_vars target_module_type in
  let field_value
      ({ ModuleTypValues.nested_module; record_operation; _ } :
        ModuleTypValues.t) mixed_path =
    match (record_operation, nested_module) with
    | Some operation, _ -> record_operation_expression ~source_root operation
    | None, Some { source_fields; target_type; target_signature } ->
        let* nested_source_signature =
          match source_signature with
          | None -> return None
          | Some source_signature ->
              let rec descend signature = function
                | [] -> return (Some signature)
                | field :: fields -> (
                    let* nested = get_result_module_field signature field in
                    match nested with
                    | Some nested -> descend nested fields
                    | None -> return None)
              in
              descend source_signature source_fields
        in
        build_namespace_signature typ_vars
          (append_fields source_root source_fields)
          nested_source_signature target_type target_signature
    | None, None -> return (Variable (mixed_path, []))
  in
  let mixed_path_of_value_or_typ (field : Name.t) (access : Name.t list) =
    match source_signature with
    | None ->
        let source_path =
          append_fields source_root (List.map Name.to_string access)
        in
        MixedPath.of_path true source_path
    | Some source_signature ->
        let* root = PathName.of_path_with_convert false source_root in
        let rec fields signature = function
          | [] -> return []
          | field :: remaining ->
              let field_name = Name.to_string field in
              let* signature_name =
                PathName.of_path_with_convert false signature
              in
              let projected =
                {
                  PathName.path =
                    signature_name.PathName.path @ [ signature_name.base ];
                  base = field;
                }
              in
              let* nested = get_result_module_field signature field_name in
              let next_signature = Option.value nested ~default:signature in
              let* remaining = fields next_signature remaining in
              return (projected :: remaining)
        in
        let* fields = fields source_signature [ field ] in
        return
          (match fields with
          | [] -> MixedPath.PathName root
          | _ :: _ -> MixedPath.Access (root, fields))
  in
  build_module ~field_value typ_params_arity values target_signature
    mixed_path_of_value_or_typ

(** Include the fields needed by an enclosing first-class signature from a
    translated namespace module. Namespace modules do not themselves have a
    first-class signature record, so their fields are referenced by ordinary
    qualified Gallina paths. *)
and of_include_namespace (typ_vars : Name.t Name.Map.t) (module_path : Path.t)
    (target_module_type : Types.module_type) (signature : Types.signature)
    (e_next : t) : t Monad.t =
  match signature with
  | [] -> return e_next
  | signature_item :: signature -> (
      of_include_namespace typ_vars module_path target_module_type signature
        e_next
      >>= fun e_next ->
      let ident = Types.signature_item_id signature_item in
      let source_path = Path.Pdot (module_path, Ident.name ident) in
      match signature_item with
      | Sig_value (_, { Types.val_type; _ }, _) ->
          let* name = Name.of_ident true ident in
          let* _, _, new_typ_vars = Type.of_typ_expr true typ_vars val_type in
          let typ_vars = List.map fst new_typ_vars in
          let implicits =
            typ_vars
            |> List.map (fun name ->
                let name = Name.to_string name in
                (name, name))
          in
          let* source = MixedPath.of_path true source_path in
          return
            (LetVar (None, name, typ_vars, Variable (source, implicits), e_next))
      | Sig_type (_, { Types.type_params; _ }, _, _) ->
          let* name = Name.of_ident false ident in
          let* parameters =
            Monad.List.map Type.of_type_expr_variable type_params
          in
          let* source = MixedPath.of_path false source_path in
          let source =
            Type.Apply
              ( source,
                List.map
                  (fun parameter -> (Type.Variable parameter, false))
                  parameters )
          in
          return (LetTyp (name, parameters, source, e_next))
      | Sig_module (_, _, source_declaration, _, _) -> (
          let* name = Name.of_ident false ident in
          let* env = get_env in
          let target_declaration =
            match Env.scrape_alias env target_module_type with
            | Mty_signature target_signature ->
                target_signature
                |> List.find_map (function
                  | Types.Sig_module (target_ident, _, target_declaration, _, _)
                    when String.equal (Ident.name target_ident)
                           (Ident.name ident) ->
                      Some (target_ident, target_declaration)
                  | _ -> None)
            | Mty_ident _ | Mty_alias _ | Mty_functor _ | Mty_for_hole -> None
          in
          match target_declaration with
          | Some (target_ident, target_declaration) -> (
              let longident =
                Path.name source_path |> String.split_on_char '.'
                |> Longident.unflatten |> Option.get |> Location.mknoloc
              in
              let source_module =
                {
                  mod_desc = Tmod_ident (source_path, longident);
                  mod_loc = Location.none;
                  mod_type = source_declaration.Types.md_type;
                  mod_env = env;
                  mod_attributes = source_declaration.Types.md_attributes;
                }
              in
              let* source =
                of_module_expr typ_vars source_module
                  (Some target_declaration.Types.md_type)
              in
              let source = mark_module_reference source in
              let* source_classification =
                let* known_source_signature =
                  let* signature = get_functor_result_signature source_path in
                  match signature with
                  | Some _ -> return signature
                  | None -> get_signature_hint source_path
                in
                match known_source_signature with
                | Some source_signature ->
                    return (IsFirstClassModule.Found source_signature)
                | None ->
                    IsFirstClassModule.is_module_typ_first_class
                      source_declaration.Types.md_type (Some source_path)
              in
              let* source =
                let* target_signature =
                  IsFirstClassModule.is_module_typ_first_class
                    target_declaration.Types.md_type
                    (Some (Path.Pident target_ident))
                in
                match target_signature with
                | IsFirstClassModule.Found target_signature -> (
                    let source_signature_path =
                      match source_classification with
                      | IsFirstClassModule.Found source_signature ->
                          Some source_signature
                      | IsFirstClassModule.Not_found _ -> None
                    in
                    let translation =
                      build_namespace_signature typ_vars source_path
                        source_signature_path target_declaration.Types.md_type
                        target_signature
                    in
                    match source_classification with
                    | IsFirstClassModule.Found source_signature ->
                        set_signature_hint source_path source_signature
                          (let* translation = translation in
                           return (Some translation))
                    | IsFirstClassModule.Not_found _ ->
                        let* translation = translation in
                        return (Some translation))
                | IsFirstClassModule.Not_found _ -> (
                    match source_classification with
                    | IsFirstClassModule.Found _ -> return (Some source)
                    | IsFirstClassModule.Not_found _ -> return None)
              in
              match source with
              | Some source -> return (LetVar (None, name, [], source, e_next))
              | None -> return e_next)
          | None ->
              let* source = MixedPath.of_path false source_path in
              return (LetVar (None, name, [], Variable (source, []), e_next)))
      | Sig_typext _ | Sig_modtype _ | Sig_class _ | Sig_class_type _ ->
          return e_next)

and of_include_record_alias (typ_vars : Name.t Name.Map.t)
    (alias : IncludedRecordAliasTarget.t) (signature : Types.signature)
    (e_next : t) : t Monad.t =
  match signature with
  | [] -> return e_next
  | signature_item :: signature -> (
      of_include_record_alias typ_vars alias signature e_next >>= fun e_next ->
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
          ("M", SmartPrint.to_string 1_000_000 0 (Type.to_coq None None monad));
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

let rewrite_well_founded_calls
    (recursive_calls : (Name.t * int * (t -> t)) list)
    (recurse_name : Name.t)
    (certificate_tactic : string option) (e : t) : t =
  let map_option f = Option.map f in
  let rec flatten_application function_ arguments =
    match function_ with
    | (Apply (inner, preceding) | SourceApply (inner, preceding, _))
      when List.for_all (function None -> false | Some _ -> true) preceding ->
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
        LetVar (operator, name, parameters, rewrite value, rewrite body)
    | LetFun (definition, body) ->
        let cases =
          definition.Definition.cases
          |> List.map (fun (header, body) -> (header, Option.map rewrite body))
        in
        LetFun ({ definition with Definition.cases }, rewrite body)
    | LetTyp (name, parameters, typ, body) ->
        LetTyp (name, parameters, typ, rewrite body)
    | LetModuleUnpack (name, path, body) ->
        LetModuleUnpack (name, path, rewrite body)
    | Match (scrutinee, dependent, cases, default) ->
        let scrutinee = rewrite scrutinee in
        let cases =
          List.map
            (fun (pattern, cast, body) -> (pattern, cast, rewrite body))
            cases
        in
        if Option.is_some certificate_tactic && Option.is_none dependent then
          MatchWithEquation (scrutinee, cases, default)
        else Match (scrutinee, dependent, cases, default)
    | MatchWithEquation (scrutinee, cases, default) ->
        MatchWithEquation
          ( rewrite scrutinee,
            List.map
              (fun (pattern, cast, body) -> (pattern, cast, rewrite body))
              cases,
            default )
    | MatchExtensible (scrutinee, typ, cases) ->
        MatchExtensible
          ( rewrite scrutinee,
            typ,
            List.map (fun (pattern, body) -> (pattern, rewrite body)) cases )
    | MatchVariant (scrutinee, typ, cases) ->
        MatchVariant
          ( rewrite scrutinee,
            typ,
            List.map (fun (pattern, body) -> (pattern, rewrite body)) cases )
    | Record fields ->
        Record
          (List.map
             (fun (name, arity, value) -> (name, arity, rewrite value))
             fields)
    | Field (value, name) -> Field (rewrite value, name)
    | IfThenElse (condition, then_, else_) ->
        let condition = rewrite condition in
        let then_ = rewrite then_ in
        let else_ = rewrite else_ in
        if Option.is_some certificate_tactic then
          IfThenElseWithEquation (condition, then_, else_)
        else IfThenElse (condition, then_, else_)
    | IfThenElseWithEquation (condition, then_, else_) ->
        IfThenElseWithEquation (rewrite condition, rewrite then_, rewrite else_)
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
    | PropagatedAssumption (kind, typ, body) ->
        PropagatedAssumption (kind, typ, rewrite body)
    | ErrorArray values -> ErrorArray (List.map rewrite values)
    | ErrorMessage (body, message) -> ErrorMessage (rewrite body, message)
  and rewrite_application result_typ function_ arguments =
    let function_, arguments = flatten_application function_ arguments in
    let recursive_call =
      match expression_function_name function_ with
      | Some candidate ->
          let candidate_terminal =
            candidate |> drop_closing_parentheses |> final_path_component
          in
          let exact =
            List.find_opt
              (fun (recursive_name, _, _) ->
                String.equal candidate_terminal
                  (definition_final_component (Name.to_string recursive_name)))
              recursive_calls
          in
          (match exact with
          | Some _ -> exact
          | None ->
              List.find_opt
                (fun (recursive_name, _, _) ->
                  function_name_matches candidate
                    (Name.to_string recursive_name))
                recursive_calls)
      | None -> None
    in
    let supplied_arguments =
      List.filter_map (fun argument -> argument) arguments
    in
    match recursive_call with
    | Some (_, argument_count, inject)
      when List.length supplied_arguments = argument_count
           && List.length arguments = argument_count ->
      let state =
        match supplied_arguments with
        | [] -> Tuple []
        | [ value ] -> rewrite value
        | values -> Tuple (List.map rewrite values)
      in
      Apply
        ( Variable (MixedPath.of_name recurse_name, []),
          [
            Some (inject state);
            Some
              (match certificate_tactic with
              | Some tactic -> Ltac (Raw tactic)
              | None -> Variable (MixedPath.of_name (Name.of_string_raw "_"), []));
          ] )
    | _ ->
      let function_ = rewrite function_ in
      let arguments = List.map (map_option rewrite) arguments in
      match result_typ with
      | None -> Apply (function_, arguments)
      | Some result_typ -> SourceApply (function_, arguments, result_typ)
  in
  rewrite e

let rewrite_local_well_founded_calls (recursive_name : Name.t)
    (recurse_name : Name.t) (argument_count : int)
    (certificate_tactic : string option) (e : t) : t =
  rewrite_well_founded_calls
    [ (recursive_name, argument_count, Fun.id) ]
    recurse_name certificate_tactic e

let rewrite_mutual_well_founded_calls
    (recursive_calls : (Name.t * int * (t -> t)) list)
    (recurse_name : Name.t) (certificate_tactic : string) (e : t) : t =
  rewrite_well_founded_calls recursive_calls recurse_name
    (Some certificate_tactic) e

let is_named_expression (names : string list) (e : t) : bool =
  match expression_function_name e with
  | Some candidate -> List.exists (function_name_matches candidate) names
  | None -> false

let is_named_application (names : string list) (e : t) : bool =
  match e with
  | Apply (function_, _) | SourceApply (function_, _, _) -> (
      match expression_function_name function_ with
      | Some candidate -> List.exists (function_name_matches candidate) names
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
  | Type.Apply (path, [ (monad, _); _ ])
    when let path = MixedPath.to_string path in
         path = "RocqOfOCaml.Partial.Resumption.t"
         || string_ends_with path ".Partial.Resumption.t" ->
      Some monad
  | _ -> None

(** Lift one source expression into the explicit partial-computation syntax.
    Recursive calls and calls to other configured partial definitions already
    have the lifted type. Pure branches become [Done]. In a monadic partial
    computation, ordinary source-monad actions become [Bind] nodes, while a
    lifted recursive/partial action composes with [Resumption.bind]. *)
let rec lift_partial_expression ~(resumption : bool) ~(monad : Type.t option)
    ~(recursive_names : string list) ~(partial_definitions : string list)
    (e : t) : t =
  let rec flatten_application e =
    match e with
    | (Apply (function_, arguments) | SourceApply (function_, arguments, _))
      when List.for_all (function None -> false | Some _ -> true) arguments ->
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
    is_partial e || has_partial_recursion e
    || has_partial_reference partial_definitions e
  in
  let done_ value =
    apply_runtime
      ?monad:(if resumption then monad else None)
      (if resumption then "Resumption" else "Delay")
      "Done" [ value ]
  in
  let bind computation continuation =
    apply_runtime ?monad "Resumption" "Compose" [ computation; continuation ]
  in
  let action action continuation =
    apply_runtime ?monad "Resumption" "Bind" [ action; continuation ]
  in
  let suspend computation =
    let thunk = Function (Name.of_string_raw "_", None, computation) in
    apply_runtime
      ?monad:(if resumption then monad else None)
      (if resumption then "Resumption" else "Delay")
      "Tau" [ thunk ]
  in
  let continuation name typ body = Function (name, typ, recurse body) in
  let runtime_sequence_value value_name =
    Variable
      ( MixedPath.PathName
          {
            PathName.path =
              [
                Name.of_string_raw "RocqOfOCaml"; Name.of_string_raw "OCamlSeq";
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
    | Function (name, typ, body) -> Function (name, typ, recurse body)
    | _ ->
        let value = Name.of_string_raw "_rocq_partial_argument" in
        Function
          ( value,
            None,
            recurse
              (Apply
                 (callback, [ Some (Variable (MixedPath.of_name value, [])) ]))
          )
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
    | Apply (function_, arguments) | SourceApply (function_, arguments, _) ->
        lift_seq_map function_ arguments
    | _ -> None
  in
  match lifted_seq_map with
  | Some e -> e
  | None when is_named_application recursive_names e -> suspend e
  | None when is_partial e -> e
  | None -> (
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
              List.map (fun (pattern, body) -> (pattern, recurse body)) cases )
      | MatchVariant (scrutinee, typ, cases) ->
          MatchVariant
            ( scrutinee,
              typ,
              List.map (fun (pattern, body) -> (pattern, recurse body)) cases )
      | IfThenElse (condition, then_, else_) ->
          IfThenElse (condition, recurse then_, recurse else_)
      | IfThenElseWithEquation (condition, then_, else_) ->
          IfThenElseWithEquation (condition, recurse then_, recurse else_)
      | LetVar (None, name, parameters, value, body) ->
          LetVar (None, name, parameters, value, recurse body)
      | LetFun (definition, body)
        when match definition.Definition.recursion_strategy with
             | Definition.Partial _ -> true
             | Definition.Structural | Definition.WellFounded _
             | Definition.Convergent _ ->
                 false ->
          let local_partial_names =
            definition.Definition.cases
            |> List.map (fun (header, _) -> Name.to_string header.Header.name)
          in
          LetFun
            ( definition,
              lift_partial_expression ~resumption ~monad ~recursive_names
                ~partial_definitions:(local_partial_names @ partial_definitions)
                body )
      | LetFun (definition, body)
        when has_partial_recursion body
             || has_partial_reference partial_definitions body ->
          LetFun (definition, recurse body)
      | LetVar (Some _, name, [], value, body) when resumption ->
          let continuation = continuation name None body in
          if contains_partial value then bind (recurse value) continuation
          else action value continuation
      | Apply (function_, [ Some value; Some (Function (name, typ, body)) ])
      | SourceApply
          (function_, [ Some value; Some (Function (name, typ, body)) ], _)
        when resumption
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
      | SourceApply (function_, [ Some value; Some continuation_function ], _)
        when resumption
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
                       [ Some (Variable (MixedPath.of_name value_name, [])) ] ))
              )
          in
          if contains_partial value then bind (recurse value) continuation
          else action value continuation
      | Apply (function_, [ Some mapper; Some computation ])
      | SourceApply (function_, [ Some mapper; Some computation ], _)
        when resumption
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
                        [ Some (Variable (MixedPath.of_name value_name, [])) ]
                      )) ))
      | Return (_, value) -> done_ value
      | Apply (function_, [ Some value ])
      | SourceApply (function_, [ Some value ], _)
        when match expression_function_name function_ with
             | Some name -> function_name_matches name "return"
             | None -> false ->
          done_ value
      | ErrorMessage (body, message) -> ErrorMessage (recurse body, message)
      | TypAnnotation (body, typ) ->
          TypAnnotation (recurse body, Type.partialize typ)
      | _ when resumption ->
          let result = Name.of_string_raw "_rocq_partial_value" in
          action e
            (Function
               (result, None, done_ (Variable (MixedPath.of_name result, []))))
      | _ -> done_ e)

let guard_partial_body (resumption : bool) (monad : Type.t option) (body : t) :
    t =
  let thunk = Function (Name.of_string_raw "_", None, body) in
  apply_runtime
    ?monad:(if resumption then monad else None)
    (if resumption then "Resumption" else "Delay")
    "Tau" [ thunk ]

let to_coq_implicit (implicit : string * string) : SmartPrint.t =
  let name, value = implicit in
  nest (parens (!^name ^^ !^":=" ^^ !^value))

let to_coq_assumed_value (kind : assumption_kind) (typ : Type.t) : SmartPrint.t
    =
  let projection =
    match kind with
    | Unreachable -> "@RocqOfOCaml.Basics.unreachable"
    | Unimplemented -> "@RocqOfOCaml.Basics.unimplemented"
    | ModuleContext ->
        failwith "a module context cannot be rendered as an assumed value"
  in
  parens
    (nest
       (!^projection ^^ Type.to_coq None (Some Type.Context.Apply) typ ^^ !^"_"))

(** Render a translated function that escapes as a polymorphic record field
    without eta-expanding its generated assumption telescope. A bare Rocq
    reference eagerly resolves type-class arguments, while [@value] retains them
    as explicit products. Local values in generated functors have one leading
    [FArgs] argument, which belongs to the enclosing record rather than to the
    field and must therefore be instantiated here. *)
let to_coq_first_class_alias ~(local_fargs : bool)
    ~(compact_aliases : int Name.Map.t) ~(arity : int) (expression : t) :
    SmartPrint.t option =
  let rec head = function
    | RequiresAssumption (_, _, body) | PropagatedAssumption (_, _, body) ->
        head body
    | SourceApply (Variable (path, []), [], source_type) ->
        Some (path, source_type)
    | _ -> None
  in
  let same_requirements left right =
    List.length left = List.length right
    && List.for_all2
         (fun left right -> compare_assumption_requirement left right = 0)
         left right
  in
  match head expression with
  | None -> None
  | Some (path, source_type) ->
      let is_unqualified_local =
        match path with
        | MixedPath.PathName { PathName.path = []; _ } -> true
        | MixedPath.PathName _ | MixedPath.Access _ | MixedPath.AppliedAccess _
          ->
            false
      in
      let source_requirements =
        Option.value source_type.assumption_telescope ~default:[]
      in
      let field_requirements =
        assumption_requirements expression
        |> List.filter (fun (kind, _) -> kind <> ModuleContext)
        |> stable_uniq_assumptions
      in
      if
        (not local_fargs) || (not is_unqualified_local)
        || Name.Map.find_opt (MixedPath.get_pathName_base path) compact_aliases
           <> Some arity
        || Type.nb_forall_typs source_type.callee <> 0
        || List.length source_requirements <> arity
        || not (same_requirements source_requirements field_requirements)
      then None
      else
        Some (nest (separate space [ !^"@" ^-^ MixedPath.to_coq path; !^"_" ]))

let to_coq_record_fields ?(local_fargs = false)
    ?(compact_aliases = Name.Map.empty)
    (field_implicits : (Name.t * SmartPrint.t) list)
    (render_expression : t -> SmartPrint.t)
    (fields : (PathName.t * int * t) list) : SmartPrint.t =
  if fields = [] then !^"ltac:(constructor)"
  else
    let render_field_implicits expression =
      let requires_module_context =
        assumption_requirements expression
        |> List.exists (fun (kind, _) -> kind = ModuleContext)
      in
      field_implicits
      |> List.filter (fun (name, _) ->
          not
            (requires_module_context
            && String.equal (Name.to_string name) "_fargs"))
      |> List.map (fun (name, value) ->
          parens (Name.to_coq name ^^ !^":=" ^^ value))
    in
    nest
      (!^"{|"
      ^^ separate space
           (fields
           |> List.map (fun (field, arity, expression) ->
               let first_class_alias =
                 if arity = 0 then None
                 else
                   to_coq_first_class_alias ~local_fargs ~compact_aliases ~arity
                     expression
               in
               nest
                 (nest
                    (PathName.to_coq field
                    ^^ separate space
                         (render_field_implicits expression
                         @
                         match first_class_alias with
                         | Some _ -> []
                         | None -> Pp.n_underscores arity)
                    ^^ !^":=")
                 ^^ (match first_class_alias with
                   | Some alias -> alias
                   | None -> render_expression expression)
                 ^-^ !^";")))
      ^^ !^"|}")

let to_coq_module_fields ?(local_fargs = false)
    ?(compact_aliases = Name.Map.empty)
    (field_implicits : (Name.t * SmartPrint.t) list)
    (render_expression : t -> SmartPrint.t)
    (fields : (PathName.t * int * t) list) : SmartPrint.t =
  let render_field_implicits expression =
    let requires_module_context =
      assumption_requirements expression
      |> List.exists (fun (kind, _) -> kind = ModuleContext)
    in
    field_implicits
    |> List.filter (fun (name, _) ->
        not
          (requires_module_context
          && String.equal (Name.to_string name) "_fargs"))
    |> List.map (fun (name, value) ->
        parens (Name.to_coq name ^^ !^":=" ^^ value))
  in
  group
    (!^"{|" ^^ newline
    ^^ indent
         (separate (!^";" ^^ newline)
            (fields
            |> List.map (fun (field, arity, expression) ->
                let first_class_alias =
                  if arity = 0 then None
                  else
                    to_coq_first_class_alias ~local_fargs ~compact_aliases
                      ~arity expression
                in
                nest
                  (group
                     (nest
                        (PathName.to_coq field
                        ^^ separate space
                             (render_field_implicits expression
                             @
                             match first_class_alias with
                             | Some _ -> []
                             | None -> Pp.n_underscores arity))
                     ^^ !^":=")
                  ^^
                  match first_class_alias with
                  | Some alias -> alias
                  | None -> render_expression expression))))
    ^^ newline ^^ !^"|}")

(** Pretty-print an expression to Rocq (inside parenthesis if the [paren] flag
    is set). *)
let rec to_coq (paren : bool) (e : t) : SmartPrint.t =
  match e with
  | Constant c -> Constant.to_coq paren c
  | Variable (x, implicits) -> (
      let module_reference, implicits =
        List.partition
          (fun (name, _) -> String.equal name module_reference_marker)
          implicits
      in
      let module_label label =
        let ordinary = "_rocq_assumption_" in
        if module_reference <> [] && String.starts_with ~prefix:ordinary label
        then
          "_rocq_module_assumption_"
          ^ String.sub label (String.length ordinary)
              (String.length label - String.length ordinary)
        else label
      in
      let implicits =
        List.map (fun (label, value) -> (module_label label, value)) implicits
      in
      let x =
        match x with
        | MixedPath.AppliedAccess (root, applications, fields) ->
            MixedPath.AppliedAccess
              ( root,
                List.map
                  (fun (label, value) -> (module_label label, value))
                  applications,
                fields )
        | MixedPath.PathName _ | MixedPath.Access _ -> x
      in
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
      | (Apply (e_f, e_xs') | SourceApply (e_f, e_xs', _))
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
          let e_f, trailing_implicits =
            match e_f with
            | Variable
                (MixedPath.AppliedAccess (root, applications, fields), implicits)
              when String.equal
                     (Name.to_string
                        (match List.rev fields with
                        | field :: _ -> field.PathName.base
                        | [] -> root.PathName.base))
                     "Build_FArgs" ->
                let trailing, applications =
                  List.partition
                    (fun (label, _) ->
                      String.starts_with ~prefix:"_rocq_projection_assumption_"
                        label)
                    applications
                in
                let path =
                  match (applications, fields) with
                  | [], [] -> MixedPath.PathName root
                  | [], fields -> MixedPath.Access (root, fields)
                  | applications, fields ->
                      MixedPath.AppliedAccess (root, applications, fields)
                in
                (Variable (path, implicits), List.map to_coq_implicit trailing)
            | _ -> (e_f, [])
          in
          Pp.parens paren
            (nest
               ((match missing_args with
                  | [] -> empty
                  | _ :: _ ->
                      !^"fun" ^^ separate space missing_args ^^ !^"=>" ^^ space)
               ^-^ nest
                     (separate space
                        ((to_coq true e_f :: all_args) @ trailing_implicits)))))
  | SourceApply (e_f, e_xs, _) -> to_coq paren (Apply (e_f, e_xs))
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
  | LetFun (def, e) -> (
      match def.Definition.recursion_strategy with
      | Definition.WellFounded details ->
          to_coq_well_founded_let paren details def e
      | Definition.Partial { definition_name; partial_definitions; recursion }
        ->
          to_coq_partial_let paren definition_name partial_definitions recursion
            def e
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
               ^^ mutual_fixpoint_selector ^^ !^"in" ^^ newline
               ^^ to_coq false e))
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
            | Pattern.Alias (pattern, name) when Pattern.has_or_patterns pattern
              ->
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
                  | Pattern.Alias (pattern, name) when Name.equal name alias ->
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
      | None -> (
          let single_let =
            to_coq_try_single_let_pattern paren None e cases
              is_with_default_case
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
                        ^^ !^"(@RocqOfOCaml.Basics.unreachable _ _)"
                        ^^ newline
                    else empty)
                ^^ !^"end")))
  | MatchWithEquation (e, cases, is_with_default_case) ->
      let scrutinee = !^"_rocq_match_scrutinee" in
      let view = !^"_rocq_match_view" in
      let equation = !^"_rocq_match_eq" in
      Pp.parens paren
      @@ nest
           (!^"let" ^^ scrutinee ^^ !^":=" ^^ to_coq false e ^^ !^"in"
          ^^ newline ^^ !^"match" ^^ scrutinee ^^ !^"as" ^^ view
          ^^ !^"return"
          ^^ parens (scrutinee ^^ !^"=" ^^ view ^^ !^"->" ^^ !^"_")
          ^^ !^"with" ^^ newline
           ^^ separate space
                (cases
                |> List.map (fun (pattern, existential_cast, body) ->
                    nest
                      (!^"|" ^^ Pattern.to_coq false pattern ^^ !^"=>"
                      ^^ !^"fun" ^^ equation ^^ !^"=>"
                      ^^ to_coq_cast_existentials existential_cast body
                      ^^ newline)))
           ^^ (if is_with_default_case then
                 !^"|" ^^ !^"_" ^^ !^"=>" ^^ !^"fun" ^^ equation ^^ !^"=>"
                 ^^ !^"(@RocqOfOCaml.Basics.unreachable _ _)" ^^ newline
               else empty)
          ^^ !^"end" ^^ !^"eq_refl")
  | MatchExtensible (e, result_typ, cases) -> (
      match cases with
      | [ (None, body) ] ->
          Pp.parens paren
          @@ nest
               (!^"let" ^^ !^"'_" ^^ !^":=" ^^ to_coq false e ^^ !^"in"
              ^^ newline ^^ to_coq false body)
      | _ ->
          let rec dispatch = function
            | [] -> to_coq_assumed_value Unreachable result_typ
            | (None, body) :: _ -> to_coq false body
            | (Some (tag, p, typ), body) :: rest ->
                nest
                  (!^"if"
                  ^^ nest (!^"String.eqb" ^^ !^"tag" ^^ !^("\"" ^ tag ^ "\""))
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
                                    (parens
                                       (nest
                                          (!^"let" ^^ !^"'_" ^^ !^":="
                                         ^^ !^"payload" ^^ !^"in" ^^ newline
                                          ^^ to_coq_assumed_value Unreachable
                                               typ))
                                    ^^ !^"in")
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
              ^^ (match pattern with Pattern.Variable _ -> empty | _ -> !^"'")
              ^-^ Pattern.to_coq false pattern
              ^^ !^":=" ^^ value ^^ !^"in")
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
                  bind_pattern_doc (Name.to_coq variant_name) whole
                    (to_coq false body)
            in
            let payload =
              parens
                (nest
                   (!^"let" ^^ !^"'_" ^^ !^":=" ^^ Name.to_coq payload_name
                  ^^ !^"in" ^^ newline
                   ^^ to_coq_assumed_value Unreachable typ))
            in
            let tagged_body =
              match pattern with
              | Pattern.Tuple [] -> body
              | _ when Pattern.is_irrefutable pattern ->
                  bind_pattern_doc payload pattern body
              | _ ->
                  nest
                    (!^"match" ^^ payload ^^ !^"with" ^^ newline ^^ !^"|"
                    ^^ Pattern.to_coq false pattern
                    ^^ !^"=>" ^^ body ^^ newline ^^ !^"|" ^^ !^"_" ^^ !^"=>"
                    ^^ fallback ^^ newline ^^ !^"end")
            in
            nest
              (!^"if" ^^ !^"String.eqb" ^^ Name.to_coq tag_name
              ^^ !^("\"" ^ tag ^ "\"")
              ^^ !^"then")
            ^^ newline ^^ indent tagged_body ^^ newline ^^ !^"else" ^^ newline
            ^^ indent fallback
      in
      Pp.parens paren
      @@ nest
           (!^"let" ^^ Name.to_coq variant_name ^^ !^":=" ^^ to_coq false e
          ^^ !^"in" ^^ newline ^^ !^"match" ^^ Name.to_coq variant_name
          ^^ !^"with" ^^ newline ^^ !^"|" ^^ !^"Variant.Build"
          ^^ Name.to_coq tag_name ^^ !^"_" ^^ Name.to_coq payload_name ^^ !^"=>"
          ^^ newline
           ^^ indent (dispatch cases)
           ^^ newline ^^ !^"end")
  | Record fields -> to_coq_record_fields [] (to_coq false) fields
  | Field (e, x) -> to_coq true e ^-^ !^".(" ^-^ PathName.to_coq x ^-^ !^")"
  | IfThenElse (e1, e2, e3) ->
      Pp.parens paren
      @@ nest
           (group_all (!^"if" ^^ indent (to_coq false e1) ^^ !^"then")
           ^^ newline
           ^^ indent (to_coq false e2)
           ^^ newline ^^ !^"else" ^^ newline
           ^^ indent (to_coq false e3))
  | IfThenElseWithEquation (condition, then_, else_) ->
      let guard = !^"_rocq_guard" in
      let equation = !^"_rocq_guard_eq" in
      Pp.parens paren
      @@ nest
           (!^"match" ^^ to_coq false condition ^^ !^"as" ^^ guard ^^ !^"return"
           ^^ parens
                (to_coq false condition ^^ !^"=" ^^ guard ^^ !^"->" ^^ !^"_")
           ^^ !^"with" ^^ newline ^^ !^"|" ^^ !^"true" ^^ !^"=>" ^^ !^"fun"
           ^^ equation ^^ !^"=>" ^^ to_coq false then_ ^^ newline ^^ !^"|"
           ^^ !^"false" ^^ !^"=>" ^^ !^"fun" ^^ equation ^^ !^"=>"
           ^^ to_coq false else_ ^^ newline ^^ !^"end" ^^ !^"eq_refl")
  | Module (typ, []) ->
      parens
        (nest (!^"ltac:(constructor)" ^^ !^":" ^^ Type.to_coq None None typ))
  | Module (_, fields) -> to_coq_module_fields [] (to_coq false) fields
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
           (!^"let" ^^ !^"'_" ^^ !^":=" ^^ to_coq false e ^^ !^"in" ^^ newline
           ^^ to_coq_assumed_value Unreachable typ)
  | TypAnnotation (e, typ) ->
      parens @@ nest (to_coq true e ^^ !^":" ^^ Type.to_coq None None typ)
  | Assert (typ, e) ->
      Pp.parens paren
      @@
      if Type.is_unit typ then
        nest
          (!^"if" ^^ to_coq false e ^^ !^"then" ^^ !^"tt" ^^ !^"else"
          ^^ to_coq_assumed_value Unreachable typ)
      else
        nest
          (!^"let" ^^ !^"'_" ^^ !^":=" ^^ to_coq false e ^^ !^"in" ^^ newline
          ^^ to_coq_assumed_value Unreachable typ)
  | Assumption (kind, typ, arguments) ->
      Pp.parens paren
      @@ List.fold_right
           (fun argument body ->
             nest
               (!^"let" ^^ !^"'_" ^^ !^":=" ^^ to_coq false argument ^^ !^"in"
              ^^ newline ^^ body))
           arguments
           (to_coq_assumed_value kind typ)
  | RequiresAssumption (_, _, body) | PropagatedAssumption (_, _, body) ->
      to_coq paren body
  | Error message -> !^message
  | ErrorArray es -> OCaml.list (to_coq false) es
  | ErrorTyp typ -> Pp.parens paren @@ Type.to_coq None None typ
  | ErrorMessage (e, error_message) ->
      group (Error.to_comment error_message ^^ newline ^^ to_coq paren e)
  | Ltac tac -> to_coq_ltac tac

(** Render local well-founded recursion with the term-level kernel [Fix]. The
    enclosing [Program] command turns each proof hole passed to [_rocq_recurse]
    into a decrease obligation in its branch context. *)
and to_coq_partial_let (paren : bool) (_definition_name : string)
    (partial_definitions : string list)
    (recursion : Definition.partial_recursion)
    (definition : t option Definition.t) (continuation : t) : SmartPrint.t =
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
        if definition.Definition.is_rec && recursion = Definition.MayDiverge
        then guard_partial_body resumption monad body
        else body
      in
      Pp.parens paren
      @@ nest
           (!^"let"
           ^^ (if definition.Definition.is_rec then
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
           ^^ !^":"
           ^^ Type.to_coq None None header.Header.typ
           ^^ !^":=" ^^ newline
           ^^ indent (to_coq false body)
           ^^ !^"in" ^^ newline ^^ to_coq false continuation)
  | _ -> failwith "local partial recursion must contain one concrete definition"

and to_coq_well_founded_let (paren : bool)
    (details : Definition.well_founded_details)
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
          | [] -> Type.Apply (MixedPath.of_name (Name.of_string_raw "unit"), [])
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
        let destruct_state inner =
          match args with
          | [] -> inner
          | [ (argument, _) ] ->
              !^"let" ^^ Name.to_coq argument ^^ !^":="
              ^^ Name.to_coq state_name ^^ !^"in" ^^ newline ^^ inner
          | _ ->
              (* Rocq's tuple notation is left-associated for both terms and
                 product types.  Destructure with the same tuple notation so
                 local recursive functions with three or more arguments do
                 not accidentally interpret [(a * b) * c] as [a * (b * c)]. *)
              !^"let" ^^ !^"'" ^-^ state_value ^^ !^":="
              ^^ Name.to_coq state_name ^^ !^"in" ^^ newline ^^ inner
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
          rewrite_local_well_founded_calls name recurse_name (List.length args)
            (Option.map
               (fun certificate -> certificate.Definition.tactic)
               details.Definition.certificate)
            body
        in
        let () =
          if Name.Set.mem name (get_free_vars body) then
            failwith
              ("local well-founded recursive function " ^ Name.to_string name
             ^ " must be fully applied at each recursive call")
        in
        let functional =
          parens
            (nest
               (!^"fun" ^^ Name.to_coq state_name ^^ Name.to_coq recurse_name
              ^^ !^"=>" ^^ newline
               ^^ indent (destruct_state (to_coq false body))))
        in
        let body_definition =
          !^"let" ^^ Name.to_coq body_name ^^ !^":"
          ^^ parens
               (nest
                  (!^"forall" ^^ Name.to_coq state_name ^^ !^":"
                  ^^ Type.to_coq None None state_typ
                  ^-^ !^","
                  ^^ parens
                       (nest
                          (!^"forall" ^^ !^"_rocq_next" ^^ !^":"
                          ^^ Type.to_coq None None state_typ
                          ^-^ !^"," ^^ !^"ltof"
                          ^^ Type.to_coq None (Some Type.Context.Apply)
                               state_typ
                          ^^ Name.to_coq measure_name ^^ !^"_rocq_next"
                          ^^ Name.to_coq state_name ^^ !^"->"
                          ^^ Type.to_coq None None typ))
                  ^^ !^"->" ^^ Type.to_coq None None typ))
          ^^ !^":=" ^^ functional ^^ !^"in"
        in
        let motive =
          parens (!^"fun" ^^ !^"_" ^^ !^"=>" ^^ Type.to_coq None None typ)
        in
        let measure_definition =
          !^"let" ^^ Name.to_coq measure_name
          ^^ parens
               (Name.to_coq state_name ^^ !^":"
               ^^ Type.to_coq None None state_typ)
          ^^ !^":" ^^ !^"nat" ^^ !^":="
          ^^ (match details.Definition.certificate with
            | Some certificate -> !^(certificate.Definition.measure)
            | None ->
                !^"RocqOfOCaml.Basics.well_founded_measure"
                ^^ !^("\""
                     ^ String.escaped details.Definition.definition_name
                     ^ "\"")
                ^^ measure_input)
          ^^ !^"in"
        in
        let fix_definition =
          !^"let" ^^ Name.to_coq fix_name ^^ !^":=" ^^ !^"@Fix"
          ^^ Type.to_coq None (Some Type.Context.Apply) state_typ
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
          !^"let" ^^ Name.to_coq name ^^ rendered_arguments ^^ !^":"
          ^^ Type.to_coq None None typ ^^ !^":=" ^^ Name.to_coq fix_name
          ^^ state_value ^^ !^"in"
        in
        Pp.parens paren
        @@ nest
             (measure_definition ^^ newline ^^ body_definition ^^ newline
            ^^ fix_definition ^^ newline ^^ public_definition ^^ newline
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
  | Raw tactic -> !^tactic

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
        nest
          (!^"let" ^^ !^"'_" ^^ !^":=" ^^ to_coq false e ^^ !^"in" ^^ newline
          ^^ to_coq_assumed_value Unreachable return_typ)
    | _ -> to_coq false e
  in
  match existential_cast with
  | None -> e
  | Some
      ({ new_typ_vars; bound_vars; use_axioms; enable; _ } as existential_cast)
    -> (
      let variable_names =
        Pp.primitive_tuple
          (bound_vars |> List.map (fun (name, _) -> Name.to_coq name))
      in
      let assumed_variable_names =
        match List.map (fun (name, _) -> Name.to_coq name) bound_vars with
        | [] -> !^"tt"
        | [ name ] -> name
        | names -> parens (separate (!^"," ^^ space) names)
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
              | [ _ ] -> assumed_variable_names
              | _ -> assumed_variable_names
            in
            nest
              (!^"let" ^^ variable_names_pattern ^^ !^":="
              ^^ parens
                   (nest
                      (!^"let" ^^ !^"'_" ^^ !^":=" ^^ assumed_variable_names
                     ^^ !^"in" ^^ newline
                      ^^ to_coq_assumed_value Unreachable
                           (existential_cast_value_type existential_cast)))
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
            ^^ (if use_axioms then assumed_variable_names else variable_names)
            ^^ !^":="
            ^^ (if use_axioms then
                  to_coq_assumed_value Unreachable
                    (existential_cast_value_type existential_cast)
                else
                  nest
                    (!^"existT"
                    ^^ nest
                         (parens
                            (!^"A" ^^ !^":="
                            ^^ Pp.primitive_tuple_type new_typ_vars_kinds))
                    ^^ parens
                         (nest
                            (!^"fun" ^^ existential_names_pattern ^^ !^"=>"
                           ^^ variable_typ false))
                    ^^ Pp.primitive_tuple_infer (List.length new_typ_vars)
                    ^^ variable_names))
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

let to_coq_record_with_field_implicits ?(local_fargs = false)
    ?(compact_aliases = Name.Map.empty)
    (field_implicits : (Name.t * SmartPrint.t) list) (e : t) : SmartPrint.t =
  let e = remove_selected_fargs e in
  match e with
  | Record fields ->
      to_coq_record_fields ~local_fargs ~compact_aliases field_implicits
        (to_coq false) fields
  | Module (typ, []) ->
      parens
        (nest (!^"ltac:(constructor)" ^^ !^":" ^^ Type.to_coq None None typ))
  | Module (_, fields) ->
      to_coq_module_fields ~local_fargs ~compact_aliases field_implicits
        (to_coq false) fields
  | _ -> to_coq false e

let to_coq_module_result ~(local_fargs : bool)
    ~(compact_aliases : int Name.Map.t) (e : t) : SmartPrint.t =
  to_coq_record_with_field_implicits ~local_fargs ~compact_aliases [] e

let to_coq_record_constructor (constructor : SmartPrint.t)
    (parameters : SmartPrint.t list) (e : t) : SmartPrint.t =
  let e = remove_selected_fargs e in
  match e with
  | Record fields | Module (_, fields) ->
      let rec unwrap_assumptions expression =
        match expression with
        | RequiresAssumption (_, _, body) | PropagatedAssumption (_, _, body) ->
            unwrap_assumptions body
        | _ -> expression
      in
      let render_field (_, arity, expression) =
        let expression = to_coq false (unwrap_assumptions expression) in
        if arity = 0 then expression
        else
          parens
            (nest
               (!^"fun"
               ^^ separate space (Pp.n_underscores arity)
               ^^ !^"=>" ^^ expression))
      in
      parens
        (nest
           (separate space
              ((constructor :: parameters) @ List.map render_field fields)))
  | _ -> to_coq_record_with_field_implicits [] e
