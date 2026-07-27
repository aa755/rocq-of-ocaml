type comments = (string * Location.t) list

module Import = struct
  type t = { import : Monad.import; mli : bool }

  let merge (imports1 : t list) (imports2 : t list) : t list =
    List.sort_uniq
      (fun import1 import2 ->
        match (import1.import, import2.import) with
        | RequireImport _, Require _ -> -1
        | Require _, RequireImport _ -> 1
        | RequireImport _, RequireImport _ | Require _, Require _ ->
            compare import1 import2)
      (imports1 @ imports2)
end

module Result = struct
  type 'a t = {
    errors : Error.t list;
    imports : Import.t list;
    use_unsafe_fixpoints : bool;
    value : 'a;
    warnings : Error.t list;
  }

  let success (value : 'a) : 'a t =
    {
      errors = [];
      imports = [];
      use_unsafe_fixpoints = false;
      value;
      warnings = [];
    }
end

module EnvStack = struct
  type t = Env.t list

  let init : t = []
end

module Context = struct
  type t = {
    comments : comments;
    configuration : Configuration.t;
    constructor_names : ConstructorNames.t;
    definition_path : string list;
    term_environment : string list;
    env : Env.t;
    env_stack : EnvStack.t;
    included_path_aliases : IncludedPathAliases.t;
    included_record_aliases : IncludedRecordAliases.t;
    loc : Location.t;
    module_path_aliases : ModulePathAliases.t;
    module_path_alias_overrides : (Path.t * Path.t) list;
    signature_hints : SignatureHints.t;
    project_hints : ProjectHints.t;
    value_names : ValueNames.t;
  }

  let init (comments : comments) (configuration : Configuration.t)
      (constructor_names : ConstructorNames.t)
      (initial_env : Env.t) (initial_loc : Location.t)
      (included_path_aliases : IncludedPathAliases.t)
      (included_record_aliases : IncludedRecordAliases.t)
      (module_path_aliases : ModulePathAliases.t)
      (signature_hints : SignatureHints.t)
      (project_hints : ProjectHints.t)
      (value_names : ValueNames.t) : t =
    {
      comments;
      configuration;
      constructor_names;
      definition_path = [];
      term_environment = [];
      env = initial_env;
      env_stack = [];
      included_path_aliases;
      included_record_aliases;
      loc = initial_loc;
      module_path_aliases;
      module_path_alias_overrides = [];
      signature_hints;
      project_hints;
      value_names;
    }
end

module Interpret = struct
  type 'a t = Context.t -> 'a Result.t
end

module Command = struct
  open Monad.Command

  let rec normalize_project_path (env : Env.t) (path : Path.t) : Path.t =
    match Env.normalize_module_path None env path with
    | normalized when not (Path.same normalized path) -> normalized
    | _ -> (
        match path with
        | Path.Pident _ -> path
        | Path.Pdot (prefix, field) ->
            Path.Pdot (normalize_project_path env prefix, field)
        | Path.Papply (functor_path, argument_path) ->
            Path.Papply
              ( normalize_project_path env functor_path,
                normalize_project_path env argument_path )
        | Path.Pextra_ty (prefix, extra) ->
            Path.Pextra_ty
              (normalize_project_path env prefix, extra))
    | exception _ -> (
        match path with
        | Path.Pident _ -> path
        | Path.Pdot (prefix, field) ->
            Path.Pdot (normalize_project_path env prefix, field)
        | Path.Papply (functor_path, argument_path) ->
            Path.Papply
              ( normalize_project_path env functor_path,
                normalize_project_path env argument_path )
        | Path.Pextra_ty (prefix, extra) ->
            Path.Pextra_ty
              (normalize_project_path env prefix, extra))

  let eval (type a) (command : a t) : a Interpret.t =
   fun context ->
    match command with
    | GetConfiguration -> Result.success context.configuration
    | GetDocumentation ->
        let documentation, _ =
          let open Merlin_analysis in
          Ocamldoc.associate_comment
            ~after_only:false
            context.comments
            context.loc
            context.loc
        in
        Result.success documentation
    | GetDefinitionPath -> Result.success context.definition_path
    | GetTermEnvironment -> Result.success context.term_environment
    | GetEnv -> Result.success context.env
    | GetEnvStack -> Result.success context.env_stack
    | GetIncludedPathAlias ident ->
        Result.success
          (IncludedPathAliases.find ident context.loc
             context.included_path_aliases)
    | GetIncludedSignaturePathAlias ident ->
        Result.success
          (IncludedPathAliases.find_for_signature ident context.loc
             context.included_path_aliases)
    | GetIncludedRecordAlias ident ->
        Result.success
          (IncludedRecordAliases.find ident context.loc
             context.included_record_aliases)
    | GetConstructorName uid ->
        Result.success (ConstructorNames.find uid context.constructor_names)
    | GetValueName ident ->
        Result.success (ValueNames.find ident context.value_names)
    | GetModulePathAlias path ->
        let normalized_path = normalize_project_path context.env path in
        let alias =
          match
            context.module_path_alias_overrides
            |> List.find_map (fun (source, target) ->
                   if
                     Path.same path source
                     || Path.same normalized_path
                          (normalize_project_path context.env source)
                   then Some target
                   else None)
          with
          | Some _ as target -> target
          | None -> (
              match
                ModulePathAliases.find path context.loc
                  context.module_path_aliases
              with
              | Some _ as target -> target
              | None ->
                  ModulePathAliases.find normalized_path context.loc
                    context.module_path_aliases)
        in
        Result.success
          (match alias with
          | Some target when Path.same path target -> None
          | Some _ | None -> alias)
    | GetSignatureHint path ->
        let normalized_path =
          normalize_project_path context.env path
        in
        Result.success
          (match SignatureHints.find path context.signature_hints with
          | Some _ as result -> result
          | None -> (
              match
                SignatureHints.find normalized_path
                  context.signature_hints
              with
              | Some _ as result -> result
              | None ->
                  ProjectHints.find_module_result normalized_path
                    context.project_hints))
    | GetModuleTypeHint path ->
        Result.success
          (match
             SignatureHints.find_module_type path context.loc
               context.signature_hints
           with
          | Some _ as result -> result
          | None ->
              ProjectHints.find_module_type
                (normalize_project_path context.env path)
                context.project_hints)
    | GetModuleTypeHints ->
        Result.success
          (SignatureHints.module_types context.signature_hints
          @ ProjectHints.module_types context.project_hints)
    | GetAnonymousSignatureHints ->
        Result.success
          (SignatureHints.anonymous_signatures context.loc
             context.signature_hints)
    | GetAnonymousFunctorParameter (functor_path, parameter_name) ->
        Result.success
          (match
             SignatureHints.find_anonymous_functor_parameter functor_path
               parameter_name context.signature_hints
           with
          | Some _ as result -> result
          | None ->
              ProjectHints.find_anonymous_functor_parameter
                (normalize_project_path context.env functor_path)
                parameter_name context.project_hints)
    | GetFunctorParameterTypes functor_path ->
        Result.success
          (match
             SignatureHints.find_functor_parameter_types functor_path
               context.signature_hints
           with
          | Some _ as result -> result
          | None ->
              ProjectHints.find_functor_parameter_types
                (normalize_project_path context.env functor_path)
                context.project_hints)
    | GetFunctorResultSignature functor_path ->
        Result.success
          (match
             SignatureHints.find_functor_result_signature functor_path
               context.signature_hints
           with
          | Some _ as result -> result
          | None ->
              ProjectHints.find_functor_result
                (normalize_project_path context.env functor_path)
                context.project_hints)
    | GetResultModuleField (result_signature, field_name) ->
        Result.success
          (match
             SignatureHints.find_result_module_field result_signature
               field_name context.signature_hints
           with
          | Some _ as result -> result
          | None ->
              ProjectHints.find_result_module_field
                (normalize_project_path context.env result_signature)
                field_name context.project_hints)
    | GetResultNamespaceInclude (result_signature, namespace) ->
        Result.success
          (SignatureHints.find_result_namespace_include
             result_signature namespace context.signature_hints)
    | GetAppliedFunctorChild path ->
        Result.success
          (SignatureHints.find_applied_functor_child path
             context.signature_hints)
    | Raise (value, category, message) ->
        let result = Result.success value in
        let errors =
          let error_id = Error.Category.to_id category in
          let is_valid_error =
            (not
               (Configuration.is_category_in_error_blacklist
                  context.configuration error_id))
            && not
                 (Configuration.is_message_in_error_blacklist
                    context.configuration message)
          in
          if is_valid_error then
            [ { Error.category; loc = Loc.of_location context.loc; message } ]
          else []
        in
        { result with errors }
    | Warn message ->
        let result = Result.success () in
        {
          result with
          warnings =
            [
              {
                Error.category = Error.Category.Unexpected;
                loc = Loc.of_location context.loc;
                message;
              };
            ];
        }
    | Use import ->
        let result = Result.success () in
        let mli =
          match import with
          | Require (_, name) ->
              Configuration.is_require_mli context.configuration name
          | RequireImport _ -> false
        in
        { result with imports = [ { import; mli } ] }
    | UseUnsafeFixpoint ->
        let result = Result.success () in
        { result with use_unsafe_fixpoints = true }
end

module Wrapper = struct
  let eval (wrapper : Monad.Wrapper.t) (interpret : 'a Interpret.t) :
      'a Interpret.t =
   fun context ->
    match wrapper with
    | EnvSet env -> interpret { context with env }
    | DefinitionPathPush name ->
        interpret
          {
            context with
            definition_path = context.definition_path @ [ name ];
          }
    | TermEnvironmentPush names ->
        interpret
          {
            context with
            term_environment = names @ context.term_environment;
          }
    | EnvStackPush ->
        interpret { context with env_stack = context.env :: context.env_stack }
    | LocSet loc ->
      interpret { context with loc }
    | ModulePathAliasSet (source, target) ->
        interpret
          {
            context with
            module_path_alias_overrides =
              (source, target) :: context.module_path_alias_overrides;
          }
    | SignatureHintSet (module_path, signature_path) ->
        interpret
          {
            context with
            signature_hints =
              SignatureHints.add module_path signature_path
                context.signature_hints;
          }
end

let profile_translation =
  Option.is_some (Sys.getenv_opt "ROCQ_OF_OCAML_PROFILE")

let eval_steps = ref 0

let rec eval : type a. a Monad.t -> a Interpret.t =
 fun x context ->
  if profile_translation then (
    incr eval_steps;
    if !eval_steps mod 100_000 = 0 then
      let loc = context.Context.loc.Location.loc_start in
      let gc = Gc.quick_stat () in
      Printf.eprintf
        "rocq-of-ocaml: %d monad steps at %s:%d (heap %.1f MiB)\n%!"
        !eval_steps loc.Lexing.pos_fname loc.Lexing.pos_lnum
        (float_of_int gc.Gc.heap_words *. float_of_int (Sys.word_size / 8)
        /. 1_048_576.));
  match x with
  | Monad.Bind (x, f) ->
      let {
        Result.errors = errors_x;
        imports = imports_x;
        use_unsafe_fixpoints = use_unsafe_fixpoints_x;
        value = value_x;
        warnings = warnings_x;
      } =
        eval x context
      in
      let {
        Result.errors = errors_y;
        imports = imports_y;
        use_unsafe_fixpoints = use_unsafe_fixpoints_y;
        value = value_y;
        warnings = warnings_y;
      } =
        eval (f value_x) context
      in
      {
        errors = errors_x @ errors_y;
        imports = imports_x @ imports_y;
        use_unsafe_fixpoints = use_unsafe_fixpoints_x || use_unsafe_fixpoints_y;
        value = value_y;
        warnings = warnings_x @ warnings_y;
      }
  | Command command -> Command.eval command context
  | RetrieveUnsafeFixpoints x ->
      let result = eval x context in
      {
        result with
        use_unsafe_fixpoints = false;
        value = (result.use_unsafe_fixpoints, result.value);
      }
  | Return value -> Result.success value
  | Wrapper (wrapper, x) -> Wrapper.eval wrapper (eval x) context
