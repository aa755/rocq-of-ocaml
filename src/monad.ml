(** A monad to:
    * have a code without side-effects;
    * handle errors;
    * report as much errors as possible (many branches of the AST can be explored
      in parallel and errors of each branch are reported);
    * handle the current position in the source [Loc.t];
    * handle the current environment [Env.t]. *)

type import = Require of string * string | RequireImport of string

module Command = struct
  type 'a t =
    | GetConfiguration : Configuration.t t
    | GetDocumentation : string option t
    | GetEnv : Env.t t
    | GetEnvStack : Env.t list t
    | GetIncludedPathAlias : Ident.t -> Path.t option t
    | GetIncludedSignaturePathAlias : Ident.t -> Path.t option t
    | GetIncludedRecordAlias :
        Ident.t -> IncludedRecordAliasTarget.t option t
    | GetConstructorName : Types.Uid.t -> string option t
    | GetValueName : Ident.t -> string option t
    | GetModulePathAlias : Path.t -> Path.t option t
    | GetSignatureHint : Path.t -> Path.t option t
    | GetModuleTypeHint : Path.t -> Types.module_type option t
    | GetModuleTypeHints : (Path.t * Types.module_type) list t
    | GetAnonymousSignatureHints : (Path.t * Types.module_type) list t
    | GetAnonymousFunctorParameter :
        Path.t * string -> Path.t option t
    | GetFunctorParameterTypes :
        Path.t -> FunctorParameterHint.t list option t
    | GetFunctorResultSignature : Path.t -> Path.t option t
    | GetResultModuleField :
        Path.t * string -> Path.t option t
    | GetResultNamespaceInclude :
        Path.t * string -> string option t
    | GetAppliedFunctorChild :
        Path.t -> (Path.t * Path.t) option t
    | Raise : 'a * Error.Category.t * string -> 'a t
    | Use : import -> unit t
    | UseUnsafeFixpoint : unit t
end

module Wrapper = struct
  type t =
    | EnvSet of Env.t
    | EnvStackPush
    | LocSet of Location.t
    | ModulePathAliasSet of Path.t * Path.t
    | SignatureHintSet of Path.t * Path.t
end

type 'a t =
  | Bind : 'b t * ('b -> 'a t) -> 'a t
  | Command of 'a Command.t
  | RetrieveUnsafeFixpoints : 'a t -> (bool * 'a) t
  | Return of 'a
  | Wrapper of Wrapper.t * 'a t

module Notations = struct
  let return (x : 'a) : 'a t = Return x
  let ( let* ) (x : 'a t) (f : 'a -> 'b t) : 'b t = Bind (x, f)
  let ( >>= ) (x : 'a t) (f : 'a -> 'b t) : 'b t = Bind (x, f)
  let ( >> ) (x : 'a t) (y : 'b t) : 'b t = Bind (x, fun () -> y)
  let get_configuration : Configuration.t t = Command Command.GetConfiguration
  let get_documentation : string option t = Command Command.GetDocumentation
  let get_env : Env.t t = Command Command.GetEnv
  let get_env_stack : Env.t list t = Command Command.GetEnvStack
  let get_included_path_alias (ident : Ident.t) : Path.t option t =
    Command (Command.GetIncludedPathAlias ident)

  let get_included_signature_path_alias (ident : Ident.t) :
      Path.t option t =
    Command (Command.GetIncludedSignaturePathAlias ident)

  let get_included_record_alias (ident : Ident.t) :
      IncludedRecordAliasTarget.t option t =
    Command (Command.GetIncludedRecordAlias ident)

  let get_constructor_name (uid : Types.Uid.t) : string option t =
    Command (Command.GetConstructorName uid)

  let get_value_name (ident : Ident.t) : string option t =
    Command (Command.GetValueName ident)

  let get_module_path_alias (path : Path.t) : Path.t option t =
    Command (Command.GetModulePathAlias path)

  let get_signature_hint (path : Path.t) : Path.t option t =
    Command (Command.GetSignatureHint path)

  let get_module_type_hint (path : Path.t) : Types.module_type option t =
    Command (Command.GetModuleTypeHint path)

  let get_module_type_hints : (Path.t * Types.module_type) list t =
    Command Command.GetModuleTypeHints

  let get_anonymous_signature_hints : (Path.t * Types.module_type) list t =
    Command Command.GetAnonymousSignatureHints

  let get_anonymous_functor_parameter (functor_path : Path.t)
      (parameter_name : string) : Path.t option t =
    Command
      (Command.GetAnonymousFunctorParameter (functor_path, parameter_name))

  let get_functor_parameter_types (functor_path : Path.t) :
      FunctorParameterHint.t list option t =
    Command (Command.GetFunctorParameterTypes functor_path)

  let get_functor_result_signature (functor_path : Path.t) :
      Path.t option t =
    Command (Command.GetFunctorResultSignature functor_path)

  let get_result_module_field (result_signature : Path.t)
      (field_name : string) : Path.t option t =
    Command (Command.GetResultModuleField (result_signature, field_name))

  let get_result_namespace_include (result_signature : Path.t)
      (namespace : string) : string option t =
    Command
      (Command.GetResultNamespaceInclude
         (result_signature, namespace))

  let get_applied_functor_child (path : Path.t) :
      (Path.t * Path.t) option t =
    Command (Command.GetAppliedFunctorChild path)

  let set_env (env : Env.t) (x : 'a t) : 'a t = Wrapper (Wrapper.EnvSet env, x)

  let set_loc (loc : Location.t) (x : 'a t) : 'a t =
    Wrapper (Wrapper.LocSet loc, x)

  let push_env (x : 'a t) : 'a t = Wrapper (Wrapper.EnvStackPush, x)

  let set_module_path_alias (source : Path.t) (target : Path.t)
      (x : 'a t) : 'a t =
    Wrapper (Wrapper.ModulePathAliasSet (source, target), x)

  let set_signature_hint (module_path : Path.t) (signature_path : Path.t)
      (x : 'a t) : 'a t =
    Wrapper (Wrapper.SignatureHintSet (module_path, signature_path), x)

  let raise (value : 'a) (category : Error.Category.t) (message : string) : 'a t
      =
    Command (Command.Raise (value, category, message))

  let use (import : import) : unit t = Command (Command.Use import)
  let use_unsafe_fixpoint : unit t = Command Command.UseUnsafeFixpoint

  let retrieve_unsafe_fixpoints (x : 'a t) : (bool * 'a) t =
    RetrieveUnsafeFixpoints x
end

module List = struct
  open Notations

  let rec concat_map (f : 'a -> 'b list t) (l : 'a list) : 'b list t =
    match l with
    | [] -> return []
    | x :: l ->
        f x >>= fun x ->
        concat_map f l >>= fun l -> return (x @ l)

  let rec filter (f : 'a -> bool t) (l : 'a list) : 'a list t =
    match l with
    | [] -> return []
    | x :: l ->
        f x >>= fun is_valid ->
        filter f l >>= fun l -> if is_valid then return (x :: l) else return l

  let rec filter_map (f : 'a -> 'b option t) (l : 'a list) : 'b list t =
    match l with
    | [] -> return []
    | x :: l -> (
        f x >>= fun x ->
        filter_map f l >>= fun l ->
        match x with None -> return l | Some x -> return (x :: l))

  let rec fold_left (f : 'a -> 'b -> 'a t) (accumulator : 'a) (l : 'b list) :
      'a t =
    match l with
    | [] -> return accumulator
    | x :: l -> f accumulator x >>= fun accumulator -> fold_left f accumulator l

  let rec fold_right (f : 'b -> 'a -> 'a t) (l : 'b list) (accumulator : 'a) :
      'a t =
    match l with
    | [] -> return accumulator
    | x :: l ->
        fold_right f l accumulator >>= fun accumulator -> f x accumulator

  let rec iter (f : 'a -> unit t) (l : 'a list) : unit t =
    match l with [] -> return () | x :: l -> f x >> iter f l

  let rec map (f : 'a -> 'b t) (l : 'a list) : 'b list t =
    match l with
    | [] -> return []
    | x :: l ->
        f x >>= fun x ->
        map f l >>= fun l -> return (x :: l)

  let rec lesser_and_greater (compare : 'a -> 'a -> int t) (x : 'a)
      (l : 'a list) : ('a list * 'a list) t =
    match l with
    | [] -> return ([], [])
    | y :: l ->
        compare y x >>= fun comparison ->
        lesser_and_greater compare x l >>= fun (lesser, greater) ->
        if comparison < 0 then return (y :: lesser, greater)
        else if comparison > 0 then return (lesser, y :: greater)
        else return (lesser, greater)

  let rec sort_uniq (compare : 'a -> 'a -> int t) (l : 'a list) : 'a list t =
    match l with
    | [] -> return []
    | head :: tail ->
        lesser_and_greater compare head tail >>= fun (lesser, greater) ->
        sort_uniq compare lesser >>= fun lesser ->
        sort_uniq compare greater >>= fun greater ->
        return (lesser @ [ head ] @ greater)
end
