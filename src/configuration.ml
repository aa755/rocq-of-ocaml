module ConstructorMapping = struct
  type t = { source : string; target : string; typ : string }
end

module Import = struct
  type t = { source : string; target : string }
end

module MergeRule = struct
  type t = { source1 : string; source2 : string; target : string }
end

module MonadicOperators = struct
  type t = { bind : string; name : string; return : string }
end

module Operator = struct
  type t = { name : string; notation : string }
end

module RenamingRule = struct
  type t = { source : string; target : string }

  let remove_suffix (suffix : string) (value : string) : string option =
    let suffix_length = String.length suffix in
    let value_length = String.length value in
    if
      value_length >= suffix_length
      && String.sub value (value_length - suffix_length) suffix_length = suffix
    then Some (String.sub value 0 (value_length - suffix_length))
    else None

  let rewrite ({ source; target } : t) (path : string) : string option =
    match remove_suffix ".*" source with
    | Some source_prefix ->
        let qualified_prefix = source_prefix ^ "." in
        let prefix_length = String.length qualified_prefix in
        if
          String.length path > prefix_length
          && String.sub path 0 prefix_length = qualified_prefix
        then
          Some
            (target ^ "."
            ^ String.sub path prefix_length (String.length path - prefix_length))
        else None
    | None -> if source = path then Some target else None

  let find (rules : t list) (source : string) : string option =
    rules
    |> (* We reverse the list so that the last entry is taken into account. *)
    List.rev
    |> List.find_map (fun rule -> rewrite rule source)
end

module RecursionStrategy = struct
  type kind = WellFounded | Partial | Convergent

  type t = {
    source : string;
    definition : string;
    kind : kind;
    arity : int option;
  }
end

module VariantMapping = struct
  type t = { source : string; target : string }
end

type t = {
  alias_barrier_modules : string list;
  constant_warning : bool;
  constructor_map : ConstructorMapping.t list;
  error_category_blacklist : string list;
  error_filename_blacklist : string list;
  error_message_blacklist : string list;
  escape_value : string list;
  file_name : string;
  first_class_module_path_blacklist : string list;
  first_class_module_signature_blacklist : string list;
  head_suffix : string;
  merge_returns : MergeRule.t list;
  merge_types : MergeRule.t list;
  monadic_lets : Operator.t list;
  monadic_let_returns : MonadicOperators.t list;
  monadic_returns : Operator.t list;
  monadic_return_lets : MonadicOperators.t list;
  operator_infix : Operator.t list;
  recursion_strategies : RecursionStrategy.t list;
  renaming_rules : RenamingRule.t list;
  renaming_type_constructor : RenamingRule.t list;
  require : Import.t list;
  require_import : Import.t list;
  require_long_ident : Import.t list;
  require_mli : string list;
  variant_constructors : VariantMapping.t list;
  variant_types : VariantMapping.t list;
  without_default_imports : bool;
  without_guard_checking : string list;
  without_positivity_checking : string list;
}

let default (file_name : string) : t =
  {
    alias_barrier_modules = [];
    constant_warning = true;
    constructor_map = [];
    error_category_blacklist = [];
    error_filename_blacklist = [];
    error_message_blacklist = [];
    escape_value = [];
    file_name;
    first_class_module_path_blacklist = [];
    first_class_module_signature_blacklist = [];
    head_suffix = "";
    merge_returns = [];
    merge_types = [];
    monadic_lets = [];
    monadic_let_returns = [];
    monadic_returns = [];
    monadic_return_lets = [];
    operator_infix = [];
    recursion_strategies = [];
    renaming_rules =
      ConfigurationRenaming.rules
      |> List.map (fun (source, target) -> { RenamingRule.source; target });
    renaming_type_constructor = [];
    require = [];
    require_import = [];
    require_long_ident = [];
    require_mli = [];
    variant_constructors = [];
    variant_types = [];
    without_default_imports = false;
    without_guard_checking = [];
    without_positivity_checking = [];
  }

let is_alias_in_barrier_module (configuration : t) (name : string) : bool =
  List.mem name configuration.alias_barrier_modules

let is_constructor_renamed (configuration : t) (typ : string) (name : string) :
    string option =
  configuration.constructor_map
  |> List.find_opt (fun { ConstructorMapping.source; typ = typ'; _ } ->
         source = name && typ' = typ)
  |> Option.map (fun { ConstructorMapping.target; _ } -> target)

let have_constant_warning (configuration : t) : bool =
  configuration.constant_warning

let is_category_in_error_blacklist (configuration : t) (error_id : string) :
    bool =
  List.mem error_id configuration.error_category_blacklist

let filename_matches (actual : string) (configured : string) : bool =
  actual = configured
  ||
  let actual_length = String.length actual in
  let configured_length = String.length configured in
  configured_length < actual_length
  && String.ends_with ~suffix:configured actual
  && actual.[actual_length - configured_length - 1] = '/'

let filename_is_listed (actual : string) (configured : string list) : bool =
  List.exists (filename_matches actual) configured

let is_filename_in_error_blacklist (configuration : t) : bool =
  filename_is_listed configuration.file_name
    configuration.error_filename_blacklist

let is_message_in_error_blacklist (configuration : t) (message : string) : bool
    =
  configuration.error_message_blacklist
  |> List.exists (fun content ->
         (* That is the simplest way I found to test string inclusion from the
            standard library. *)
         Str.replace_first (Str.regexp_string content) "" message <> message)

let is_value_to_escape (configuration : t) (name : string) : bool =
  List.mem name configuration.escape_value

let get_recursion_strategy (configuration : t) (definition_path : string list) :
    RecursionStrategy.kind option =
  let definition = String.concat "." definition_path in
  configuration.recursion_strategies
  |> List.find_opt (fun { RecursionStrategy.source; definition = configured; _ } ->
         configured = definition
         && filename_matches configuration.file_name source)
  |> Option.map (fun { RecursionStrategy.kind; _ } -> kind)

let partial_definition_names (configuration : t) : string list =
  configuration.recursion_strategies
  |> List.filter_map
       (fun { RecursionStrategy.definition; kind; _ } ->
         if kind = RecursionStrategy.Partial then Some definition else None)

let recursion_definition_suffix_matches (configured : string)
    (definition_path : string list) : bool =
  let requested = String.concat "." definition_path in
  let last_two path =
    match List.rev (String.split_on_char '.' path) with
    | value :: module_ :: _ -> Some (module_, value)
    | _ -> None
  in
  configured = requested
  || String.ends_with ~suffix:("." ^ requested) configured
  || String.ends_with ~suffix:("." ^ configured) requested
  ||
  match (last_two configured, last_two requested) with
  | Some configured, Some requested -> configured = requested
  | _ -> false

let has_recursion_strategy_suffix (configuration : t)
    (definition_path : string list) (kind : RecursionStrategy.kind) : bool =
  configuration.recursion_strategies
  |> List.exists
       (fun
         {
           RecursionStrategy.definition;
           kind = configured_kind;
           _;
         } ->
         configured_kind = kind
         && recursion_definition_suffix_matches definition definition_path)

let recursion_strategy_arity_suffix (configuration : t)
    (definition_path : string list) (kind : RecursionStrategy.kind) :
    int option =
  configuration.recursion_strategies
  |> List.find_map
       (fun
         {
           RecursionStrategy.definition;
           kind = configured_kind;
           arity;
           _;
         } ->
         if
           configured_kind = kind
           && recursion_definition_suffix_matches definition definition_path
         then arity
         else None)

let is_in_first_class_module_path_backlist (configuration : t) (path : Path.t) :
    bool =
  let path_components = Path.name path |> Str.split (Str.regexp "__\\|\\.") in
  match List.rev path_components with
  | [] -> false
  | _ :: path ->
      let path = String.concat "." (List.rev path) in
      List.mem path configuration.first_class_module_path_blacklist

let is_in_first_class_module_signature_backlist (configuration : t)
    (path : Path.t) : bool =
  List.mem (Path.name path) configuration.first_class_module_signature_blacklist

let is_in_merge_returns (configuration : t) (source1 : string)
    (source2 : string) : string option =
  configuration.merge_returns
  |> List.find_map (fun (merge_rule : MergeRule.t) ->
         if source1 = merge_rule.source1 && source2 = merge_rule.source2 then
           Some merge_rule.target
         else None)

let is_in_merge_types (configuration : t) (source1 : string) (source2 : string)
    : string option =
  configuration.merge_types
  |> List.find_map (fun (merge_rule : MergeRule.t) ->
         if source1 = merge_rule.source1 && source2 = merge_rule.source2 then
           Some merge_rule.target
         else None)

let is_monadic_let (configuration : t) (name : string) : string option =
  let monadic_operator =
    List.find_opt
      (fun { Operator.name = name'; _ } -> name' = name)
      configuration.monadic_lets
  in
  match monadic_operator with
  | None -> None
  | Some { Operator.notation; _ } -> Some notation

let is_monadic_let_return (configuration : t) (name : string) :
    (string * string) option =
  let monadic_operator =
    List.find_opt
      (fun { MonadicOperators.name = name'; _ } -> name' = name)
      configuration.monadic_let_returns
  in
  match monadic_operator with
  | None -> None
  | Some { MonadicOperators.bind; return; _ } -> Some (bind, return)

let is_monadic_return (configuration : t) (name : string) : string option =
  let monadic_operator =
    List.find_opt
      (fun { Operator.name = name'; _ } -> name' = name)
      configuration.monadic_returns
  in
  match monadic_operator with
  | None -> None
  | Some { Operator.notation; _ } -> Some notation

let is_monadic_return_let (configuration : t) (name : string) :
    (string * string) option =
  let monadic_operator =
    List.find_opt
      (fun { MonadicOperators.name = name'; _ } -> name' = name)
      configuration.monadic_return_lets
  in
  match monadic_operator with
  | None -> None
  | Some { MonadicOperators.bind; return; _ } -> Some (bind, return)

let is_operator_infix (configuration : t) (name : string) : string option =
  let operator_infix =
    List.find_opt
      (fun { Operator.name = name'; _ } -> name' = name)
      configuration.operator_infix
  in
  match operator_infix with
  | None -> None
  | Some { Operator.notation; _ } -> Some notation

let is_in_renaming_rule (configuration : t) (path : string) : string option =
  RenamingRule.find configuration.renaming_rules path

let is_in_renaming_type_constructor (configuration : t) (source : string) :
    string option =
  RenamingRule.find configuration.renaming_type_constructor source

let should_require (configuration : t) (base : string) : string option =
  configuration.require
  |> List.find_opt (fun { Import.source; _ } -> source = base)
  |> Option.map (fun { Import.target; _ } -> target)

let should_require_import (configuration : t) (base : string) : string option =
  configuration.require_import
  |> List.find_opt (fun { Import.source; _ } -> source = base)
  |> Option.map (fun { Import.target; _ } -> target)

let should_require_long_ident (configuration : t) (base : string) :
    string option =
  configuration.require_long_ident
  |> List.find_opt (fun { Import.source; _ } -> source = base)
  |> Option.map (fun { Import.target; _ } -> target)

let is_require_mli (configuration : t) (name : string) : bool =
  List.mem name configuration.require_mli

let get_variant_constructor (configuration : t) (name : string) : string option
    =
  configuration.variant_constructors
  |> List.find_opt (fun { VariantMapping.source; _ } -> source = name)
  |> Option.map (fun { VariantMapping.target; _ } -> target)

let get_variant_typ (configuration : t) (name : string) : string option =
  configuration.variant_types
  |> List.find_opt (fun { VariantMapping.source; _ } -> source = name)
  |> Option.map (fun { VariantMapping.target; _ } -> target)

let is_without_guard_checking (configuration : t) : bool =
  filename_is_listed configuration.file_name configuration.without_guard_checking

let is_without_default_imports (configuration : t) : bool =
  configuration.without_default_imports

let is_without_positivity_checking (configuration : t) : bool =
  filename_is_listed configuration.file_name
    configuration.without_positivity_checking

let get_bool (id : string) (json : Yojson.Basic.t) : bool =
  let error_message = "Expected a boolean in " ^ id in
  match json with `Bool value -> value | _ -> failwith error_message

let get_string (id : string) (json : Yojson.Basic.t) : string =
  let error_message = "Expected a string in " ^ id in
  match json with `String value -> value | _ -> failwith error_message

let get_string_list (id : string) (json : Yojson.Basic.t) : string list =
  let error_message = "Expected a string list in " ^ id in
  match json with
  | `List jsons ->
      jsons
      |> List.map (function
           | `String value -> value
           | _ -> failwith error_message)
  | _ -> failwith error_message

let get_string_couple_list (id : string) (json : Yojson.Basic.t) :
    (string * string) list =
  let error_message = "Expected a list of couples of strings in " ^ id in
  match json with
  | `List jsons ->
      jsons
      |> List.map (function
           | `List [ `String value1; `String value2 ] -> (value1, value2)
           | _ -> failwith error_message)
  | _ -> failwith error_message

let get_string_triple_list (id : string) (json : Yojson.Basic.t) :
    (string * string * string) list =
  let error_message = "Expected a list of triples of strings in " ^ id in
  match json with
  | `List jsons ->
      jsons
      |> List.map (function
           | `List [ `String value1; `String value2; `String value3 ] ->
               (value1, value2, value3)
           | _ -> failwith error_message)
  | _ -> failwith error_message

let of_json (file_name : string) (json : Yojson.Basic.t) : t =
  match json with
  | `Assoc entries ->
      List.fold_left
        (fun configuration (id, entry) ->
          match id with
          | "alias_barrier_modules" ->
              let entry = get_string_list "alias_barrier_modules" entry in
              { configuration with alias_barrier_modules = entry }
          | "constructor_map" ->
              let entry =
                entry
                |> get_string_triple_list "constructor_map"
                |> List.map (fun (typ, source, target) ->
                       { ConstructorMapping.source; target; typ })
              in
              { configuration with constructor_map = entry }
          | "constant_warning" ->
              let entry = get_bool "constant_warning" entry in
              { configuration with constant_warning = entry }
          | "error_category_blacklist" ->
              let entry = get_string_list "error_category_blacklist" entry in
              { configuration with error_category_blacklist = entry }
          | "error_filename_blacklist" ->
              let entry = get_string_list "error_filename_blacklist" entry in
              { configuration with error_filename_blacklist = entry }
          | "error_message_blacklist" ->
              let entry = get_string_list "error_message_blacklist" entry in
              { configuration with error_message_blacklist = entry }
          | "escape_value" ->
              let entry = get_string_list "escape_value" entry in
              { configuration with escape_value = entry }
          | "first_class_module_path_blacklist" ->
              let entry =
                get_string_list "first_class_module_path_blacklist" entry
              in
              { configuration with first_class_module_path_blacklist = entry }
          | "first_class_module_signature_blacklist" ->
              let entry =
                get_string_list "first_class_module_signature_blacklist" entry
              in
              {
                configuration with
                first_class_module_signature_blacklist = entry;
              }
          | "head_suffix" ->
              let entry = get_string "head_suffix" entry in
              { configuration with head_suffix = entry }
          | "merge_returns" ->
              let entry =
                entry
                |> get_string_triple_list "merge_returns"
                |> List.map (fun (source1, source2, target) ->
                       { MergeRule.source1; source2; target })
              in
              { configuration with merge_returns = entry }
          | "merge_types" ->
              let entry =
                entry
                |> get_string_triple_list "merge_types"
                |> List.map (fun (source1, source2, target) ->
                       { MergeRule.source1; source2; target })
              in
              { configuration with merge_types = entry }
          | "monadic_lets" ->
              let entry =
                entry
                |> get_string_couple_list "monadic_lets"
                |> List.map (fun (name, notation) ->
                       { Operator.name; notation })
              in
              { configuration with monadic_lets = entry }
          | "monadic_let_returns" ->
              let entry =
                entry
                |> get_string_triple_list "monadic_let_returns"
                |> List.map (fun (name, bind, return) ->
                       { MonadicOperators.bind; name; return })
              in
              { configuration with monadic_let_returns = entry }
          | "monadic_returns" ->
              let entry =
                entry
                |> get_string_couple_list "monadic_returns"
                |> List.map (fun (name, notation) ->
                       { Operator.name; notation })
              in
              { configuration with monadic_returns = entry }
          | "monadic_return_lets" ->
              let entry =
                entry
                |> get_string_triple_list "monadic_return_lets"
                |> List.map (fun (name, bind, return) ->
                       { MonadicOperators.bind; name; return })
              in
              { configuration with monadic_return_lets = entry }
          | "operator_infix" ->
              let entry =
                entry
                |> get_string_couple_list "operator_infix"
                |> List.map (fun (name, notation) ->
                       { Operator.name; notation })
              in
              { configuration with operator_infix = entry }
          | "recursion_strategies" ->
              let entry =
                let error_message =
                  "Expected recursion_strategies entries to contain a source, \
                   qualified definition, strategy, and optional integer arity"
                in
                let entries =
                  match entry with
                  | `List entries -> entries
                  | _ -> failwith error_message
                in
                entries
                |> List.map (function
                     | `List
                         [
                           `String source;
                           `String definition;
                           `String strategy;
                         ] ->
                         (source, definition, strategy, None)
                     | `List
                         [
                           `String source;
                           `String definition;
                           `String strategy;
                           `Int arity;
                         ]
                       when arity >= 0 ->
                         (source, definition, strategy, Some arity)
                     | _ -> failwith error_message)
                |> List.map (fun (source, definition, strategy, arity) ->
                       if definition = "" then
                         failwith
                           "Expected a qualified definition name in \
                            recursion_strategies";
                       let kind =
                         match strategy with
                         | "well_founded" ->
                             RecursionStrategy.WellFounded
                         | "partial" -> RecursionStrategy.Partial
                         | "convergent" -> RecursionStrategy.Convergent
                         | _ ->
                             failwith
                               "Expected recursion strategy \"well_founded\", \
                                \"partial\", or \"convergent\""
                       in
                       { RecursionStrategy.source; definition; kind; arity })
              in
              { configuration with recursion_strategies = entry }
          | "renaming_rules" ->
              let entry =
                entry
                |> get_string_couple_list "renaming_rules"
                |> List.map (fun (source, target) ->
                       { RenamingRule.source; target })
              in
              {
                configuration with
                renaming_rules = configuration.renaming_rules @ entry;
              }
          | "renaming_type_constructor" ->
              let entry =
                entry
                |> get_string_couple_list "renaming_type_constructor"
                |> List.map (fun (source, target) ->
                       { RenamingRule.source; target })
              in
              { configuration with renaming_type_constructor = entry }
          | "require" ->
              let entry =
                entry
                |> get_string_couple_list "require"
                |> List.map (fun (source, target) -> { Import.source; target })
              in
              { configuration with require = entry }
          | "require_import" ->
              let entry =
                entry
                |> get_string_couple_list "require_import"
                |> List.map (fun (source, target) -> { Import.source; target })
              in
              { configuration with require_import = entry }
          | "require_long_ident" ->
              let entry =
                entry
                |> get_string_couple_list "require_long_ident"
                |> List.map (fun (source, target) -> { Import.source; target })
              in
              { configuration with require_long_ident = entry }
          | "require_mli" ->
              let entry = get_string_list "require_mli" entry in
              { configuration with require_mli = entry }
          | "variant_constructors" ->
              let entry =
                entry
                |> get_string_couple_list "variant_constructors"
                |> List.map (fun (source, target) ->
                       { VariantMapping.source; target })
              in
              { configuration with variant_constructors = entry }
          | "variant_types" ->
              let entry =
                entry
                |> get_string_couple_list "variant_types"
                |> List.map (fun (source, target) ->
                       { VariantMapping.source; target })
              in
              { configuration with variant_types = entry }
          | "without_default_imports" ->
              let entry = get_bool "without_default_imports" entry in
              { configuration with without_default_imports = entry }
          | "without_guard_checking" ->
              let entry = get_string_list "without_guard_checking" entry in
              { configuration with without_guard_checking = entry }
          | "without_positivity_checking" ->
              let entry = get_string_list "without_positivity_checking" entry in
              { configuration with without_positivity_checking = entry }
          | _ -> failwith ("Unknown entry " ^ id))
        (default file_name) entries
  | _ -> failwith "Expected an object {...}"

let of_optional_file_name (source_file_name : string)
    (configuration_file_name : string option) : t =
  match configuration_file_name with
  | None -> default source_file_name
  | Some configuration_file_name -> (
      let json =
        Yojson.Basic.from_file ~fname:configuration_file_name
          configuration_file_name
      in
      try of_json source_file_name json
      with Failure message ->
        let message =
          "Error in the configuration file '" ^ configuration_file_name ^ "':\n"
          ^ message
        in
        prerr_endline message;
        exit 1)
