module Argument = struct
  let token = ()
end

module DirectApplied = Project.Provider.Fixed (Argument)

let projected_missing = DirectApplied.missing

include Project.Provider.Applied

type direct_map = Project.Provider.Applied.Map.t

let unwrapped = Project.Provider.unwrap_int (None : int option)

let local_failure =
  Project.Provider.Local_failure.unwrap
    (None : Project.Provider.Local_failure.t option)

let reexported_failure =
  Project.Provider.Partial_reexport.unwrap (None : int option)

let shadowed_failure =
  Project.Provider.Shadowing.shadowed_unwrap (None : int option)

module Result = Project.Provider.Outer (Argument)
module Alias = Result.Namespace

module AliasedResult = Project.Provider.Aliased (Argument)
module AliasedField = AliasedResult.Alias

type aliased_map = AliasedField.Map.t

module AnonymousInt = Project.Provider.Anonymous (struct
  type t = int
end)

let anonymous_identity = AnonymousInt.identity 42

module Produce (Input : sig
  val value : int
end) =
struct
  let result = Input.value
  let extra = Input.value + 1
end

module Concrete = struct
  let value = 41
end

module Coerced =
  Project.Provider.Consume (Produce) (Concrete)

module NestedApplied = Project.Provider.Nested (Argument)

module ChildApplied = NestedApplied.Child (struct
  let value = 42
end)

let nested_child_value = ChildApplied.value
