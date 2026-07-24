module Argument = struct
  let token = ()
end

type direct_map = Project.Provider.Applied.Map.t

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
