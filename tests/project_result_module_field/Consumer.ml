module Argument = struct
  let token = ()
end

module Result = Project.Provider.Outer (Argument)
module Alias = Result.Namespace
