module Make (Params : sig val enabled : bool end) = struct
  module Instantiation = Project.Middle.Instantiate (Params)
  module Host = Instantiation.Host
  include Host
end

module IncludedMake (Params : sig val enabled : bool end) = struct
  module Instantiation = Project.Middle.IncludedInstantiation (Params)
  module Host = Instantiation.Host
  let use (value : int) : int Host.M.Inner.t = Host.M.Inner.return value
end
