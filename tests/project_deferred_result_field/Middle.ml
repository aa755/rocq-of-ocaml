module Host (Params : sig val enabled : bool end) = struct
  module M = Project.Provider.State (struct type t = int end)
  let enabled = Params.enabled
end
module Instantiate (Params : sig val enabled : bool end) = struct
  module Host = Host (Params)
end

module IncludedHost (Params : sig val enabled : bool end) = struct
  include Project.Provider.Source
  let enabled = Params.enabled
  let included_marker = 1
end

module IncludedInstantiation (Params : sig val enabled : bool end) = struct
  module Host = IncludedHost (Params)
end
