module Host (Params : sig val enabled : bool end) = struct
  module M = Project.Provider.State (struct type t = int end)
  let enabled = Params.enabled
end
module Instantiate (Params : sig val enabled : bool end) = struct
  module Host = Host (Params)
end
