module Make (Params : sig val enabled : bool end) = struct
  module Instantiation = Project.Middle.Instantiate (Params)
  module Host = Instantiation.Host
  include Host
end
