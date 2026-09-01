module type PARAM = sig
  val optional : int option
end

module Inner (Param : PARAM) = struct
  module StorageKey = struct
    type t = int

    module Set = Set.Make (Int)
  end

  let required = Option.get Param.optional
  let accessed_keys : StorageKey.Set.t = StorageKey.Set.empty
end

module Outer (Param : PARAM) = struct
  module Host = Inner (Param)
end

module Reexport (Param : PARAM) = struct
  module Instantiation = Outer (Param)
  module Host = Instantiation.Host
end
