module type PARAM = sig
  val value : int
end

module GlobalAddress = struct
  type create2_params = { salt : int }
end

module State (Param : PARAM) = struct
  module Inner = struct
    let return = Param.value
  end
end

module Inner (Param : PARAM) = struct
  module Address = GlobalAddress

  module StorageKey = struct
    type t = int

    module Set = Set.Make (Int)
  end

  let accessed_keys : StorageKey.Set.t = StorageKey.Set.empty

  module M = State (Param)

  module Nested = struct
    let value = Param.value
  end
end

module Outer (Param : PARAM) = struct
  module Host = Inner (Param)
end

module Reexport (Param : PARAM) = struct
  module Instantiation = Outer (Param)
  module Host = Instantiation.Host
end

module Param = struct
  let value = 42
end

module Instantiation = Outer (Param)
let direct_result = Instantiation.Host.Nested.value

module Host = Instantiation.Host

let result = Host.Nested.value
let accessed_keys = Host.accessed_keys
