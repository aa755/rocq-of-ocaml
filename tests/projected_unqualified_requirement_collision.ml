module Source = struct
  let empty = ""

  module Map = struct
    let union value = value
  end
end

let empty = Option.get None
let union value = Option.get value

module Included = struct
  include Source
end

module IncludedMap = struct
  include Source.Map
end
