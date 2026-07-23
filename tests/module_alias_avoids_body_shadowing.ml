module Shared = struct
  let value = 7
end

module Shared_alias = Shared

module Container = struct
  module Shared = struct
    let inherited = Shared.value
  end
end

let result = Container.Shared.inherited
