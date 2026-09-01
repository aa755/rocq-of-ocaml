open Project.Provider

module Concrete = struct
  type t = int

  let zero = 0
end

module Result = struct
  include
    Extension
      (Concrete)
      (struct
        let modulus =
          let open Operations (Concrete) in
          get ()
      end)
end

let result_get = Result.get ()

module PackagedResult = Project.Provider.Packaged (Concrete)

let packaged_value = PackagedResult.value

module NestedPackaged (Element : ELEMENT) = struct
  include Project.Provider.Packaged (Element)

  module Applied = Project.Provider.Packaged (Element)
end
