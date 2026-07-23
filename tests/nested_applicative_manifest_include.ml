module Base = struct
  module Inner (Value : Stdlib.Set.OrderedType) = struct
    type 'a t = Wrap of Value.t * 'a

    let make value payload = Wrap (value, payload)
  end

  module Wrapped (Value : Stdlib.Set.OrderedType) = struct
    include Inner (Value)
  end
end

module Outer (Value : Stdlib.Set.OrderedType) = struct
  module Nested = struct
    include Base.Wrapped (Value)

    let duplicate value payload =
      (make value payload, make value payload)
  end
end
