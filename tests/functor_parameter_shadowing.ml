module type MONAD = sig
  type 'a t
  val return : 'a -> 'a t
end

module Enrich (M : MONAD) = struct
  type 'a t = 'a M.t
  let return = M.return
  let map f x = M.return (f x)

  module Nested = struct
    let identity value = value
  end
end

module Enrich_alias = Enrich

module Trans (Inner : MONAD) = struct
  module Inner = Enrich_alias (Inner)

  let lift x = Inner.map (fun value -> value) x
end

module Included = struct
  include Enrich_alias (struct
    type 'a t = 'a
    let return value = value
  end)

  module Nested = struct
    include Nested
    let apply value = identity value
  end
end

let included_result = Included.map (( + ) 1) 2
let inherited_nested_result = Included.Nested.apply 3
