module type ITEM = sig
  type t
end

module Consumer (Item : ITEM) = struct
  type t = Item.t
end

module Concrete = struct
  type t = int
end

module Applied = Consumer (Concrete)
