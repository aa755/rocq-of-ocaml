module Identity = struct
  type 'a t = 'a
  let return value = value
end

module State (T : sig type t end) = struct
  module Inner = Identity
  type 'a t = T.t -> ('a * T.t) Inner.t
  let return value state = Inner.return (value, state)
end

module Source = struct
  module M = State (struct type t = int end)
end
