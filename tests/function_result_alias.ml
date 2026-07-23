module State (T : sig
  type t
end) =
struct
  type 'a m = T.t -> 'a * T.t

  let return (value : 'a) : 'a m = fun state -> (value, state)

  let map (f : 'a -> 'b) (computation : 'a m) : 'b m =
   fun state ->
    let value, state = computation state in
    (f value, state)
end
