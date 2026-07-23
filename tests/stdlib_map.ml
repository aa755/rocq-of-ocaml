(** [Stdlib.Map] is mapped to the executable Gallina compatibility layer. *)
module Int_order = struct
  type t = int
  let compare left right = left - right
end

module Int_map = Stdlib.Map.Make (Int_order)

let example =
  Int_map.empty
  |> Int_map.add 2 "two"
  |> Int_map.add 1 "one"

let lookup_one = Int_map.find_opt 1 example
