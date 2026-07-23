(** [Stdlib.Set] shares the ordered-type interface used by [Stdlib.Map]. *)
module Int_order = struct
  type t = int
  let compare left right = left - right
end

module Int_set = Stdlib.Set.Make (Int_order)

let example = Int_set.of_list [3; 1; 2; 1]
let contains_two = Int_set.mem 2 example
