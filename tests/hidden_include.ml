type t = {value : int}

include struct
  let _ = fun (_ : t) -> ()
end
[@@merlin.hide]

include struct
  let generated value = value + 1
end
[@@merlin.hide]

let get x = x.value
let generated_result = generated 41

type tree = Leaf of int | Node of tree list

include struct
  let rec equal left right =
    match left, right with
    | Leaf x, Leaf y -> Int.equal x y
    | Node xs, Node ys ->
        let rec loop xs ys =
          match xs, ys with
          | [], [] -> true
          | x :: xs, y :: ys -> equal x y && loop xs ys
          | _ -> false
        in
        loop xs ys
    | _ -> false
end
[@@merlin.hide]

include struct
  let shadowed = 1
  let previous = shadowed
end
[@@merlin.hide]

let shadowed = 2

include (struct
  let helper x = x + 1
  let constrained x = helper x
end : sig val constrained : int -> int end)
[@@merlin.hide]

let constrained_result = constrained 41
