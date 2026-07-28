type t = [ `A | `B of int ]

let a : t = `A
let b : t = `B 1

let payload = function
  | `A -> 0
  | `B n -> n

let only_a (x : [> `A ]) =
  match x with
  | `A -> 1
