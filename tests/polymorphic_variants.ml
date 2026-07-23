type t = [ `A | `B of int ]

let a : t =
  `A

let b : t =
  `B 1

let match_variant (x : t) =
  match x with
  | `A -> 0
  | `B n -> n

let match_open (x : [> `A | `B of int ]) =
  match x with
  | `A -> 0
  | `B n -> n
  | _ -> -1

type active = [ `A | `B of int ]

let narrow (x : [ `A | `B of int | `C ]) : active option =
  match x with
  | #active as active -> Some active
  | _ -> None
