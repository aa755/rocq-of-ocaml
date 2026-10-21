let rec equal =
  let compare = Int.equal in
  fun (left : int) (right : int) -> compare left right

let rec shadowed =
  let shadowed value = value + 1 in
  fun (value : int) -> shadowed value

let rec nested =
  let rec length = function [] -> 0 | _ :: tail -> 1 + length tail in
  fun (values : int list) -> length values

let rec recursive = function [] -> 0 | _ :: tail -> 1 + recursive tail
