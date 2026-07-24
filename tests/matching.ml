let n = match ([1; 2], false) with
  | ([x; _], true) -> x
  | ([_; y], false) -> y
  | _ -> 0

type t = Bar of int | Foo of bool * string

let m x =
  match x with
  | _ when 1 = 2 -> 3
  | Bar n when n > 12 -> n
  | Bar k when k = 0 -> k
  | Bar n -> -n
  | Foo _ -> 0

let guarded_unit n =
  match () with
  | () when n > 0 -> n
  | () -> 0
