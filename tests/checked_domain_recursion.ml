let rec length (values : int list) =
  match values with [] -> 0 | _ :: tail -> 1 + length tail

let local_length (values : int list) =
  let rec loop (values : int list) =
    match values with [] -> 0 | _ :: tail -> 1 + loop tail
  in
  loop values
