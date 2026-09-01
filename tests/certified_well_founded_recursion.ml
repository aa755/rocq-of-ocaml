module Through_view = struct
  let view = function [] -> None | value :: values -> Some (value, values)

  let rec length values =
    match view values with
    | None -> 0
    | Some (_, tail) -> 1 + length tail
end

module Mutual = struct
  let rec left (values : int list) =
    match values with [] -> 0 | _ :: values -> 1 + right values

  and right (values : int list) =
    match values with [] -> 0 | _ :: values -> 1 + left values
end

type wrapped = Wrap of int

module Overlapping_names = struct
  let rec decode (values : int list) =
    match values with
    | [] -> 0
    | _ :: values ->
        let (Wrap result) = small_decode values in
        result

  and small_decode (values : int list) =
    match values with [] -> Wrap 0 | _ :: values -> Wrap (decode values)
end
