let has_even_length values =
  let rec even values =
    match values with
    | [] -> true
    | _ :: values -> odd values
  and odd values =
    match values with
    | [] -> false
    | _ :: values -> even values
  in
  even values
