let count_selected get limit =
  let rec loop index count =
    if index >= limit then count
    else
      match get index with
      | ('a' | 'b') as selected ->
          loop (index + 1) (count + Char.code selected)
      | _ -> loop (index + 1) count
  in
  loop 0 0
