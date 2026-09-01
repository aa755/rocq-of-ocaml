let pair flag (values : int Iarray.t) =
  let values = if flag then values else assert false in
  let number = if flag then 0 else assert false in
  (values, number)
