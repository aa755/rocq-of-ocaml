let apply converter =
  let __0 = converter in
  fun value -> __0 value

let result = apply (fun value -> value + 1) 41
