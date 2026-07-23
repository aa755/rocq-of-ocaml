module Source = struct
  let map value = value + 1
end

module Uses_include = struct
  include Source

  let apply value = map value

  include Source
end

let result = Uses_include.apply 2
