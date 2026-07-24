type info = {
  code : int;
}

let info code : info = {code}
let info_code code = (info code).code

module Nested = struct
  type status =
    | Ready
    | Failed

  let status ready = if ready then Ready else Failed
  let is_ready ready = match status ready with Ready -> true | Failed -> false
end

let nested_status ready = Nested.status ready
