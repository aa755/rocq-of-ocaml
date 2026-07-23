exception Parse_error of string

let recover f =
  try Ok (f ()) with
  | Parse_error message -> Error message
  | _ -> Error "unknown"

let recover_any value =
  try value with
  | _ -> 0

let recover_only f =
  try Ok (f ()) with
  | Parse_error message -> Error message
