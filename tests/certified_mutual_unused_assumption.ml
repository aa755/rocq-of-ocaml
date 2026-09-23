(* Both nominal result types must remain in the wrappers' assumption
   telescope even if typeclass resolution uses only one of them. *)
type bytes = string

let rec first (values : int list) : bytes =
  match values with [] -> invalid_arg "first" | _ :: tail -> second tail

and second (values : int list) : string =
  match values with [] -> invalid_arg "second" | _ :: tail -> first tail

let call (values : int list) = first values
