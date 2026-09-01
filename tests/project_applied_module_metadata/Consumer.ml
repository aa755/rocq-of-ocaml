open Project.Provider

let unwrap (value : Applied.t option) =
  match value with Some value -> value | None -> assert false

let produced = Applied.get true

module Child_result = Applied.Child (Int_value)
