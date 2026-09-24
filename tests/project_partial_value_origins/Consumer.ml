module M = Project.Provider.M
module N = Project.Provider.N
module Applied = Project.Provider.Make (struct let count = 3 end)
module Alias = Applied
module Included = Project.Provider.Included

let read n state = Alias.step n state
let read_current state = Included.current state

let choose flag : int M.t =
  Alias.choose flag ~otherwise:(M.bind (M.return 2) (fun n -> Alias.step n))

let choose_total flag : int M.t =
  Alias.choose flag ~otherwise:(M.return 7)

let observe_choice flag state = choose flag state

let mapped n : int N.t = Project.Provider.lift (Alias.step n)

module Make = struct
  let step n state = (n + 1, state)
end

let total n state = Make.step n state
