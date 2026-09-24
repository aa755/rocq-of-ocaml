module M = struct
  type 'a t = int -> 'a * int
  let return value state = (value, state)
  let bind action next state = let value, state = action state in next value state
end
module type VM = sig val execute : int -> int M.t end
module Make (Vm : VM) = struct
  let choose flag ~(otherwise : int M.t) : int M.t =
    if flag then Vm.execute 1 else otherwise
  let call flag : int M.t =
    choose flag ~otherwise:(M.bind (M.return 2) (fun n -> Vm.execute n))
  let total flag : int M.t = choose flag ~otherwise:(M.return 3)
  let curried flag : int M.t = (choose flag) ~otherwise:(Vm.execute 4)
  let positional flag (fallback : int M.t) : int M.t =
    if flag then Vm.execute 5 else fallback
  let call_positional flag : int M.t = positional flag (Vm.execute 6)
end
module Impl = struct
  let rec execute n : int M.t =
    if n = 0 then M.return n
    else M.bind (M.return (n - 1)) (fun n -> execute n)
end
module Concrete = Make (Impl)
