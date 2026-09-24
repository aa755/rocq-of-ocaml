module type MONAD = sig
  type 'a t

  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module Runner (Config : sig val offset : int end) = struct
  let rec run n =
    if n = 0 then (Config.offset, n) else run (n - 1)
end

let rec pure_pair left right =
  if left = 0 then right else pure_pair (left - 1) right

module Effectful (M : MONAD) = struct
  let rec resumed_countdown value =
    if value = 0 then M.return 0
    else M.bind (M.return (value - 1)) (fun next -> resumed_countdown next)

end

module Use (M : MONAD) = struct
  module Effects = Effectful (M)

  let execute n : int M.t =
    M.bind (M.return n) (fun value ->
      let module Local = Runner (struct let offset = value end) in
      let result, state = Local.run value in
      let reduced = pure_pair result state in
      M.bind (Effects.resumed_countdown reduced) (fun answer -> M.return (answer + state)))

  let pure_tail n : int M.t =
    let result = pure_pair n n in
    M.return result

  let monadic_tail n : int M.t = Effects.resumed_countdown n
end
