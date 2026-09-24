module type MONAD = sig
  type 'a t
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module Total = struct
  module Runner = struct
    let run n = (n, n)
  end
end

module Outer (M : MONAD) = struct
  module Runner (Config : sig val offset : int end) = struct
    let rec run n =
      if n = 0 then (Config.offset, n) else run (n - 1)
  end

  let rec countdown n : int M.t =
    if n = 0 then M.return n else countdown (n - 1)

  let execute n : int M.t =
    M.bind (M.return n) (fun value ->
      let module Local = Runner (struct let offset = value end) in
      let result, state = Local.run value in
      let left, right = Total.Runner.run result in
      M.bind (countdown left) (fun answer -> M.return (answer + right + state)))

  let execute_shadow n : int M.t =
    let countdown value = M.return (value + 1) in
    M.bind (countdown n) (fun answer -> M.return answer)
end

let[@rocq.partial] rec annotated n =
  if n = 0 then 0 else annotated (n - 1)

let annotated_caller n =
  let result = annotated n in
  result + 1
