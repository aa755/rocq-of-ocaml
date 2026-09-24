module Runner (Config : sig
  val offset : int
end) = struct
  let rec run n =
    if n = 0 then (Config.offset, n) else run (n - 1)

  let rec finished n =
    if n = 0 then true else finished (n - 1)
end

let execute n =
  let module Local = Runner (struct
    let offset = n
  end) in
  let result, state = Local.run n in
  result + state

module Total = struct
  module Runner = struct
    module Runner_result = struct
      let run n = (n, n)
    end
  end
end

let total n =
  let result, state = Total.Runner.Runner_result.run n in
  result + state

let execute_bound n =
  let module Local = Runner (struct
    let offset = n
  end) in
  let pair = Local.run n in
  let result, state = pair in
  result + state

let execute_condition n =
  let module Local = Runner (struct
    let offset = n
  end) in
  if Local.finished n then 1 else 0

let execute_mixed n =
  let module Local = Runner (struct
    let offset = n
  end) in
  let result, state = Total.Runner.Runner_result.run n in
  Local.run (result + state)

let execute_hygienic n _rocq_partial_scrutinee =
  let module Local = Runner (struct
    let offset = n
  end) in
  let result, state = Local.run n in
  result + state + _rocq_partial_scrutinee
