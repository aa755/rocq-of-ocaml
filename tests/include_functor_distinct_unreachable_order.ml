module Fixed (Width : sig
  val value : int
end) =
struct
  type t = string

  let init f = String.init (Option.get (Some Width.value)) f
  let get value index = String.get value index
  let map f value = init (fun index -> f (get value index))
end

module B20 = struct
  include Fixed (struct
    let value = 20
  end)
end

module B32 = Fixed (struct
  let value = 32
end)

let map = B20.map
let make char = B32.init (fun _ -> char)
