module Fixed (Width : sig
  val value : int
end) =
struct
  type t = string

  let init f = String.init (Option.get (Some Width.value)) f
  let get value index = String.get value index

  let reverse value =
    init (fun index -> get value (Width.value - index - 1))
end
