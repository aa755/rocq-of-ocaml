module Use (Element : sig
  type t
  val zero : t
  val get : t -> t
end) = struct
  let read = Option.get (Some (fun () -> Element.get Element.zero))
end

open Use (Project.Provider.Base)

let read () = read ()
