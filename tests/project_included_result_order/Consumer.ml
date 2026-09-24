open Project.Provider

module Make (Config : sig
  val enabled : bool
end) = struct
  include Source
  let enabled = Config.enabled

  (** Retain explicit fallback arguments when packaging this documented value. *)
  let documented () = empty
end

module Result = Make (struct
  let enabled = true
end)

let exported = Result.empty
