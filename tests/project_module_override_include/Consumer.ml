let included (x : Project.Provider.Impl.t) = x
let reexported (x : Project.Provider.Alias.Impl.t) = x
let fallback b = Option.get (Project.Provider.maybe_zero b)
let shadowed (x : Project.Provider.Shadowed.Impl.t) = not x
let use (x : Project.Provider.Impl.t) = Project.Provider.to_int x
