module Wrapper (X : sig type t val initial : t end) = struct
  module Base = Project.Provider.Outer (X)
  include Base

  module Run (C : sig val state : Memory.t end) = struct
    include Base.Run (C)

    module Step = struct
      let mixed = mixed
    end
  end
end
