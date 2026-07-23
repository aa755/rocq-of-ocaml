(** Names declared after an include shadow names from the included namespace. *)
module Namespace = struct
  type retained_type = int
  let retained_value = 17

  module Retained_module = struct
    let value = retained_value
  end

  module type Kept = sig
    type t
  end

  module type Replaced = sig
    val old_value : int
  end

  module Replaced_module = struct
    let old_value = 1
  end
end

include Namespace

module type Replaced = sig
  val new_value : bool
end

module Replaced_module = struct
  let new_value = true
end

let retained_type_value : retained_type = retained_value
let retained_module_value = Retained_module.value

module Use_kept (Value : Kept) = struct
  type t = Value.t
  let witness : t option = None
end
