open Project.Provider

module Result = struct
  include Make (struct
    let value = 42
  end)
end
