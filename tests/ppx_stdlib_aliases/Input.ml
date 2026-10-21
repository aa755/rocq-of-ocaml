module Sets (S : Ppx_deriving_runtime.Set.S) = struct
  let insert value set = S.add value set
  let contains value set = S.mem value set
end

module Maps (M : Ppx_deriving_runtime.Map.S) = struct
  let insert key value map = M.add key value map
  let lookup key map = M.find_opt key map
end
