module Instantiate (Vm : Project.Provider.VmProtocol(Project.Provider.Config).SIG) = struct
  include Project.Provider.Instantiate (Vm)
  let call input : int Project.Provider.M.t = Vm.execute input
end
