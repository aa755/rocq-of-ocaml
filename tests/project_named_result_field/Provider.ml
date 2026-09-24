module M = struct type 'a t = int -> 'a * int end
module type CONFIG = sig val token : unit end
module Config : CONFIG = struct let token = () end
module VmProtocol (Config : CONFIG) = struct
  module type SIG = sig val execute : int -> int M.t end
end
module Instantiate (Config : CONFIG) (Vm : VmProtocol(Config).SIG) : sig
  module Vm : VmProtocol(Config).SIG
end = struct module Vm = Vm end
