open Program
open GraphPgm
open AbsDomain

module type SEMANTICS =
sig
  module StoreDomain : STOREDOMAIN
  val make_m' : NodeDomain.t -> StoreDomain.t -> StoreDomain.t
end
