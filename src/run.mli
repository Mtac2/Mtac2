open Term
open Evd
open Environ

module ExistentialSet : Set.S with type elt = existential_key

type elem = (evar_map * ExistentialSet.t * constr)

type data =
  | Val of elem
  | Err of elem

val run : (env * evar_map) -> constr -> data

module MetaCoqNames : sig
  val mkT_lazy : constr Lazy.t
end

val run' :
  Environ.env * Constr.constr * Evd.evar_map * (int * int) list ref list * ExistentialSet.t ->
  Term.constr -> data
