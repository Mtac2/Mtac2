open Term
open Evd
open Environ

module ExistentialSet : Set.S with type elt = existential_key

type data =
  | Val of (evar_map * ExistentialSet.t * constr)
  | Err of (evar_map * ExistentialSet.t * constr)

val run : (env * evar_map) -> constr -> data

module MtacNames : sig
  val mkT_lazy : evar_map -> env -> (evar_map * constr)
end

val run' :
  Environ.env * Constr.constr * Evd.evar_map * (int * int) list ref list * ExistentialSet.t ->
  Term.constr -> data
