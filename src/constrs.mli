open Constr

module Constr : sig
  exception Constr_not_found of string
  exception Constr_poly of string

  val mkConstr : string -> constr Lazy.t

  val mkUConstr : string -> Evd.evar_map -> Environ.env
    -> (Evd.evar_map * constr)

  val isConstr : Term.constr Lazy.t -> Term.constr -> bool

end

module ConstrBuilder : sig
  type t

  val from_string : string -> t

  val from_coq : t -> (Environ.env * Evd.evar_map)
    -> constr -> constr array

  val build_app : t -> constr array -> constr

  val equal : t -> constr -> bool
end

module UConstrBuilder : sig
  type t

  val build_app : t -> Evd.evar_map -> Environ.env
    -> constr array -> (Evd.evar_map * constr)
end

module CoqN : sig

  val from_coq : (Environ.env * Evd.evar_map) -> constr -> int
  val to_coq : int -> constr
end

module CoqString : sig

  val from_coq : (Environ.env * Evd.evar_map) -> constr -> string
  val to_coq : string -> constr

end

module CoqList : sig

  val makeNil : types -> constr
  val makeCons : types -> constr -> constr -> constr
  val makeType : types -> types
  val from_coq : (Environ.env * Evd.evar_map) -> constr -> constr list
  val from_coq_conv : (Environ.env * Evd.evar_map) -> (constr -> 'a)
    -> constr -> 'a list
  val to_coq : types -> ('a -> constr) -> 'a list -> constr
end

module CoqOption : sig

  val mkNone : types -> constr

  val mkSome : types -> constr -> constr

  val from_coq : (Environ.env * Evd.evar_map) -> constr
    -> constr option
end

module CoqUnit : sig
  val mkTT : constr Lazy.t
end

module CoqBool : sig
  val mkTrue : constr
  val mkFalse : constr
end

module CoqEq : sig
  val mkAppEq : types -> constr -> constr -> constr
  val mkAppEqRefl : types -> constr -> constr
end

module CoqSig : sig
  val from_coq : (Environ.env * Evd.evar_map) -> constr -> constr
end

module MCTactics : sig
  val mkReduceGoal : constr Lazy.t
  val mkRunTac : constr Lazy.t
  val mkTactic : constr Lazy.t
end

module CoqPair : sig
  val mkPair : types -> types -> constr -> constr -> constr
end
