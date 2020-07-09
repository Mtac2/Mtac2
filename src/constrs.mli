open Evd
open EConstr

val decompose_appvect : evar_map -> constr -> constr * constr array

module Constrs : sig
  exception Constr_not_found of string
  exception Constr_poly of string

  val mkUGlobal : string -> Names.GlobRef.t

  val mkConstr : string -> constr Lazy.t

  val mkConstr_of_global : Names.GlobRef.t Lazy.t -> constr

  val mkUConstr : string -> evar_map -> Environ.env -> (Evd.evar_map * constr)

  val mkUConstr_of_global : Names.GlobRef.t -> evar_map -> Environ.env -> (Evd.evar_map * constr)

  val isConstr : evar_map -> constr Lazy.t -> constr -> bool
end

module ConstrBuilder : sig
  type t

  val from_string : string -> t

  val from_coq : t -> (Environ.env * Evd.evar_map) -> constr -> (constr array) option

  val build_app : t -> constr array -> constr

  val equal : evar_map -> t -> constr -> bool
end

module UConstrBuilder : sig
  type t

  val from_string : string -> t

  val from_coq : t -> (Environ.env * Evd.evar_map) -> constr -> (constr array) option

  val build_app : t -> Evd.evar_map -> Environ.env
    -> constr array -> (Evd.evar_map * constr)
end

module CoqN : sig
  exception NotAnN

  val from_coq : (Environ.env * Evd.evar_map) -> constr -> int
  val to_coq : int -> constr
end

module CoqZ : sig
  val to_coq : int -> constr
end

module CoqString : sig
  exception NotAString

  val from_coq : (Environ.env * Evd.evar_map) -> constr -> string
  val to_coq : string -> constr
end

module type ListParams = sig
  val nilname : string
  val consname : string
  val typename : string
end

module type LIST = sig
  val mkNil : Evd.evar_map -> Environ.env -> types -> Evd.evar_map * constr
  val mkCons : Evd.evar_map -> Environ.env -> types -> constr -> constr -> Evd.evar_map * constr
  val mkType : Evd.evar_map -> Environ.env -> types -> Evd.evar_map * types

  exception NotAList of constr

  val from_coq : Evd.evar_map -> Environ.env -> constr -> constr list

  (** Allows skipping an element in the conversion *)
  exception Skip
  val from_coq_conv : Evd.evar_map -> Environ.env -> (Evd.evar_map -> constr -> Evd.evar_map * 'a) -> constr -> Evd.evar_map * 'a list

  val to_coq : Evd.evar_map -> Environ.env -> types -> (Evd.evar_map -> 'a -> Evd.evar_map * constr) -> 'a list -> Evd.evar_map * constr
  val pto_coq : Environ.env -> types -> ('a -> Evd.evar_map -> Evd.evar_map * constr) -> 'a list -> Evd.evar_map -> Evd.evar_map * constr
end

module GenericList : functor (LP : ListParams) -> LIST

module CoqList : LIST

module CoqOption : sig
  val mkNone : Evd.evar_map -> Environ.env -> types -> Evd.evar_map * constr
  val mkSome : Evd.evar_map -> Environ.env -> types -> constr -> Evd.evar_map * constr

  exception NotAnOption

  val from_coq : Evd.evar_map -> Environ.env -> constr -> constr option

  (** to_coq ty ot constructs an option type with type ty *)
  val to_coq : Evd.evar_map -> Environ.env -> types -> constr option -> Evd.evar_map * constr
end

module CoqUnit : sig
  val mkType : constr
  val mkTT : constr
end

module CoqBool : sig

  val mkType : constr
  val mkTrue : constr
  val mkFalse : constr

  exception NotABool

  val to_coq : bool -> constr
  val from_coq : evar_map -> constr -> bool
end

module CoqEq : sig
  val mkType : Evd.evar_map -> Environ.env -> types -> constr -> constr -> Evd.evar_map * constr
  val mkEqRefl : Evd.evar_map -> Environ.env -> types -> constr -> Evd.evar_map * constr
end

module CoqSig : sig
  val from_coq : (Environ.env * Evd.evar_map) -> constr -> constr
end

module MCTactics : sig
  val mkGTactic : Environ.env -> Evd.evar_map -> Evd.evar_map * constr
end

module CoqPair : sig
  exception NotAPair

  val mkPair : Evd.evar_map -> Environ.env -> types -> types -> constr -> constr -> Evd.evar_map * constr

  val from_coq : (Environ.env * Evd.evar_map) -> constr -> constr * constr
end

module CoqMTele : sig
  exception NotAnMTele

  val from_coq : Evd.evar_map -> Environ.env -> constr -> (constr * constr) option
end

module CoqSigT : sig
  exception NotAmexistT

  val from_coq : Evd.evar_map -> Environ.env -> constr -> (constr * constr)
end


module CoqSort : sig
  val mkSType : Environ.env -> Evd.evar_map -> Evd.evar_map * EConstr.t
  val mkSProp : Environ.env -> Evd.evar_map -> Evd.evar_map * EConstr.t
  exception NotASort
  type sort = Prop_sort | Type_sort
  val from_coq : Evd.evar_map -> Environ.env -> EConstr.t -> sort
  val to_coq :
    Evd.evar_map -> Environ.env -> sort -> Evd.evar_map * EConstr.t
end

module CoqInd_Dyn : sig
  exception NotAmkInd_dyn
  val from_coq : Evd.evar_map -> 'a -> EConstr.t -> EConstr.t array
  val to_coq :
    Evd.evar_map ->
    Environ.env -> EConstr.t array -> Evd.evar_map * EConstr.t
end
