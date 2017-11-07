open Evd
open EConstr

val decompose_appvect : evar_map -> constr -> constr * constr array

module Constr : sig
  exception Constr_not_found of string
  exception Constr_poly of string

  val mkConstr : string -> constr Lazy.t

  val mkUConstr : string -> evar_map -> Environ.env -> (Evd.evar_map * constr)

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
  val mkNil : types -> constr
  val mkCons : types -> constr -> constr -> constr
  val mkType : types -> types

  exception NotAList of constr

  val from_coq : (Environ.env * Evd.evar_map) -> constr -> constr list

  (** Allows skipping an element in the conversion *)
  exception Skip
  val from_coq_conv : (Environ.env * Evd.evar_map) -> (constr -> 'a) -> constr -> 'a list

  val to_coq : types -> ('a -> constr) -> 'a list -> constr
  val pto_coq : types -> ('a -> Evd.evar_map -> Evd.evar_map * constr) -> 'a list -> Evd.evar_map -> Evd.evar_map * constr
end

module GenericList : functor (LP : ListParams) -> LIST

module CoqList : LIST

module CoqOption : sig
  val mkNone : types -> constr
  val mkSome : types -> constr -> constr

  exception NotAnOption

  val from_coq : (Environ.env * Evd.evar_map) -> constr -> constr option

  (** to_coq ty ot constructs an option type with type ty *)
  val to_coq : types -> constr option -> constr
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
  val mkType : types -> constr -> constr -> constr
  val mkEqRefl : types -> constr -> constr
end

module CoqSig : sig
  val from_coq : (Environ.env * Evd.evar_map) -> constr -> constr
end

module MCTactics : sig
  val mkGTactic : Environ.env -> Evd.evar_map -> Evd.evar_map * Term.constr
end

module CoqPair : sig
  exception NotAPair

  val mkPair : types -> types -> constr -> constr -> constr

  val from_coq : (Environ.env * Evd.evar_map) -> constr -> constr * constr
end
