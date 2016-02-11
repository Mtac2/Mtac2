
module TacticNames : sig

  val tacType : unit -> Constr.constr

end

exception UserException of Constr.constr

val interp : Constr.constr -> unit Proofview.tactic

(* debug *)
val debug : exn -> unit
