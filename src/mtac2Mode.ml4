(** This module initializes the proof mode MProof for Mtac2. *)

(*i camlp4deps: "grammar/grammar.cma" i*)

(** The following identifiers must be globally unique. They are used
    in several global tables to register some callbacks (for instance
    for the parser and the interpreter). *)

let proof_mode_identifier = "MProof"

(** Register a proof mode. 

    See proof_global.mli for a documentation on the role of each of
    the following fields. In our case, there are no state to restore
    and save when we go from and to the standard proof mode.

 *)
let _ =
  Proof_global.register_proof_mode {
    Proof_global.
    name  = proof_mode_identifier ;
    set   = begin fun () -> () end ;
    reset = begin fun () -> () end 
  }

(**

   The following command extends both the parser and the interpreter
   of the Vernacular language so that a new keyword "MProof" is
   recognized and is interpreted as the entry point for a proof 
   written in Mtac.

   In the following command:

   - On the first line, "MProofCommand" is a new constructor in the
     abstract syntax tree of VernacExpr. It will appear as an
     [extend_name] after the [VernacExtend]. Notice that [extend_name]
     is a pair of a string (which is "MProofCommand" here) and an
     integer which represents the index of the interpretation rule
     (here 0).

   - On the second line, [ "MProof" ] is the right hand side of the 
     unique grammar rule for the non terminal MProofCommand.

   - On the third line, there are two classifiers that influence
     the interpretation of this command. 

     "VtProofMode" classifies the command as a proof mode introducer.
     The "proof_mode_identifier" is used as a key in 
     Vernac_classifier.classifiers. 

     "VtNow" indicates that the interpretation of this command cannot
     be done in the background asynchronously. Indeed, changing the
     proof mode has an effect on the parsing and the interpretation
     of the subsequent commands. 

    - On the fourth line, the interpretation function is given. This
     interpretation function is registered in Vernacinterp and called
     in Vernacentries.interp.

*)
VERNAC COMMAND EXTEND MProofCommand
  [ "MProof" ] 
  => [ Vernacexpr.VtProofMode proof_mode_identifier, Vernacexpr.VtNow  ] 
  -> [ () ]
END
