(** This module initializes the plugin (parser extension, callbacks, …). *)

open Pcoq  (* required by Camlp5 *)

(**

   Since Coq 8.5, the following directive must appear to declare plugins. See:

   http://lists.gforge.inria.fr/pipermail/coq-commits/2014-July/012704.html

   Remark: We should add a "How-to write your plugin" section in Coq manual.

*)
DECLARE PLUGIN "mtac2"

(** Defines the parser of the proof mode for Mtac2.

    For the moment, this parser is trivial: an MProof command is
    simply a toplevel Gallina term. We will stay with a trivial parser
    as long as Coq's notations are meeting our needs.

*)

(** Introduce a new parsing rule identifier "vernac:mproof_command".
    This rule is expected to produce a vernac expression. *)
let mproof_mode : Vernacexpr.vernac_expr Pcoq.Gram.entry =
  Pcoq.Gram.entry_create "vernac:mproof_command"

(**

   In Coq's parser, the semantic values are typed using the
   module {Genarg} facilities (defined in package "lib").

   We must declare a new type of arguments for MProof instructions
   to type the semantic values produced by our new grammar rule.

   Hence, at the [Genarg] level, we introduce a new type constant
   named "mproof_instr" using the [Genarg.create_arg] function.
   The type of the result [Genarg.genarg_type] is constrained
   to encode the following static property:

   - at the raw level (just after parsing), these semantic values are
   [Mtac2Instr.mproof_instr] ;

   - after parsing, they should not appear anymore. (This is encoded
   by the usage of [Util.Empty.t] type which encode a type with no
   inhabitant.)

*)
let wit_mproof_instr : (Mtac2Instr.mproof_instr, Util.Empty.t, Util.Empty.t) Genarg.genarg_type =
  Genarg.create_arg None "mproof_instr"

(* FIXME: (Yann) I am not 100% sure that using all this machinery is really needed.
   FIXME: Indeed, for the moment [with_mproof_instr] is not used except in the following
   FIXME: instruction.

   FIXME: Besides, is that true that no Mproof instruction will escape the
   FIXME: parsing phase?
*)

(** We introduce a new grammar rule for MProof instructions. The type of
    the semantic values (with_mproof_instr) is specified. *)
let mproof_instr : Mtac2Instr.mproof_instr Pcoq.Gram.entry =
  Pcoq.create_generic_entry "mproof_instr" (Genarg.rawwit wit_mproof_instr)

(** We now declare the grammar rule named [mproof_mode] as the entry point
    for proof instructions (installed by [Mtac2Mode] in [ProofGlobal]).

    A grammar rule is defined in three parts (i) the producers ;
    (ii) the effect descriptor needed by STM (iii) the semantic
    value.

    Here, there is only one producer: the non terminal [mproof_instr]
    whose parsing rules are defined at the end of this file. The minus
    sign at the beginning of the rule means that there is no specific
    keyword starting the words derived from this non terminal.

    As far as I understand STM machinery:
    - [VtProofStep false] means that the interpretation of the proof step
    cannot be parallelized.
    - [VtLater] means that the command does not alter the parser and can
    therefore by executed after the parsing of the rest of the source file.

    Finally, we do not produce any semantic value for the moment.

*)

VERNAC mproof_mode EXTEND MProofInstr
  [ - mproof_instr(_instr) ] => [ Vernacexpr.VtProofStep false, Vernacexpr.VtLater ] ->
  [ Mtac2Interp.interp_proof_constr _instr ]
END

(** The parsing rule for the non terminal [mproof_instr]. *)
GEXTEND Gram
GLOBAL: mproof_instr;
  mproof_instr :
    [[ c=Pcoq.Constr.operconstr ; "." -> Mtac2Instr.Mtac2_constr c ]];
END

(** Initialize the proof mode MProof for Mtac2. *)

(** The following identifiers must be globally unique. They are used
    in several global tables to register some callbacks (for instance
    for the parser and the interpreter). *)
let proof_mode_identifier = "MProof"

(** Register the proof mode.

    See proof_global.mli for a documentation on the role of each of
    the following fields.

    In our case, we have to set the command entry to "mproof_mode"
    defined in the Mtac2Parser when we enter in proof mode. This
    dynamically change the parser for the proof script instructions.
    See Mtac2Parser to know the syntax of our proof instructions.

    We also reset to the noedit_mode when we quit the mtac2 proof
    mode.
*)
(* FIXME: (Yann) What is exactly this noedit_mode? *)
let () =
  Proof_global.register_proof_mode {
    Proof_global.
    name  = proof_mode_identifier ;
    set   =
      begin fun () ->
        G_vernac.set_command_entry mproof_mode
      end ;
    reset =
      begin fun () ->
       G_vernac.set_command_entry G_vernac.noedit_mode
      end
  }

(** The following command extends both the parser and the interpreter
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
  -> [ Mtac2Interp.interp_mproof_command () ]
END
