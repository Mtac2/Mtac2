(** This module defines the parser of the proof mode for Mtac2.

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
  [ () ]
END

(** The parsing rule for the non terminal [mproof_instr]. *)
open Pcoq
GEXTEND Gram
GLOBAL: mproof_instr;
  mproof_instr :
    [[ c=Pcoq.Constr.operconstr ; "." -> Mtac2Instr.Run c ]];
END
