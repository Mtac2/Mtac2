(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

open Ltac_plugin
open MetaCoqInterp
open Stdarg

DECLARE PLUGIN "MetaCoqPlugin"

TACTIC EXTEND mrun
  | [ "mrun" uconstr(c) ] -> [ MetaCoqRun.run_tac_constr c ]
END

VERNAC COMMAND EXTEND MtacDo CLASSIFIED AS SIDEFF
  | [ "Mtac" "Do" uconstr(c) ] -> [
      MetaCoqRun.run_cmd c
  ]
END
