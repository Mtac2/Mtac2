(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)
open MetaCoqInterp

DECLARE PLUGIN "MetaCoqPlugin"

TACTIC EXTEND mrun
  | [ "mrun" uconstr(c) ] -> [ MetaCoqRun.run_tac_constr c ]
END
