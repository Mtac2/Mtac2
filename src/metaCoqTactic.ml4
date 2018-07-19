(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

open Ltac_plugin
open MetaCoqInterp
open Stdarg
open Pcoq.Constr

DECLARE PLUGIN "MetaCoqPlugin"

let print_mtac_type _ _ _ _ = Pp.mt ()

(* (reference, global_reference located or_var, global_reference) *)
let interp_mtac_type ist gl r = (gl.Evd.sigma, r)

let subst_mtac_type subst r =
  let ty, r = r in
  (ty, fst (Globnames.subst_global subst r))

ARGUMENT EXTEND mtac_type
  PRINTED BY print_mtac_type

  INTERPRETED BY interp_mtac_type
  GLOBALIZED BY glob_mtac_type
  SUBSTITUTED BY subst_mtac_type

| [ global(l) ] -> [ l ]
END

TACTIC EXTEND mrun
  | [ "mrun_static" mtac_type(c) ] -> [ MetaCoqRun.run_tac_constr (StaticallyChecked c) ]
  | [ "mrun" uconstr(c) ] -> [ MetaCoqRun.run_tac_constr (DynamicallyChecked c) ]
END

VERNAC COMMAND EXTEND MtacDo CLASSIFIED AS SIDEFF
  | [ "Mtac" "Do" uconstr(c) ] -> [
      MetaCoqRun.run_cmd c
  ]
END
