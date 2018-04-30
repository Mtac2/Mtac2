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

let glob_mtac_type ist r =
  let loc,_ as lqid = Libnames.qualid_of_reference r in
  try
  let gr =
    (Smartlocate.locate_global_with_alias lqid) (* Maybe put loc back in for error reporting *)
  in
  (* Typecheck here. Unification? probably *)
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let sigma, t = EConstr.fresh_global env sigma gr in
    let ty = Retyping.get_type_of env sigma t in
    let (h, args) = Reductionops.whd_all_stack env sigma ty in
    let sigma, metaCoqType = MtacNames.mkT_lazy sigma env in
    if EConstr.eq_constr_nounivs sigma metaCoqType h && List.length args = 1 then
       (Program (List.hd args), gr)
    else
      let b, sigma = ifTactic env sigma ty t in
      if b then
        (GTactic, gr)
      else
        CErrors.user_err (Pp.str "Not a Mtactic")
  with Not_found -> Nametab.error_global_not_found (snd lqid)

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
