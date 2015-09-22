(** This module run the interpretation of a constr
*)

open Proofview.Notations

(**  *)
let pretypeT env sigma t c =
  let (_, e) = Run.MtacNames.mkT_lazy sigma env in
  let ty = Retyping.get_type_of env sigma c in
  let (h, args) = Reductionops.whd_betadeltaiota_stack env sigma ty in
  if Term.eq_constr_nounivs e h && List.length args = 1 then
    let sigma = Evarconv.the_conv_x_leq env t (List.hd args) sigma in
    (sigma, c)
  else
    Errors.error "Not a Mtactic"

(** Get back the context given a goal, interp the constr_expr to obtain a constr
    Then run the interpretation fo the constr, and returns the tactic value,
    according to the value of the data returned by [run].
*)
let run_tac t =
  Proofview.Goal.nf_enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let concl = Proofview.Goal.concl gl in
    let sigma,c = Constrintern.interp_open_constr env sigma t in
    let (sigma, t) = pretypeT env sigma concl c in
    let r = Run.run (env, sigma) c in
    match r with
    | Run.Val (sigma', _, v) ->
        (Proofview.Unsafe.tclEVARS sigma')
        <*> (Proofview.Refine.refine ~unsafe:false (fun s->(s, v)))
    | Run.Err (_, _, e) ->
        Errors.error ("Uncaught exception: " ^ (Pp.string_of_ppcmds (Termops.print_constr e)))
  end
