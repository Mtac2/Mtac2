module R = Run
module PV = Proofview
module CB = Constrs.ConstrBuilder
module CC = Constrs.Constr
module RO = Reductionops
module Stack = Reductionops.Stack

open PV.Notations

type constr = Term.constr

module Exceptions = struct

  let refineExceptionBuilder = CB.from_string "MetaCoq.Tactic.CouldntRefine"

  let refineException x y = CB.build_app refineExceptionBuilder [|x;y|]

  let error_stuck () =
    Errors.error "Cannot reduce term, perhaps an opaque definition?"

end

module TacticNames = struct

  let tacType () = Lazy.force (CC.mkConstr "MetaCoq.Tactic.Tactic")

end

let index_of c =
  if Term.isConstruct c then
    let ((m, ix), _) = Term.destConstruct c in
    if Names.eq_ind m (fst (Term.destInd (TacticNames.tacType ()))) then
      ix
    else
      Exceptions.error_stuck ()
  else
    Exceptions.error_stuck ()

exception UserException of constr

let evars_list_of_term c =
  let rec evrec acc c =
    match Term.kind_of_term c with
    | Term.Evar (n, l) -> n :: (Array.fold_left evrec acc l)
    | _ -> Term.fold_constr evrec acc c
  in
  evrec [] c

let debug : exn -> unit = fun _ -> ()

let rec interp (c : constr) : unit PV.tactic =
  PV.tclEVARMAP >>= fun sigma ->
  PV.tclENV >>= fun env ->
  let (h, args) = RO.whd_betadeltaiota_state env sigma (c, []) in
  let nth = Stack.nth args in
  match index_of h with
  | 1 -> (* Tthen *)
      let t1 = interp (nth 0) in
      let t2 = fun _ -> interp (nth 1) in
      PV.tclBIND t1 t2

  | 2 -> (* Trefine *)
      let tm = nth 1 in
      let evs = evars_list_of_term tm in
      let rprinc_goal = ref None in
      let rgoals = ref [] in
      let open Type_errors in begin
        PV.tclOR
          begin PV.Refine.refine ~unsafe:false begin fun sigma ->
            rprinc_goal := Evd.principal_future_goal sigma;
            rgoals := Evd.future_goals sigma;
            let sigma = List.fold_right Evd.declare_future_goal evs sigma in
            (sigma, nth 1)
          end end
          begin fun (e, _) ->
            match e with
              TypeError(_, (ActualType (a,b))) ->
                Printf.printf "aca!\n";
                PV.tclEVARMAP >>= fun sigma ->
                let sigma = Evd.reset_future_goals sigma in
                let sigma = Evd.restore_future_goals sigma !rgoals !rprinc_goal in
                PV.Unsafe.tclEVARS sigma <*>
                PV.tclZERO (UserException (Exceptions.refineException a.uj_type b))

            | e -> PV.tclZERO e
          end
      end

  | 3 -> (* Tlet *)
      begin
        match Run.run (env, sigma) (nth 1) with
        | Run.Val (sigma, _, t) ->
            PV.Unsafe.tclEVARS sigma <*>
            interp (Term.mkApp (nth 2,  [|t|]))
        | Run.Err (sigma, _, t) ->
            PV.Unsafe.tclEVARS sigma <*>
            PV.tclZERO (UserException (RO.nf_evar sigma t))
        | _ -> Exceptions.error_stuck ()
      end

  | 4 -> (* Tor *)
      let t1 = interp (nth 0) in
      let t2 = (fun x->
        match x with
        | (UserException e, _) -> interp (Term.mkApp (nth 1, [|e|]))
        | (e, _) -> PV.tclZERO e) in
      PV.tclOR t1 t2

  | 5 -> (* Traise *)
      PV.tclZERO (UserException (nth 0))

  (* | 6 -> (* Tmark_as_goal *)
     PV.Unsafe.mark_as_goal (nth 0)
  *)
  | _ -> Exceptions.error_stuck ()
