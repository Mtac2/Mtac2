open Constr
open Term
open Reductionops

let reduce_value = Tacred.compute

module Constr = struct
  exception Constr_not_found of string
  exception Constr_poly of string

  let mkConstr name = lazy (
    try Universes.constr_of_global
          (Nametab.global_of_path (Libnames.path_of_string name))
    with Not_found -> raise (Constr_not_found name)
       | Invalid_argument _ -> raise (Constr_poly name)
  )

  let mkUConstr name sigma env =
    try Evd.fresh_global env sigma
          (Nametab.global_of_path (Libnames.path_of_string name))
    with Not_found -> raise (Constr_not_found name)

  let isConstr = fun r c -> eq_constr (Lazy.force r) c

  let isUConstr r sigma env = fun c ->
    eq_constr_nounivs (snd (mkUConstr r sigma env)) c

  let eq_ind i1 i2 = Names.eq_ind (fst i1) (fst i2)

end

module ConstrBuilder = struct

  type t = string

  let from_string (s:string) : t = s

  let build s = Lazy.force (Constr.mkConstr s)
  let build_app s args = mkApp (Lazy.force (Constr.mkConstr s), args)

  let equal s = Constr.isConstr (Constr.mkConstr s)

  let from_coq s _ cterm =
    let (head, args) = decompose_appvect cterm in
    if equal s head then
      Some args
    else
      None
end

module UConstrBuilder = struct

  type t = string

  let from_string (s:string) : t = s

  let build_app s sigma env args =
    let (sigma, c) = Constr.mkUConstr s sigma env in
    (sigma, mkApp (c, args))

  let equal = Constr.isUConstr

  let from_coq s (env, sigma) cterm =
    let (head, args) = decompose_appvect cterm in
    if equal s sigma env head then
      Some args
    else
      None
end

module CoqOption = struct
  open ConstrBuilder

  let noneBuilder = from_string "Coq.Init.Datatypes.None"

  let mkNone ty = build_app noneBuilder [|ty|]

  let someBuilder = from_string "Coq.Init.Datatypes.Some"

  let mkSome ty t = build_app someBuilder [|ty; t|]

  exception NotAnOptionType
  let from_coq (env, sigma as ctx) cterm =
    match from_coq noneBuilder ctx cterm with
    | None ->
        begin
          match from_coq someBuilder ctx cterm with
          | None -> raise NotAnOptionType
          | Some arr -> Some arr.(1)
        end
    | Some _ -> None

  let to_coq ty oterm =
    match oterm with
    | None -> mkNone ty
    | Some t -> mkSome ty t

end

module CoqList = struct
  open UConstrBuilder
  let mkNil  = from_string "MetaCoq.Plist.pnil"
  let mkCons = from_string "MetaCoq.Plist.pcons"
  let mkType = from_string "MetaCoq.Plist.plist"

  let makeNil ty sigma env = build_app mkNil sigma env [| ty |]
  let makeCons t x xs sigma env = build_app mkCons sigma env [| t ; x ; xs |]
  let makeType ty sigma env = build_app mkType sigma env [|ty|]

  let isNil  = equal mkNil
  let isCons = equal mkCons

  exception Skip
  exception NotAList of constr
  (** given a list of terms and a convertion function fconv
      it creates a list of elements using the converstion function.
      if fconv raises Skip, that element is not included.
      if the list is ill-formed, an exception NotAList is raised. *)
  let from_coq_conv (env, sigma) (fconv : Term.constr -> 'a) cterm =
    let rec fcc cterm =
      let (constr, args) = decompose_appvect cterm in
      if isNil sigma env constr then [] else
      if not (isCons sigma env constr) then raise (NotAList cterm)
      else
        let tail = fcc args.(2) in
        try fconv args.(1) :: tail with Skip -> tail
    in
    fcc cterm

  let from_coq (env, sigma) =
    from_coq_conv (env, sigma) (fun x->x)

  let to_coq ty f l sigma env =
    List.fold_right (fun e (sigma, l) ->
      makeCons ty (f e) l sigma env) l (makeNil ty sigma env)

  let pto_coq ty f l sigma env =
    List.fold_right (fun e (sigma, l) ->
      let sigma, c = f e sigma in
      makeCons ty c l sigma env) l (makeNil ty sigma env)
end

module CoqEq = struct
  let mkEq = Constr.mkConstr "Coq.Init.Logic.eq"
  let mkEqRefl = Constr.mkConstr "Coq.Init.Logic.eq_refl"

  let mkAppEq a x y = mkApp(Lazy.force mkEq, [|a;x;y|])
  let mkAppEqRefl a x = mkApp(Lazy.force mkEqRefl, [|a;x|])
end

module CoqSigT = struct
  let mkExistT  = Constr.mkConstr "Coq.Init.Specif.existT"

  let mkAppExistT a p x px =
    mkApp (Lazy.force mkExistT, [|a; p; x; px|])
end


module CoqSig = struct
  let rec from_coq (env, sigma) constr =
    (* NOTE: Hightly unsafe *)
    let (_, args) = decompose_appvect (whd_all env sigma constr) in
    args.(1)
end

module CoqNat = struct
  let mkZero = Constr.mkConstr "Coq.Init.Datatypes.O"
  let mkSucc = Constr.mkConstr "Coq.Init.Datatypes.S"

  let isZero = Constr.isConstr mkZero
  let isSucc = Constr.isConstr mkSucc

  let rec to_coq = function
    | 0 -> Lazy.force mkZero
    | n -> Term.mkApp (Lazy.force mkSucc, [| to_coq (pred n) |])

  let from_coq (env, evd) c =
    let rec fc c =
      if isZero c then
        0
      else
        let (s, n) = destApp c in
        begin
          if isSucc s then
            1 + (fc (n.(0)))
          else
            CErrors.error "Not a nat"
        end
    in
    let c' = reduce_value env evd c in
    fc c'

end

module CoqPositive = struct
  let xI = Constr.mkConstr "Coq.Numbers.BinNums.xI"
  let xO = Constr.mkConstr "Coq.Numbers.BinNums.xO"
  let xH = Constr.mkConstr "Coq.Numbers.BinNums.xH"

  let isH = Constr.isConstr xH
  let isI = Constr.isConstr xI
  let isO = Constr.isConstr xO

  let from_coq (env, evd) c =
    let rec fc i c =
      if isH c then
        1
      else
        let (s, n) = destApp c in
        begin
          if isI s then
            (fc (i+1) (n.(0)))*2 + 1
          else if isO s then
            (fc (i+1) (n.(0)))*2
          else
            CErrors.error "Not a positive"
        end
    in
    let c' = reduce_value env evd c in
    fc 0 c'

  let rec to_coq n =
    if n = 1 then
      Lazy.force xH
    else if n mod 2 = 0 then
      mkApp(Lazy.force xO, [|to_coq (n / 2)|])
    else
      mkApp(Lazy.force xI, [|to_coq ((n-1)/2)|])

end

module CoqN = struct
  let tN = Constr.mkConstr "Coq.Numbers.BinNums.N"
  let h0 = Constr.mkConstr "Coq.Numbers.BinNums.N0"
  let hP = Constr.mkConstr "Coq.Numbers.BinNums.Npos"

  let is0 = Constr.isConstr h0
  let isP = Constr.isConstr hP

  let from_coq (env, evd) c =
    let rec fc c =
      if is0 c then
        0
      else
        let (s, n) = destApp c in
        begin
          if isP s then
            CoqPositive.from_coq (env, evd) (n.(0))
          else
            CErrors.error "Not a positive"
        end
    in
    let c' = reduce_value env evd c in
    fc c'

  let to_coq n =
    if n = 0 then
      Lazy.force h0
    else
      mkApp(Lazy.force hP, [|CoqPositive.to_coq n|])
end

module CoqBool = struct

  let trueB = ConstrBuilder.from_string "Coq.Init.Datatypes.true"
  let falseB = ConstrBuilder.from_string "Coq.Init.Datatypes.false"

  let isTrue = ConstrBuilder.equal trueB

  let mkTrue = ConstrBuilder.build trueB
  let mkFalse = ConstrBuilder.build falseB

  let to_coq b = if b then
      ConstrBuilder.build trueB
    else ConstrBuilder.build falseB

end

module CoqAscii = struct

  let asciiBuilder = ConstrBuilder.from_string "Coq.Strings.Ascii.Ascii"

  let from_coq _ c =
    let (h, args) = decompose_appvect c in
    let rec from_bits n =
      if n >= Array.length args then 0
      else (if CoqBool.isTrue args.(n) then 1 else 0) lsl n + from_bits (n+1)
    in
    let n = from_bits 0 in
    String.make 1 (Char.chr n)

  let to_coq c =
    let c = int_of_char c in
    let a = Array.init 8 (fun i->(c lsr i) mod 2 = 1) in
    let a = Array.map CoqBool.to_coq a in
    ConstrBuilder.build_app asciiBuilder a

end

module CoqString = struct

  let emptyB = ConstrBuilder.from_string "Coq.Strings.String.EmptyString"
  let stringB = ConstrBuilder.from_string "Coq.Strings.String.String"

  let isEmpty = ConstrBuilder.equal emptyB
  let isString = ConstrBuilder.equal stringB

  let from_coq (env, sigma as ctx) s =
    let rec fc s =
      let (h, args) = decompose_appvect s in
      if isEmpty h then ""
      else if isString h then
        CoqAscii.from_coq ctx args.(0) ^ fc args.(1)
      else
        CErrors.error "Not a string"
    in
    fc (reduce_value env sigma s)

  let rec to_coq s =
    if String.length s = 0 then
      ConstrBuilder.build emptyB
    else
      ConstrBuilder.build_app stringB [|
        CoqAscii.to_coq s.[0];
        to_coq (String.sub s 1 (String.length s -1))|]

end

module CoqUnit = struct
  let mkTT = Constr.mkConstr "Coq.Init.Datatypes.tt"
end

module MCTactics = struct
  let reduceGoal = "metaCoqReduceGoal"
  let runTac = "MetaCoq.Tactics.run_tac"
  let tactic = "MetaCoq.Tactics.tactic"

  let mkConstr s =
    let open Nametab in let open Libnames in
    try Universes.constr_of_global (locate (qualid_of_string s))
    with _ -> raise (Constr.Constr_not_found s)

  let mkUConstr s sigma env =
    let open Nametab in let open Libnames in
    try Evd.fresh_global env sigma (locate (qualid_of_string s))
    with _ -> raise (Constr.Constr_not_found s)

  let mkReduceGoal = lazy (mkConstr reduceGoal)

  let mkRunTac = mkUConstr runTac

  let mkTactic = mkUConstr tactic

end

module CoqPair = struct
  let pairBuilder = ConstrBuilder.from_string "Coq.Init.Datatypes.pair"

  let mkPair tya tyb a b = ConstrBuilder.build_app pairBuilder [|tya;tyb;a;b|]
end
