open Prelude

(* Errors *)
exception Rel_gen_bug of string


(* Pre-checking structures *)
type pprem_r =
  | PPremInd of {
    pind : Names.lident;
    pargs : Constrexpr.constr_expr list
  }
  | PPremPred of {
    ppred : Constrexpr.constr_expr
  }
and pprem = pprem_r CAst.t

type parity_decl_r = {
  prel_name : Names.lident ; parity : Constrexpr.constr_expr list
}
and parity_decl = parity_decl_r CAst.t

type prule_decl_r = {
  prule_name : Names.lident ;
  pvars : (Names.lident * Constrexpr.constr_expr) list ; (* TODO : allow Constrexpr option *)
  pconclusion : Names.lident * Constrexpr.constr_expr list ;
  ppremises : pprem list
}
and prule_decl = prule_decl_r CAst.t

type rel_psignature_r = { parity_decls : parity_decl list ; prule_decls : prule_decl list }

and rel_psignature = rel_psignature_r CAst.t

(* Post-checking structures *)
type prem =
  | PremInd of {
    ind : Names.variable;
    args : Evd.econstr list
  }
  | PremPred of {
    pred : Evd.econstr
  }

type arity_decl = {
  rel_name : Names.variable ; arity : Evd.econstr list
}

type rule_decl = {
  rule_name : Names.variable ;
  vars : (Names.lident * Evd.econstr) list ;
  conclusion : Names.variable * Evd.econstr list ;
  premises : prem list
}

type rel_signature = { arity_decls : arity_decl list ; rule_decls : rule_decl list }


(* Checking functions *)

type state = {
  env : Environ.env ;
  sigma : Evd.evar_map ;
  signature : rel_signature
}


let check_fresh (st : state) (name : Names.lident) : unit =
  (* Check that we did not define a relation with that name *)
  let b_rel = List.mem name.v (List.map (fun d -> d.rel_name) st.signature.arity_decls) in
  let b_rule = List.mem name.v (List.map (fun d -> d.rule_name) st.signature.rule_decls) in
  (* TODO : check in the global environment *)
  if b_rel || b_rule then
    Log.error ?loc:name.loc "%s is already declared." (Names.Id.to_string name.v)

let check_arity_decl (st : state) (d : parity_decl) : state =
  (* Check that the name is fresh *)
  check_fresh st d.v.prel_name;
  (* Typecheck all arities *)
  let sigma, arity = List.monad_map (fun t env sigma -> Constrintern.interp_constr_evars env sigma t) d.v.parity st.env st.sigma in
  let ad : arity_decl = {
    rel_name = d.v.prel_name.v ;
    arity = arity
  } in
  {
    env = st.env ;
    sigma = sigma ;
    signature = {
      arity_decls = ad::st.signature.arity_decls;
      rule_decls = st.signature.rule_decls
    }
  }

let check_var_decls (name, t : Names.lident * Constrexpr.constr_expr) (st : state) : Evd.econstr * state =
  let sigma, t = Constrintern.interp_constr_evars st.env st.sigma t in
  let annot = Context.make_annot name.v Sorts.Relevant in
  let decl = Context.Named.Declaration.LocalAssum (annot, EConstr.to_constr sigma t) in
  let env' = Environ.push_named decl st.env in
  t, {
    env = env' ;
    sigma = sigma ;
    signature = st.signature
  }

let rec mk_var_decls (l : (Names.lident * Constrexpr.constr_expr) list) (st : state) : Evd.econstr list * state = match l with
| [] -> [], st
| h::t ->
  let ht, hst = check_var_decls h st in
  let tt, tst = mk_var_decls t hst in
  ht::tt, tst

let check_app (ind : Names.lident) (args : Constrexpr.constr_expr list) (st : state) : Names.variable * Evd.econstr list * state =
  (* Check that the name of the inductive is something we defined *)
  let ad = List.find_opt (fun (d : arity_decl) -> d.rel_name = ind.v) st.signature.arity_decls in
  match ad with
  | None -> Log.error ?loc:ind.loc "%s is not a declared relation." (Names.Id.to_string ind.v)
  | Some _ -> ();
  let ad = Option.get ad in
  (* Check the arguments *)
  let sigma, args = List.monad_map (fun t env sigma -> Constrintern.interp_constr_evars env sigma t) args st.env st.sigma in
  (* Check that the arguments are indeed the right ones *)
  let arg_types = List.map (Retyping.get_type_of st.env sigma) args in
  (if arg_types <> ad.arity then Log.error ?loc:ind.loc "Bad arguments" ());
  ind.v, args, {
    env = st.env ;
    sigma = sigma ;
    signature = st.signature
  }

let check_rule_decls (st : state) (d : prule_decl) : state =
  (* Check that the name is fresh *)
  check_fresh st d.v.prule_name;
  (* Check the variables and get the new environment *)
  let names = List.map fst d.v.pvars in
  (* let pvars = List.rev (d.v.pvars) in *)
  let vars, st' = mk_var_decls d.v.pvars st in
  (* Check the conclusion *)
  let ccl, args_ccl, st' = check_app (fst d.v.pconclusion) (snd d.v.pconclusion) st' in
  (* Check all premises *)
  (* We do not work with the monad [m] anymore, but with [state]. We redefine the monad map for this here *)
  let rec state_monad_map (f : 'a -> state -> 'b * state) (l : 'a list) (st : state) : 'b list * state = match l with
  | [] -> [], st
  | h::t ->
    let h', st' = f h st in
    let t', st' = state_monad_map f t st' in
    (h'::t'), st'
  in
  let premises, st' = state_monad_map (fun (p : pprem) st -> match p.v with
    | PPremPred p ->
      let sigma, p = Constrintern.interp_constr_evars st.env st.sigma p.ppred in
      PremPred {pred = p}, {
        env = st.env ;
        sigma = sigma ;
        signature = st.signature
      }
    | PPremInd p ->
      let ind, args, st = check_app p.pind p.pargs st in
      PremInd {ind = ind ; args = args}, st
  ) (d.v.ppremises) st' in
  let r : rule_decl = {
    rule_name = d.v.prule_name.v ;
    vars = List.combine names vars ;
    conclusion = (ccl, args_ccl) ;
    premises = premises
  } in
  {
    env = st.env ; (* We do NOT change the global environment! *)
    sigma = st'.sigma ; (* But we want to add the evars *)
    signature = {
      arity_decls = st.signature.arity_decls ;
      rule_decls = r::st.signature.rule_decls
    }
  }

let check_psig (s : rel_psignature) : state m = fun env sigma ->
  (* Initial signature *)
  let st : state = {
    env = env ;
    sigma = sigma ;
    signature = {
      arity_decls = [] ; rule_decls = []
    }
  } in
  (* Check arities *)
  let st = List.fold_left check_arity_decl st (s.v.parity_decls) in
  (* Check rules *)
  let st = List.fold_left check_rule_decls st (s.v.prule_decls) in
  (* Get back the right order of declarations *)
  let st = {
    env = st.env ;
    sigma = st.sigma ;
    signature = {
      arity_decls = List.rev st.signature.arity_decls ;
      rule_decls = st.signature.rule_decls
    }
  } in
  sigma, st

(* Building the inductive *)

let rec make_arity (l : Evd.econstr list) = match l with
| [] -> EConstr.mkProp
| h::t -> EConstr.mkArrowR h (make_arity t)

let make_rule_type (name_assoc : (Names.variable * int) list) (d : rule_decl) : Names.variable list -> Evd.econstr m = fun inds ->
  (* Auxiliary function that builds the arrow type *)
  let rec mk_arrow (l : prem list) : Evd.econstr = match l with
  | [] -> (* Build the conclusion *)
      let concl = List.nth inds (List.assoc (fst d.conclusion) name_assoc) in
      let args = Array.of_list (snd d.conclusion) in
      EConstr.mkApp (EConstr.mkVar concl, args)
  | PremPred p :: t ->
    EConstr.mkArrowR p.pred (mk_arrow t)
  | PremInd p :: t ->
    let ind = List.nth inds (List.assoc p.ind name_assoc) in
    let args = Array.of_list p.args in
    EConstr.mkArrowR (EConstr.mkApp (EConstr.mkVar ind, args)) (mk_arrow t)
  in
  let rec mk_prod (l : (Names.lident * Evd.econstr) list) = match l with
  | [] -> mk_arrow d.premises
  | (x, t)::l ->
    let x_annot = Context.make_annot x.v EConstr.ERelevance.relevant in
    EConstr.mkNamedProd (Evd.from_env (Global.env ())) x_annot t (mk_prod l)
  in ret (mk_prod d.vars)

let rec sort_by_rel (assoc : (Names.variable * int) list) (a : 'a list array) (f : rule_decl -> 'a) (l : rule_decl list) : unit = match l with
| [] -> ()
| h::t ->
  let i = List.assoc (fst h.conclusion) assoc in
  Array.set a i ((f h) :: a.(i));
  sort_by_rel assoc a f t

let build_inductive (st : state) : Names.MutInd.t =
  let signature = st.signature in
  (* Build all relation names *)
  let rel_names = List.map (fun d -> d.rel_name) signature.arity_decls in
  (* Build all relation arities *)
  let rel_arities = List.map (fun d -> make_arity d.arity) signature.arity_decls in

  (* Rules *)
  let rel_names_assoc = List.mapi (fun i n -> n, i) rel_names in
  let rule_names_arr : Names.variable list array = Array.make (List.length rel_names) [] in
  let rule_types_arr : (Names.variable list -> Evd.econstr m) list array = Array.make (List.length rel_names) [] in

  sort_by_rel rel_names_assoc rule_types_arr (make_rule_type rel_names_assoc) (signature.rule_decls);
  sort_by_rel rel_names_assoc rule_names_arr (fun (d : rule_decl) -> d.rule_name) (signature.rule_decls);

  let rule_names = Array.to_list rule_names_arr in
  let rule_types = Array.to_list rule_types_arr in

  let mname = monad_run @@ declare_mut_ind rel_names rel_arities rule_names rule_types in
  mname

(* Main function *)
let main (s : rel_psignature) : unit =
  (* Check the signature *)
  let st = monad_run @@ check_psig s in
  (* Build the inductive *)
  let _ = build_inductive st in
  ()