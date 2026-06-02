open Prelude

(* Errors *)
exception Rel_gen_bug of string

(* Pre-checking structures *)
type pprem_r =
  | PPremInd of {
    pind : (* Name of the inductive we call *)
      Names.lident;
    pargs : (* Arguments of the inductive we call *)
      Constrexpr.constr_expr list ;
    pextension : (* Context extension *)
      Constrexpr.constr_expr list option ;
  }
  | PPremPred of {
    ppred : (* Predicate *)
      Constrexpr.constr_expr
  }
and pprem = pprem_r CAst.t

type parity_decl_r = {
  prel_name : (* Name of the relation we build *)
    Names.lident ;
  pdecl : (* Type of declarations stored in contexts *)
    Constrexpr.constr_expr ;
  parity : (* Arity of the relation we build *)
    Constrexpr.constr_expr list ;
  pctx_name : (* Name of contexts for the relation we build *)
    Names.lident ;
}
and parity_decl = parity_decl_r CAst.t

type prule_decl_r = {
  prule_name : (* Name of the rule we declare *)
    Names.lident ;
  pvars : (* Variables by which we abstract, of the form [(x : t)] *)
    (Names.lident * Constrexpr.constr_expr) list ;
    (* TODO : allow Constrexpr option *)
  pconclusion : (* Conclusion of the rule, as a name of an inductive with arguments *)
    Names.lident * Constrexpr.constr_expr list ;
  ppremises : (* List of premises of the rule *)
    pprem list
}
and prule_decl = prule_decl_r CAst.t

type rel_psignature_r = {
  parity_decls : (* All arities *)
    parity_decl list ;
  prule_decls : (* All rules *)
    prule_decl list
}
and rel_psignature = rel_psignature_r CAst.t

(* Post-checking structures ; the structure is similar to the one above *)
type prem =
  | PremInd of {
    ind : Names.variable;
    args : Evd.econstr list;
    extension : Evd.econstr option ;
  }
  | PremPred of {
    pred : Evd.econstr
  }

type arity_decl = {
  rel_name : Names.variable ;
  decl : Evd.econstr ;
  arity : Evd.econstr list ;
  ctx_name : Names.variable ;
}

type rule_decl = {
  rule_name : Names.variable ;
  decl : Evd.econstr ;
  vars : (Names.lident * Evd.econstr) list ;
  conclusion : Names.variable * Evd.econstr list ;
  premises : prem list ;
  ctx_name : Names.variable ;
}

type rel_signature = { arity_decls : arity_decl list ; rule_decls : rule_decl list }


(* Checking functions *)

type state = {
  env : (* Current environment *)
    Environ.env ;
  sigma : (* Current evar map *)
    Evd.evar_map ;
  signature : (* Current signature *)
    rel_signature
}

(* We defne a monad_map for the monad ['a -> state -> 'a * state] *)
let rec state_monad_map (f : 'a -> state -> 'b * state) (l : 'a list) (st : state) : 'b list * state = match l with
| [] -> [], st
| h::t ->
  let h', st' = f h st in
  let t', st' = state_monad_map f t st' in
  (h'::t'), st'


(* Check that a variable is fresh in a state ; TODO : also check in the environment *)
let check_fresh (st : state) (name : Names.lident) : unit =
  (* Check that we did not define a relation with that name *)
  let b_rel = List.mem name.v (List.map (fun d -> d.rel_name) st.signature.arity_decls) in
  let b_rule = List.mem name.v (List.map (fun d -> d.rule_name) st.signature.rule_decls) in
  (* TODO : check in the global environment *)
  if b_rel || b_rule then
    Log.error ?loc:name.loc "%s is already declared." (Names.Id.to_string name.v)

(* Check an arity declaration and add its checked version to the current signature *)
let check_arity_decl (st : state) (d : parity_decl) : state =
  (* Check that the name is fresh *)
  check_fresh st d.v.prel_name;
  (* Typecheck the type of declarations *)
  let sigma, tdecl = Constrintern.interp_constr_evars st.env st.sigma  d.v.pdecl in
  (* Typecheck all arities *)
  let sigma, arity = List.monad_map (fun t env sigma -> Constrintern.interp_constr_evars env sigma t) d.v.parity st.env sigma in
  let ad : arity_decl = {
    rel_name = d.v.prel_name.v ;
    decl = tdecl ;
    arity = arity ;
    ctx_name = d.v.pctx_name.v
  } in
  {
    env = st.env ;
    sigma = sigma ;
    signature = {
      arity_decls = ad::st.signature.arity_decls;
      rule_decls = st.signature.rule_decls
    }
  }

(* Check variable declarations and add them to the current environment. Also returns the type of the variable *)
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

(* Apply the previous function on a list of variable declarations *)
let rec mk_var_decls (l : (Names.lident * Constrexpr.constr_expr) list) (st : state) : Evd.econstr list * state = match l with
| [] -> [], st
| h::t ->
  let ht, hst = check_var_decls h st in
  let tt, tst = mk_var_decls t hst in
  ht::tt, tst

(* Check something of the form [name arg1 ... argn], either a conclusion or a premise *)
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
  (* Add the list type *)
  (* let gr_list = Rocqlib.lib_ref "core.list.type" in *)
  (* let sigma, c_list = Evd.fresh_global st.env sigma gr_list in *)
  (if arg_types <> ad.arity then Log.error ?loc:ind.loc "Bad arguments" ());
  (* (if arg_types <> ((EConstr.mkApp (c_list, [|ad.decl|]))::ad.arity) then Log.error ?loc:ind.loc "Bad arguments" ()); *)
  ind.v, args, {
    env = st.env ;
    sigma = sigma ;
    signature = st.signature
  }

(* Check a rule declaration and adds it to the state *)
let check_rule_decls (st : state) (d : prule_decl) : state =
  (* Check that the name is fresh *)
  check_fresh st d.v.prule_name;
  (* Get the type of the declaration for the rule *)
  let ad = List.find_opt (fun (ad : arity_decl) -> ad.rel_name = (fst d.v.pconclusion).v) st.signature.arity_decls in
  match ad with
  | None -> Log.error ?loc:(fst (d.v.pconclusion)).loc "%s is not a declared relation." (Names.Id.to_string (fst d.v.pconclusion).v)
  | Some _ -> ();
  let ad = Option.get ad in
  let tdecl = ad.decl in

  (* Check the variables and get the new environment *)
  let names = List.map fst d.v.pvars in
  let vars, st' = mk_var_decls d.v.pvars st in

  (* Check the conclusion *)
  let ccl, args_ccl, st' = check_app (fst d.v.pconclusion) (snd d.v.pconclusion) st' in

  (* Check all premises *)
  let premises, st' = state_monad_map (fun (p : pprem) st -> match p.v with
    | PPremPred p ->
      (* We need to check [p] in an environment where the context is abstracted *)
      let gr_list = Rocqlib.lib_ref "core.list.type" in
      let sigma, c_list = Evd.fresh_global st'.env st'.sigma gr_list in
      let annot = Context.make_annot ad.ctx_name Sorts.Relevant in
      let decl = Context.Named.Declaration.LocalAssum (annot, EConstr.to_constr st'.sigma (EConstr.mkApp (c_list, [|ad.decl|]))) in
      let env' = Environ.push_named decl st.env in
      let sigma, p = Constrintern.interp_constr_evars env' st.sigma p.ppred in
      PremPred {pred = p}, {
        env = st.env ;
        sigma = sigma ;
        signature = st.signature
      }
    | PPremInd p_ind ->
      (* Check that the arguments are the right ones *)
      let ind, args, st = check_app p_ind.pind p_ind.pargs st in
      (* Check that the extension is the right one *)
      let sigma, ext = match p_ind.pextension with
      | None -> st.sigma, None
      | Some e ->
        (* Transform the list [e] into a Rocq list with all the checked elements of [e] *)
        let rec listify (l : Constrexpr.constr_expr list) (sigma : Evd.evar_map) : Evd.evar_map * Evd.econstr = match l with
        | [] ->
          let gr_nil = Rocqlib.lib_ref "sulfur.list.nil" in
          let sigma, c_nil = Evd.fresh_global st.env sigma gr_nil in
          sigma, EConstr.mkApp (c_nil, [|tdecl|])
        | h::t ->
          let sigma, h = Constrintern.interp_constr_evars st.env sigma h in
          let type_h = Retyping.get_type_of st.env sigma h in
          if type_h <> tdecl then Log.error ?loc:p.loc "Wrong extension type" ();
          let sigma, l = listify t sigma in
          let gr_cons = Rocqlib.lib_ref "sulfur.list.cons" in
          let sigma, c_cons = Evd.fresh_global st.env sigma gr_cons in
          sigma, EConstr.mkApp (c_cons, [|tdecl ; h ; l|])
        in let sigma, e = listify e st.sigma in
        sigma, Some e
      in
      PremInd {ind = ind ; args = args ; extension = ext}, st
  ) (d.v.ppremises) st' in
  let r : rule_decl = {
    rule_name = d.v.prule_name.v ;
    decl = tdecl ;
    vars = List.combine names vars ;
    conclusion = (ccl, args_ccl) ;
    premises = premises ;
    ctx_name = ad.ctx_name ;
  } in
  {
    env = st.env ; (* We do NOT change the global environment! *)
    sigma = st'.sigma ; (* But we want to add the evars *)
    signature = {
      arity_decls = st.signature.arity_decls ;
      rule_decls = r::st.signature.rule_decls
    }
  }

(* Check the whole signature *)
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

(* From the list [t1 ; ... ; tn], builds the term [t1 -> ... -> tn -> Prop] *)
let rec make_arity (l : Evd.econstr list) = match l with
| [] -> EConstr.mkProp
| h::t -> EConstr.mkArrowR h (make_arity t)

(* Creates the type of a rule, with the right format for [declare_mut_ind] *)
let make_rule_type (name_assoc : (Names.variable * int) list) (ctx_type : Evd.econstr) (app_type : Evd.econstr) (d : rule_decl) : Names.variable list -> Evd.econstr m = fun inds ->
  (* Auxiliary function that builds the arrow type *)
  let rec mk_arrow (l : prem list) : Evd.econstr = match l with
  | [] -> (* Build the conclusion *)
      (* Finds the element of the list [ind] that correspond to the name of the inductive in the conclusion *)
      let concl = List.nth inds (List.assoc (fst d.conclusion) name_assoc) in
      (* Add the context to the begining of the conclusion arguments *)
      let args = Array.of_list (
        (EConstr.mkVar d.ctx_name):: (snd d.conclusion)
      ) in
      EConstr.mkApp (EConstr.mkVar concl, args)
  | PremPred p :: t ->
    (* Predicate premises are kept as is *)
    EConstr.mkArrowR p.pred (mk_arrow t)
  | PremInd p :: t ->
    (* Finds the element of the list [ind] that correspond to the name of the inductive in the premise *)
    let ind = List.nth inds (List.assoc p.ind name_assoc) in
    (* Create the extended context and adds it to the arguments *)
    let new_ctx = match p.extension with
    | None -> EConstr.mkVar d.ctx_name
    | Some e ->
      EConstr.mkApp (app_type, [|d.decl ; e ; EConstr.mkVar d.ctx_name|])
    in
    let args = Array.of_list (new_ctx :: p.args) in
    EConstr.mkArrowR (EConstr.mkApp (EConstr.mkVar ind, args)) (mk_arrow t)
  in
  (* Auxiliary function that builds the product type by abstracting over the variables *)
  let rec mk_prod (l : (Names.lident * Evd.econstr) list) = match l with
  | [] -> mk_arrow d.premises
  | (x, t)::l ->
    let x_annot = Context.make_annot x.v EConstr.ERelevance.relevant in
    EConstr.mkNamedProd (Evd.from_env (Global.env ())) x_annot t (mk_prod l)
  in
  (* Add the abstracted context to the variables *)
  ret (mk_prod (
    (CAst.make d.ctx_name, ctx_type)::(d.vars)
  ))

(* For every [d : rule_decl] in [l], puts [f d] in the list at the place in [a] that corresponds to the conclusion of [d] *)
let rec sort_by_rel (assoc : (Names.variable * int) list) (a : 'a list array) (f : rule_decl -> 'a) (l : rule_decl list) : unit = match l with
| [] -> ()
| h::t ->
  let i = List.assoc (fst h.conclusion) assoc in
  Array.set a i ((f h) :: a.(i));
  sort_by_rel assoc a f t

(* Main function to build the inductive relation *)
let build_inductive (st : state) : Names.MutInd.t =
  let signature = st.signature in
  let sigma = st.sigma in let env = st.env in
  (* Build all relation names *)
  let rel_names = List.map (fun d -> d.rel_name) signature.arity_decls in
  (* Build all relation arities *)
  let gr_list = Rocqlib.lib_ref "core.list.type" in
  let sigma, c_list = Evd.fresh_global env sigma gr_list in
  let rel_arities = List.map (fun (d : arity_decl) ->
    let ctx_type = EConstr.mkApp (c_list, [|d.decl|]) in
    EConstr.mkArrowR ctx_type (make_arity d.arity)
  ) signature.arity_decls in

  (* Rules *)
  let rel_names_assoc = List.mapi (fun i n -> n, i) rel_names in
  let rule_names_arr : Names.variable list array = Array.make (List.length rel_names) [] in
  let rule_types_arr : (Names.variable list -> Evd.econstr m) list array = Array.make (List.length rel_names) [] in

  sort_by_rel rel_names_assoc rule_types_arr (fun (r : rule_decl) ->
    (* Type of lists *)
    let gr_app = Rocqlib.lib_ref "sulfur.list.app" in
    let sigma, c_app = Evd.fresh_global st.env sigma gr_app in
    make_rule_type rel_names_assoc (EConstr.mkApp (c_list, [|r.decl|])) c_app r
  ) (signature.rule_decls);
  sort_by_rel rel_names_assoc rule_names_arr (fun (d : rule_decl) -> d.rule_name) (signature.rule_decls);

  let rule_names = Array.to_list rule_names_arr in
  let rule_types = Array.to_list rule_types_arr in

  let mname = monad_run @@ declare_mut_ind rel_names rel_arities rule_names rule_types in
  mname

(* Main function *)
let main (s : rel_psignature) : unit =
  (* Check the signature *)
  let st = monad_run @@ check_psig s in
  Feedback.msg_info (Pp.str "Checking OK");
  (* Build the inductive *)
  let _ = build_inductive st in
  ()