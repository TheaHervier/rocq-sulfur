From Sulfur Require Import Prelude Sig Renamings.
From Sulfur Require Import ParamSyntax.
Module P := ParamSyntax.

Section WithSignature.
Context {sig : signature}.

  (** Notations for expressions with known kinds. *)
  #[local] Reserved Notation "'mterm'" (at level 0).
  #[local] Reserved Notation "'marg' ty" (at level 0, ty at level 0).
  #[local] Reserved Notation "'margs' tys" (at level 0, tys at level 0).

  (* Reuse the notations from [ParamSyntax.v] *)
  #[local] Notation "'term'" := (P.expr Kt) (at level 0).
  #[local] Notation "'arg' ty" := (P.expr (Ka ty)) (at level 0, ty at level 0).
  #[local] Notation "'args' tys" := (P.expr (Kal tys)) (at level 0, tys at level 0).

  Unset Elimination Schemes.

  (* Meta variables *)
  Record mvar := {
    (* Meta variables do not have binders, so we can use names easily. We use natural numbers for names *)
    name : nat;

    (* Local scope of a mvar, i.e. the number of terms that will be able to be substituted in this mvar *)
    lscope : nat
  }.
  (* NOTE : two meta variables with the same name but with different lscope are different meta variables. It is not problematic, but one need to keep that in mind when doing things *)


  (** Terms over an abstract signature.
      Terms are indexed by a kind.
      Terms are also intrinsically scoped *)
  Inductive mexpr : kind -> nat -> Type :=
  | (** Term variable. *)
    M_var scope : forall i, i < scope -> mterm scope
  | (** Non-variable expr constructor, applied to a list of arguments. *)
    M_ctor scope : forall c, margs (ctor_type c) scope -> mterm scope
  | (** Empty argument list. *)
    M_al_nil scope : margs [] scope
  | (** Non-empty argument list. *)
    M_al_cons scope {ty tys} : marg ty scope -> margs tys scope -> margs (ty :: tys) scope
  | (** Base argument (e.g. bool or string). *)
    M_abase scope : forall b, eval_base b -> marg (AT_base b) scope
  | (** Term argument. *)
    M_aterm scope : mterm scope -> marg AT_term scope
  | (** Bind a term in an argument. *)
    M_abind scope {ty} : marg ty (S scope) -> marg (AT_bind ty) scope
  | (**
    Meta variable applyed to a substitution
    A substitution should be finite if we want to preserve scopeness.
    The problem is that functions from integers are nice to use, and that substitutions in [ParamSyntax] are infinite.
    In order to not do complicated conversions, we use the following data :
      - A family [scopes] of scopes, such that [scopes i] is the scope of the [ith] term of the substitution
      - A proof saying that all [lscope k] first elements of the substitution are of scope [scope]
      - The substitutionn that is a function from natural numbers

    Note that because of this, equality is not decidable on [mterms], and equality is not even the relation we should be interested in.
    **)
    M_mvar scope (k : mvar) :
      (* For every index of the substitution, gives a scope *)
      forall scopes : nat -> nat,
      (forall i, i < lscope k -> scopes i = scope) ->
      (forall i, mterm (scopes i)) -> mterm scope

  where "'mterm'" := (mexpr Kt)
    and "'marg' ty" := (mexpr (Ka ty))
    and "'margs' tys" := (mexpr (Kal tys)).

  Set Elimination Schemes.
  Derive NoConfusion for mexpr.

  (** Better induction scheme for [mexpr] **)
  Section MExprInd.
    Context (P : forall k s, mexpr k s -> Prop).

    Context (H_var : forall s i (Hsi : i < s), P _ _ (M_var s i Hsi)).
    Context (H_ctor : forall s c al, P _ _ al -> P _ _ (M_ctor s c al)).
    Context (H_al_nil : forall s, P _ _ (M_al_nil s)).
    Context (H_al_cons : forall s ty tys (a : marg ty _) (al : margs tys _),
      P _ _ a -> P _ _ al -> P _ _ (M_al_cons s a al)).
    Context (H_abase : forall s b x, P _ _ (M_abase s b x)).
    Context (H_aterm : forall s t, P _ _ t -> P _ _ (M_aterm s t)).
    Context (H_abind : forall s ty (a : marg ty _), P _ _ a -> P _ _ (M_abind s a)).
    Context (H_mvar : forall s k I HI σ,
      (forall i, i < lscope k -> P _ _ (σ i)) ->
      P _ _ (M_mvar s k I HI σ)
    ).

    Fixpoint mexpr_ind k s (t : mexpr k s) {struct t} : P k s t.
    Proof.
    destruct t.
    - apply H_var.
    - apply H_ctor. apply mexpr_ind.
    - apply H_al_nil.
    - apply H_al_cons ; apply mexpr_ind.
    - apply H_abase.
    - apply H_aterm. apply mexpr_ind.
    - apply H_abind. apply mexpr_ind.
    - apply H_mvar. intros. apply mexpr_ind.
    Qed.

  End MExprInd.

  (** Substitution of meta variables **)
  Section MetaSubst.

    (**
      We currify [msubst]s in [mexpr] so that it is easier to use when proving things on [mexpr]. The tradeoff is that it is slightly heavier when defining a concrete syntax (which in any case, should not be done by hand).
      We describe a substitution of meta variable [msubst] with a record.
    *)
    Record msubst {k s} := {
      (**
        - k is the number of variables that will be substituted
        - s is the scope of the substitution
        When used, the type of the substitution is not important, only the objects matter
      **)
      scopes : nat -> nat;
      Hscopes :
        forall i : nat, i < k -> scopes i = s;
      ms :
        forall i : nat, mterm (scopes i)
    }.
    Arguments msubst : clear implicits.

    (* Identity substitution of [k] meta terms, scoped by [k]. *)
    #[refine] Definition msid (k : nat) : msubst k k := {|
      scopes := fun i => if i <? k then k else S i;
      ms := fun i => M_var _ i _
    |}.
    Proof.
      - (* All of the interesting terms are scoped by k *)
        intros. apply PeanoNat.Nat.ltb_lt in H. rewrite H. reflexivity.
      - (* All the terms (here, variables) are well scoped by [scopes] *)
        destruct (i <? k) eqn:Hi.
        apply PeanoNat.Nat.ltb_lt. assumption.
        lia.
    Defined.

    (* Add a term to a substitution *)
    #[refine] Definition mscons {k s : nat} (t : mterm s) (σ : msubst k s) : msubst (S k) s := {|
      scopes := fun i => match i with
      | 0 => s
      | S i => (σ.(scopes) i)
      end;

      ms := fun i => match i with
      | 0 => t
      | S i => σ.(ms) i
      end
    |}.
    Proof.
      intros.
      destruct i as [|i]. reflexivity.
      apply Hscopes. lia.
    Defined.

    (* Meta variable applied to no substitution (i.e. identity) *)
    #[refine] Definition scoped_mvar (name : nat) (s : nat) : mterm s :=
      M_mvar s {|name:=name;lscope:=s|} (msid s).(scopes) _ (msid s).(ms).
    Proof.
      intros. simpl in *. apply PeanoNat.Nat.ltb_lt in H. rewrite H. reflexivity.
    Defined.

    (* Meta variable where we substitute the first variable by [t] ; can be generalized *)
    #[refine] Definition one_subst (name : nat) (t : mterm 0) :=
      M_mvar 0 {|name:=name;lscope:= 1|} (mscons t (msid 0)).(scopes) _ (mscons t (msid 0)).(ms).
    Proof.
      destruct i. reflexivity. simpl. lia.
    Defined.
  End MetaSubst.

  (** Evaluation of an expression with meta variables into expressions without **)
  Section Evaluation.
    Definition menv := mvar -> P.expr Kt.
    Definition default_menv : menv := fun k => E_var (name k).

    Equations eval {s k} (m : menv) (t : mexpr k s) : P.expr k :=
    eval m (M_var _ i _) := E_var i ;
    eval m (M_ctor _ c al) := E_ctor c (eval m al) ;
    eval m (M_al_nil _) := E_al_nil ;
    eval m (M_al_cons _ a al) := E_al_cons (eval m a) (eval m al) ;
    eval m (M_abase _ b x) := E_abase b x ;
    eval m (M_aterm _ t) := E_aterm (eval m t) ;

    eval m (M_abind _ a) :=
      (* We don't shift anything ; it is dealt with when evaluating a meta variable *)
      E_abind (eval m a);
    eval m (M_mvar _ k _ _ σ) := substitute
      (fun i =>
        if i<?lscope k then
          eval m (σ i)
        else
          (* [- lscope k] shifts the indexes to take into account the substitution *)
          (* [+ s] takes into account the scope, "the number of lambdas we are under" *)
          E_var (i - lscope k + s)
      ) (m k).

    #[export] Instance eval_proper_inst {k s} :
      Proper (eq1 ==> eq ==> eq) (@eval s k).
    Proof.
      intros m m' Hm t' t Ht. subst.
      induction t in m, m', Hm |- *; simpl in *; intros.
      - reflexivity.
      - erewrite IHt. reflexivity. assumption.
      - reflexivity.
      - erewrite IHt1, IHt2. reflexivity. assumption. assumption.
      - reflexivity.
      - erewrite IHt. reflexivity. assumption.
      - f_equal. apply IHt. setoid_rewrite Hm. reflexivity.
      - rewrite Hm.
        apply substitute_proper. 2: reflexivity.
        intro i. destruct (i<?lscope k) eqn:Hi. 2: reflexivity.
        apply H. 2: assumption.
        apply PeanoNat.Nat.ltb_lt. assumption.
    Qed.

    Lemma eval_proper m m' :
      m =₁ m' -> forall {k s} (t : mexpr k s),
      eval m t = eval m' t.
    Proof.
      intros Hm k s t.
      rewrite Hm. reflexivity.
    Qed.
  End Evaluation.

  (** Definitions of contexts **)
  (* Functor of declarations that will be stored in contexts *)
  Class DeclF := declF : Type -> Type.
  Context `{InstDeclF : DeclF}
    `{HFmapDecl : FMap declF}
    `{Hdecl : !Eq1Functor declF}.
  Section Contexts.
    Definition mdecl (s : nat) := declF (mterm s).

    Inductive mctx (scope : nat) | : nat -> Type :=
    | mnil : mctx 0
    | mcons {n : nat}
      (d : mdecl (n+scope)) (Γ : mctx n) :
      mctx (S n).
    Arguments mnil {scope}.
    Arguments mcons {scope}.

    Definition ctx := list (declF term).

    Equations eval_ctx {s n} (m : menv) (Γ : mctx s n) : ctx :=
    eval_ctx m mnil := [] ;
    eval_ctx m (mcons d Γ) := (fmap declF (eval m) d)::(eval_ctx m Γ).

    (** Evaluation preserves length **)
    Lemma eval_length {s n} (Γ : mctx s n) :
      forall m, n = Datatypes.length (eval_ctx m Γ).
    Proof.
      induction Γ; intros; simpl. reflexivity. f_equal. apply IHΓ.
    Qed.

    Equations rename_ctx (ρ : ren) (Γ : ctx) : ctx :=
    rename_ctx ρ [] => [] ;
    rename_ctx ρ (d::Γ) =>
      fmap _ (rename (up_rens (Datatypes.length Γ) ρ)) d ::
      rename_ctx ρ Γ.

    (* TODO : should be moved in ParamSyntax *)
    Equations up_substs (k : nat) (σ : subst) : subst :=
    up_substs 0 σ := σ ;
    up_substs (S k) σ := up_subst (up_substs k σ).

    Lemma up_substs_lt (i k : nat) (σ : subst) :
      i < k -> up_substs k σ i = E_var i.
    Proof.
      intro. induction k in i, H |- *; simpl.
      - lia.
      - destruct i as [|i]. simpl. reflexivity.
        simpl. unfold srcomp, rshift. rewrite IHk. reflexivity. lia.
    Qed.

    Lemma up_substs_gt (i k : nat) (σ : subst) :
      i >= k -> up_substs k σ i = rename (fun i => i + k) (σ (i - k)).
    Proof.
      induction k in i |- *; intros; simpl.
      - transitivity (σ (i - 0)).
        assert (i = i - 0) by lia. rewrite H0 at 1. reflexivity.
        etransitivity. symmetry. apply ren_rid.
        apply rename_proper. 2: reflexivity. intro. unfold rid. lia.
      - destruct i as [|i]; simpl. lia.
        unfold srcomp, rshift. rewrite IHk. 2: lia.
        rewrite ren_ren. apply rename_proper. 2: reflexivity.
        unfold rcomp. intro. lia.
    Qed.

    Lemma up_substs_add n m σ :
      up_substs n (up_substs m σ) =₁ up_substs (n + m) σ.
    Proof.
      induction n; simpl. reflexivity.
      apply up_subst_proper. assumption.
    Qed.

    Equations subst_ctx (σ : subst) (Γ : ctx) : ctx :=
    subst_ctx σ [] => [] ;
    subst_ctx σ (d :: Γ) =>
      fmap _ (substitute (up_substs (Datatypes.length Γ) σ)) d ::
      subst_ctx σ Γ.

    (* Belonging to a context *)
    Reserved Notation "Γ ∋ n : d" (at level 70, n at level 50).
    Inductive inctx : ctx -> nat -> declF term -> Prop :=
    | in_head d Γ :
      (d::Γ) ∋ 0 : fmap _ (rename rshift) d
    | in_tail d d' Γ n :
      Γ ∋ n : d ->
      d'::Γ ∋ S n : fmap _ (rename rshift) d
    where "Γ ∋ n : A" := (inctx Γ n A).

    (* Allows to use existential variables easily *)
    Lemma conv_in_d Γ n d d' :
      Γ ∋ n : d ->
      d = d' ->
      Γ ∋ n : d'.
    Proof. intros; subst; assumption. Qed.
    Lemma conv_in_n Γ n m d :
      Γ ∋ n : d ->
      n = m ->
      Γ ∋ m : d.
    Proof. intros; subst; assumption. Qed.
  End Contexts.
  Arguments mnil {scope}.
  Arguments mcons {scope}.
  Notation "Γ ∋ n : d" := (inctx Γ n d) (at level 70, n at level 50).

  (** Definition of judgments **)
  Class JdgF := jdgF : Type -> Type.
  Context `{InstJdgF : JdgF}
  `{HFmapJdg : FMap jdgF}
  `{Hjdg : !Eq1Functor jdgF}.

  Class MakeJdg := make_jdg : forall X, declF X -> X -> jdgF X.
  Context `{InstMakeJdg : MakeJdg}
  `{NatMakeJdg : !NatFromProd make_jdg}.
  (* Theoretically, make_jdg is a natural transformation from (declF * Id) to jdgF *)
  Section Judgments.

    Definition mjdg (s : nat) := jdgF (mterm s).
    Definition jdg  := jdgF term.

    (** Evaluating and renaming a judgment is much more straightforward **)
    Definition eval_jdg {s} m : mjdg s -> jdg := fmap jdgF (eval m).
    Definition rename_jdg ρ : jdg -> jdg := fmap jdgF (rename ρ).
    Definition substitute_jdg σ : jdg -> jdg := fmap jdgF (substitute σ).
  End Judgments.

  (** Definition of a signature of rules **)
  Section RulesSignature.
    (* Contexts in premises must be closed, and judgments must be scoped by the context *)
    Variant premise :=
    | prem_pred (P : ctx -> menv -> Prop)
    | prem_ind {n} (Δ : mctx 0 n) (j : mjdg n).
    Derive NoConfusion for premise.

    (* The judgment of the conclusion must be closed *)
    Record rule := {
      param : Type; (* A rule is parametrized by a type, e.g. a rule for any natural number *)
      premises : param -> list premise;
      conclusion : param -> mjdg 0;
    }.

    Record jdg_sig := {
      rules : list rule
    }.
    (* Other solution, maybe more heavy to write:
      [rules : list {param : Type & param -> rule}]
      and remove [param] from [rule]
    *)
  End RulesSignature.
  Context {jsig : jdg_sig}.

  (** Derivation with the rules of the signature **)
  Section Derivation.
    Reserved Notation "Γ ⊢ j" (at level 70).
    Inductive proof : ctx -> jdg -> Prop :=
    (*
      We need a context, a rule and an instanciation of this rule, that will give the conclusion
    *)
    | step (m : menv) (Γ : ctx) (r : rule) (x : r.(param)) :
      (* The rule must be in the signature *)
      In r (jsig.(rules)) ->
      (* Satisfy all inductive premises *)
      (
        forall {n} (Δ : mctx 0 n) (j : mjdg n),
        In (prem_ind Δ j) (r.(premises) x) ->
        (eval_ctx m Δ ++ Γ) ⊢ eval_jdg m j
      ) ->
      (* Satisfy all predicate premise, depending on Γ and m *)
      (
        forall P, In (prem_pred P) (r.(premises) x) ->
        P Γ m
      ) ->
      Γ ⊢ eval_jdg m (r.(conclusion) x)
    | tvar (Γ : ctx) (n : nat) (d : declF term) :
      Γ ∋ n : d ->
      Γ ⊢ make_jdg term d (E_var n)
    where "Γ ⊢ j" := (proof Γ j).

    Lemma conv_proof_j Γ j j' :
      Γ ⊢ j ->
      j = j' ->
      Γ ⊢ j'.
    Proof. intros; subst; assumption. Qed.
    Lemma conv_proof_c Γ Γ' j :
      Γ ⊢ j ->
      Γ = Γ' ->
      Γ' ⊢ j.
    Proof. intros; subst; assumption. Qed.
  End Derivation.
  Notation "Γ ⊢ j" := (proof Γ j) (at level 70).

  (** Behaviour of renamings **)
  Section Renamings.
    (** Commutation between renaming and evaluation lemma **)
    Lemma scoped_rename_eval {k} (n : nat) (t : mexpr k n) :
      forall m ρ,
      rename (up_rens n ρ) (eval m t) =
      eval (fun k => rename (up_rens (lscope k) ρ) (m k)) t.
    Proof.
      intros.
      induction t in m, ρ |- *;
      simpl in *;
      rewrite ?IHt, ?IHt1, ?IHt2; try reflexivity.
      - f_equal.
        apply up_rens_lt. assumption.
      - rewrite ren_subst, subst_ren.
        unfold srcomp, rscomp. apply substitute_proper. 2: reflexivity.
        intro i. destruct (i <? lscope k) eqn:Hi.
        + rewrite up_rens_lt.
          (* rewrite PeanoNat.Nat.ltb_lt in Hi. *)
          2: apply PeanoNat.Nat.ltb_lt; assumption.
          rewrite Hi. apply PeanoNat.Nat.ltb_lt in Hi.
          erewrite <- HI. 2: apply Hi. rewrite H.
          reflexivity. assumption.
        + rewrite PeanoNat.Nat.ltb_ge in Hi.
          rewrite up_rens_gt. 2: lia.
          match goal with
          | |- _ = if ?b then _ else _ =>
            assert (_H : b = false);
            [idtac|rewrite _H]
          end.
          {apply PeanoNat.Nat.ltb_ge. lia. }
          simpl. f_equal.
          rewrite up_rens_gt. 2: lia.
          replace (i - lscope k + s - s) with (i - lscope k) by lia.
          lia.
    Qed.
    Corollary closed_rename_eval {k} (t : mexpr k 0) :
      forall m ρ,
      rename ρ (eval m t) =
      eval (fun k => rename (up_rens (lscope k) ρ) (m k)) t.
    Proof. apply (scoped_rename_eval 0). Qed.

    Lemma scoped_ctx_rename_eval {s n} (Γ : mctx s n) :
      forall m ρ,
      rename_ctx (up_rens s ρ) (eval_ctx m Γ) =
      eval_ctx (fun k => rename (up_rens (lscope k) ρ) (m k)) Γ.
    Proof.
      induction Γ; intros; simpl.
      - reflexivity.
      - rewrite IHΓ. f_equal.
        rewrite <- eval_length.
        rewrite func_comp.
        apply rew_eq1. intro t.
        rewrite <- scoped_rename_eval.
        apply rename_proper. 2: reflexivity.
        apply up_rens_add.
    Qed.

    Lemma scoped_jdg_rename_eval {s} (j : mjdg s) :
      forall m ρ,
      rename_jdg (up_rens s ρ) (eval_jdg m j) =
      eval_jdg (fun k => rename (up_rens (lscope k) ρ) (m k)) j.
    Proof.
      intros m ρ. unfold rename_jdg, eval_jdg.
      rewrite func_comp. apply rew_eq1.
      intro t. apply scoped_rename_eval.
    Qed.
    Corollary closed_jdg_rename_eval (j : mjdg 0) :
      forall m ρ,
      rename_jdg ρ (eval_jdg m j) =
      eval_jdg (fun k => rename (up_rens (lscope k) ρ) (m k)) j.
    Proof. apply (@scoped_jdg_rename_eval 0). Qed.

    (** Typing of a renaming **)
    Reserved Notation "Δ ⊢r ρ : Γ" (at level 70, ρ at level 50).
    Inductive rtyping : ctx -> ren -> ctx -> Prop :=
    | rtyping_empty Δ ρ :
      Δ ⊢r ρ : []
    | rtyping_cons Δ ρ Γ d :
      Δ ⊢r rcomp rshift ρ : Γ ->
      Δ ∋ (ρ 0) : fmap _ (rename (rcomp rshift ρ)) d ->
      Δ ⊢r ρ : d::Γ
    where "Δ ⊢r ρ : Γ " := (rtyping Δ ρ Γ).
    Lemma conv_rtyping Δ ρ ρ' Γ :
      Δ ⊢r ρ : Γ ->
      ρ = ρ' ->
      Δ ⊢r ρ' : Γ.
    Proof. intros; subst; assumption. Qed.

    (* Hypothesis to add to signatures for them to preserve renaming *)
    Class RenJSig := {
      prem_ren :
      forall (r : rule) x P,
      In r (jsig.(rules)) ->
      In (prem_pred P) (r.(premises) x) ->
      forall Γ ρ Δ m,
      Δ ⊢r ρ : Γ ->
      P Γ m ->
      P Δ (fun k => rename (up_rens (lscope k) ρ) (m k))
    }.

    (** Renaming lemmas **)
    #[export] Instance rtyping_proper :
      Proper (eq ==> eq1 ==> eq ==> Basics.impl) rtyping.
    Proof.
      intros Δ' Δ HΔ ρ ρ' Hρ Γ' Γ HΓ H; subst.
      induction H in ρ', Hρ |- *; intros; constructor.
      - apply IHrtyping. apply congr_rcomp. reflexivity. assumption.
      - rewrite <- Hρ. eapply conv_in_d. apply H0.
        apply rew_eq1. intro t.
        apply rename_proper. 2: reflexivity.
        unfold rcomp, rshift. intro. apply Hρ.
    Qed.
    Lemma conv_rtype_r Δ ρ ρ' Γ :
      Δ ⊢r ρ : Γ ->
      ρ =₁ ρ' ->
      Δ ⊢r ρ' : Γ.
    Proof. intros Hρ Heq. rewrite <- Heq. assumption. Qed.

    Lemma rename_in Δ Γ ρ n d :
      Γ ∋ n : d ->
      Δ ⊢r ρ : Γ ->
      Δ ∋ ρ n : fmap _ (rename ρ) d.
    Proof.
      intros HΓ Hρ. induction HΓ in Δ, ρ, Hρ |- *; intros;
      inversion Hρ; subst.
      - rewrite func_comp.
        eapply conv_in_d. apply H4.
        apply rew_eq1. intro t. rewrite ren_ren. reflexivity.
      - eapply conv_in_d. eapply conv_in_n.
        apply IHHΓ. apply H3. reflexivity.
        rewrite func_comp. apply rew_eq1.
        intro t. rewrite ren_ren. reflexivity.
    Qed.

    Lemma rtyping_comp Γ Δ Θ ρ ρ' :
      Δ ⊢r ρ : Γ ->
      Θ ⊢r ρ' : Δ ->
      Θ ⊢r rcomp ρ ρ' : Γ.
    Proof.
      intros Hρ Hρ'. induction Hρ in Θ, ρ', Hρ' |- *; intros; constructor.
      - eapply rtyping_proper. reflexivity. 2: reflexivity.
        apply rcomp_assoc. apply IHHρ. assumption.
      - eapply conv_in_d.
        unfold rcomp. eapply rename_in. apply H. assumption.
        rewrite func_comp. apply rew_eq1. intro.
        rewrite ren_ren, rcomp_assoc. reflexivity.
    Qed.

    Lemma weaken_rtyping Γ ρ Δ A :
      Δ ⊢r ρ : Γ ->
      A::Δ ⊢r rcomp ρ S : Γ.
    Proof.
      intros Hρ. induction Hρ in A |- *; intros; constructor.
      - apply IHHρ.
      - eapply conv_in_d. constructor. apply H.
        rewrite func_comp. apply rew_eq1. intro.
        rewrite ren_ren, rcomp_assoc. reflexivity.
    Qed.

    Lemma up_rtyping Γ ρ Δ d :
      Δ ⊢r ρ : Γ ->
      fmap _ (rename ρ) d::Δ ⊢r up_ren ρ : d::Γ.
    Proof.
      intros Hρ. constructor.
      - apply weaken_rtyping. assumption.
      - eapply conv_in_d. simpl. constructor.
        rewrite func_comp. apply rew_eq1. intro.
        rewrite ren_ren. reflexivity.
    Qed.

    Corollary up_rtyping_n Γ ρ Δ Θ :
      Δ ⊢r ρ : Γ ->
      (rename_ctx ρ Θ) ++ Δ ⊢r up_rens (Datatypes.length Θ) ρ : Θ ++ Γ.
    Proof.
      induction Θ in Γ, ρ, Δ |- *; intros; simpl in *.
      - assumption.
      - apply up_rtyping.
        apply IHΘ. assumption.
    Qed.

    Lemma id_rtyping Γ :
      Γ ⊢r rid : Γ.
    Proof.
      induction Γ. constructor.
      replace a with (fmap _ (rename rid) a) at 1.
      2: {
        rewrite <- func_id. apply rew_eq1. intro. apply ren_rid.
      }
      rewrite <- up_ren_rid at 2. apply up_rtyping. assumption.
    Qed.

    Context {HRenSig : RenJSig}.

    Theorem preserve_renaming Γ j Δ ρ :
      Γ ⊢ j ->
      Δ ⊢r ρ : Γ ->
      Δ ⊢ rename_jdg ρ j.
    Proof.
      intros Hj Hρ.
      induction Hj in Δ, ρ, Hρ |- *.
      (* Case of an inductive/predicate premise *)
      - (* We apply rule [r x] *)
        eapply conv_proof_j.
        unshelve econstructor.
        shelve.
        exact r. exact x.
        assumption.
        3: {symmetry. apply closed_jdg_rename_eval. }
        + (* Inductive premise *)
          intros.
          rewrite <- scoped_jdg_rename_eval. eapply H1. apply H3.
          rewrite <- scoped_ctx_rename_eval. simpl.
          eapply conv_rtyping.
          eapply up_rtyping_n. assumption.
          f_equal. symmetry. apply eval_length.
        + (* Predicate premise *)
          intros.
          eapply HRenSig. apply H. apply H3. apply Hρ. apply H2. apply H3.
      (* Case of a variable *)
      - unfold rename_jdg.
        rewrite naturality_prod.
        constructor. eapply rename_in. apply H. assumption.
    Qed.

    Corollary weaken_typing Γ j A :
      Γ ⊢ j ->
      A::Γ ⊢ rename_jdg rshift j.
    Proof.
      intro.
      eapply preserve_renaming. apply H.
      apply weaken_rtyping. apply id_rtyping.
    Qed.
  End Renamings.
  Notation "Δ ⊢r ρ : Γ" := (rtyping Δ ρ Γ) (at level 70, ρ at level 50).

  (** Behaviour of substitutions **)
  Section Substitutions.

    (* TODO : should be in ParamSyntax *)

    Definition ren_to_subst (r : ren) : subst := fun i =>
    E_var (r i).

    Lemma ren_is_subst {k} r (t : expr k) :
      rename r t = substitute (ren_to_subst r) t.
    Proof.
      induction t in r |- *; simpl;
      rewrite ?IHt, ?IHt1, ?IHt2; try reflexivity.
      f_equal. apply substitute_proper. 2: reflexivity.
      intros [|n]; simpl. reflexivity.
      unfold rcomp, rshift, srcomp. simpl. reflexivity.
    Qed.
    Corollary ren_is_subst_jdg r (t : jdg) :
      rename_jdg r t = substitute_jdg (ren_to_subst r) t.
    Proof.
      unfold rename_jdg, substitute_jdg. apply rew_eq1.
      intro. apply ren_is_subst.
    Qed.
    Lemma ren_to_subst_up_rens n ρ :
      ren_to_subst (up_rens n ρ) =₁ up_substs n (ren_to_subst ρ).
    Proof.
      intro k. induction n in ρ, k |- *; simpl.
      reflexivity.
      unfold ren_to_subst, up_subst. unfold scons. destruct k as [|k].
      simpl. reflexivity. simpl. unfold srcomp, rshift.
      etransitivity. 2: {eapply rename_proper. reflexivity. apply IHn. }
      reflexivity.
    Qed.

    (** Commutation lemmas between substitution and evaluation **)
    Lemma scoped_substitute_eval {k} (n : nat) (t : mexpr k n) :
      forall m σ,
      substitute (up_substs n σ) (eval m t) =
      eval (fun k => substitute (up_substs (lscope k) σ) (m k)) t.
    Proof.
      intros.
      induction t in m, σ |- *;
      simpl in *;
      rewrite ?IHt, ?IHt1, ?IHt2; try reflexivity.
      - apply up_substs_lt. assumption.
      - rewrite 2!subst_subst.
        unfold scomp. apply substitute_proper. 2: reflexivity.
        intro i. destruct (i <? lscope k) eqn:Hi.
        + rewrite up_substs_lt.
          (* rewrite PeanoNat.Nat.ltb_lt in Hi. *)
          2: apply PeanoNat.Nat.ltb_lt; assumption. simpl.
          rewrite Hi. apply PeanoNat.Nat.ltb_lt in Hi.
          erewrite <- HI. 2: apply Hi. apply H. assumption.
        + rewrite PeanoNat.Nat.ltb_ge in Hi.
          simpl.
          rewrite !up_substs_gt. 2: lia. 2: lia.
          rewrite subst_ren.
          rewrite ren_is_subst.
          apply substitute_proper.
          2: {f_equal. lia. }
          intro j. unfold rscomp.
          match goal with
          | |- _ = if ?b then _ else _ =>
            assert (_H : b = false);
            [idtac|rewrite _H]
          end.
          {apply PeanoNat.Nat.ltb_ge. lia. }
          unfold ren_to_subst.
          f_equal. lia.
    Qed.
    Corollary closed_substitute_eval {k} (t : mexpr k 0) :
      forall m σ,
      substitute σ (eval m t) =
      eval (fun k => substitute (up_substs (lscope k) σ) (m k)) t.
    Proof. apply (@scoped_substitute_eval _ 0). Qed.

    Lemma scoped_ctx_substitute_eval {s n} (Γ : mctx s n) :
      forall m σ,
      subst_ctx (up_substs s σ) (eval_ctx m Γ) =
      eval_ctx (fun k => substitute (up_substs (lscope k) σ) (m k)) Γ.
    Proof.
      induction Γ; intros; simpl.
      - reflexivity.
      - rewrite IHΓ. f_equal.
        rewrite <- eval_length.
        rewrite func_comp. apply rew_eq1. intro.
        rewrite <- scoped_substitute_eval.
        apply substitute_proper. 2: reflexivity.
        apply up_substs_add.
    Qed.

    Lemma scoped_jdg_substitute_eval {s} (j : mjdg s) :
      forall m σ,
      substitute_jdg (up_substs s σ) (eval_jdg m j) =
      eval_jdg (fun k => substitute (up_substs (lscope k) σ) (m k)) j.
    Proof.
      intros m ρ. unfold substitute_jdg, eval_jdg.
      rewrite func_comp. apply rew_eq1.
      intro t.
      apply scoped_substitute_eval.
    Qed.
    Corollary closed_jdg_substitute_eval (j : mjdg 0) :
      forall m σ,
      substitute_jdg σ (eval_jdg m j) =
      eval_jdg (fun k => substitute (up_substs (lscope k) σ) (m k)) j.
    Proof. apply (@scoped_jdg_substitute_eval 0). Qed.

    (** Typing of a substitution **)
    Reserved Notation "Δ ⊢s σ : Γ" (at level 70, σ at level 50).
    Inductive styping : ctx -> subst -> ctx -> Prop :=
    | styping_empty Δ σ :
      Δ ⊢s σ : []
    | styping_cons Δ σ Γ d :
      Δ ⊢s rscomp rshift σ : Γ ->
      Δ ⊢ make_jdg term
        (fmap _ (substitute (rscomp rshift σ)) d)
        (σ 0) ->
      Δ ⊢s σ : d::Γ
    where "Δ ⊢s σ : Γ " := (styping Δ σ Γ).
    Lemma conv_styping Δ ρ ρ' Γ :
      Δ ⊢s ρ : Γ ->
      ρ = ρ' ->
      Δ ⊢s ρ' : Γ.
    Proof. intros; subst; assumption. Qed.

    Lemma ren_to_subst_typing Γ ρ Δ :
      Δ ⊢r ρ : Γ ->
      Δ ⊢s ren_to_subst ρ : Γ.
    Proof.
      intro Hρ. induction Hρ.
      - constructor.
      - constructor. apply IHHρ.
        constructor. eapply conv_in_d. apply H.
        apply rew_eq1. intro i. apply ren_is_subst.
    Qed.

    (* Hypothesis to add to signatures for them to preserve substitution *)
    Class SubstJSig := {
      prem_subst :
        forall (r : rule) x P,
        In r (jsig.(rules)) ->
        In (prem_pred P) (r.(premises) x) ->
        forall Γ σ Δ m,
        Δ ⊢s σ : Γ ->
        P Γ m ->
        P Δ (fun k => substitute (up_substs (lscope k) σ) (m k));

      prem_pred_ext :
        forall (r : rule) x P,
        In r (jsig.(rules)) ->
        In (prem_pred P) (r.(premises) x) ->
        forall Γ m m',
        P Γ m -> m =₁ m' -> P Γ m'
    }.
    (* Preserving substitutions implies preserving renamings via ren_is_subst *)
    #[export] Instance SubstJdg_RenJdg : SubstJSig -> RenJSig.
    Proof.
      intro H.
      constructor. intros.
      eapply prem_pred_ext. apply H0. apply H1.
      2: {intro k. rewrite <- ren_is_subst. reflexivity. }
      eapply prem_pred_ext. apply H0. apply H1.
      2: {intro k. rewrite ren_to_subst_up_rens. reflexivity. }
      eapply prem_subst. apply H0. apply H1. 2: apply H3.
      apply ren_to_subst_typing. assumption.
    Qed.

    (** Substitution lemmas **)
    #[export] Instance styping_proper :
      Proper (eq ==> eq1 ==> eq ==> Basics.impl) styping.
    Proof.
      intros Δ' Δ HΔ σ σ' Hσ Γ' Γ HΓ H; subst.
      induction H in σ', Hσ |- *; intros; constructor.
      - apply IHstyping. apply rscomp_proper. reflexivity. assumption.
      - eapply conv_proof_j.
        apply H0.
        f_equal. 2: apply Hσ.
        apply rew_eq1. intros. intro. apply substitute_proper. 2: reflexivity.
        intro. apply Hσ.
    Qed.
    Lemma conv_stype_s Δ σ σ' Γ :
      Δ ⊢s σ : Γ ->
      σ =₁ σ' ->
      Δ ⊢s σ' : Γ.
    Proof.
      intros Hσ Heq. rewrite <- Heq. assumption.
    Qed.

    Lemma substitute_in Δ Γ σ n d :
      Γ ∋ n : d ->
      Δ ⊢s σ : Γ ->
      Δ ⊢ make_jdg term (fmap _ (substitute σ) d) (σ n).
    Proof.
      intros HΓ Hσ. induction HΓ in Δ, σ, Hσ |- *; intros;
      inversion Hσ; subst.
      - rewrite func_comp.
        eapply conv_proof_j. apply H4.
        f_equal. apply rew_eq1. intro.
        rewrite subst_ren. reflexivity.
      - eapply conv_proof_j. apply IHHΓ. apply H3.
        rewrite func_comp. f_equal. apply rew_eq1. intro.
        rewrite subst_ren. reflexivity.
    Qed.

    Context `{HSubstSig : SubstJSig}.

    Lemma weaken_styping Γ σ Δ d :
      Δ ⊢s σ : Γ ->
      d::Δ ⊢s srcomp σ S : Γ.
    Proof.
      intros Hσ. induction Hσ in d |- *; intros; constructor.
      - apply IHHσ.
      - eapply conv_proof_j. apply weaken_typing. apply H.
        simpl. unfold rename_jdg.
        rewrite naturality_prod. f_equal.
        rewrite func_comp. apply rew_eq1. intro.
        rewrite ren_subst. reflexivity.
    Qed.

    Lemma up_styping Γ σ Δ d :
      Δ ⊢s σ : Γ ->
      (fmap _ (substitute σ) d)::Δ ⊢s up_subst σ : d::Γ.
    Proof.
      intros Hσ. constructor.
      - apply weaken_styping. assumption.
      - simpl. constructor.
        eapply conv_in_d. constructor.
        rewrite func_comp.
        apply rew_eq1. intro. rewrite ren_subst. reflexivity.
    Qed.

    Corollary up_styping_n Γ σ Δ Θ :
      Δ ⊢s σ : Γ ->
      (subst_ctx σ Θ) ++ Δ ⊢s up_substs (Datatypes.length Θ) σ : Θ ++ Γ.
    Proof.
      induction Θ in Γ, σ, Δ |- *; intros; simpl in *.
      - assumption.
      - apply up_styping.
        apply IHΘ. assumption.
    Qed.

    Lemma id_styping Γ :
      Γ ⊢s sid : Γ.
    Proof.
      induction Γ. constructor.
      replace a with (fmap _ (substitute sid) a) at 1.
      2: {
        rewrite <- func_id. apply rew_eq1. intro. apply subst_sid.
      }
      rewrite <- up_subst_sid at 2. apply up_styping. assumption.
    Qed.

    Theorem preserve_subst Γ j Δ σ :
      Γ ⊢ j ->
      Δ ⊢s σ : Γ ->
      Δ ⊢ substitute_jdg σ j.
    Proof.
      intros Hj Hσ.
      induction Hj in Δ, σ, Hσ |- *.
      (* Case of an inductive/predicate premise *)
      - (* We apply rule [r x] *)
        eapply conv_proof_j.
        unshelve econstructor.
        shelve.
        exact r. exact x.
        assumption.
        3: {symmetry. apply closed_jdg_substitute_eval. }
        + (* Inductive premise *)
          intros.
          rewrite <- scoped_jdg_substitute_eval. eapply H1. apply H3.
          rewrite <- scoped_ctx_substitute_eval. simpl.
          eapply conv_styping.
          eapply up_styping_n. assumption.
          f_equal. symmetry. apply eval_length.
        + (* Predicate premise *)
          intros.
          eapply HSubstSig. apply H. apply H3. apply Hσ. apply H2. assumption.
      (* Case of a variable *)
      - unfold substitute_jdg.
        rewrite naturality_prod.
        eapply substitute_in. apply H. assumption.
    Qed.
  End Substitutions.
  Notation "Δ ⊢s σ : Γ" := (styping Δ σ Γ) (at level 70, σ at level 50).
End WithSignature.
Arguments mnil {_ _ _}.
Arguments mcons {_ _ _ _}.
Notation "Γ ∋ n : A" := (inctx Γ n A) (at level 70, n at level 50).
Notation "Γ ⊢ j" := (proof Γ j) (at level 70).

Notation "Δ ⊢r ρ : Γ" := (rtyping Δ ρ Γ) (at level 70, ρ at level 50).
Notation "Δ ⊢s σ : Γ" := (styping Δ σ Γ) (at level 70, σ at level 50).

Arguments SubstJSig {_ _ _ _ _ _} (_).
Arguments RenJSig {_ _ _ _} (_).


(** Example module of conversion in lambda pi **)
Module LPConv.
  (* Syntax of lambda pi *)
  Variant EBase := Nat.
  Variant CLamPi := CType | CApp | CLam | CPi.

  Derive NoConfusion for EBase.
  Derive EqDec for EBase.
  Derive NoConfusion for CLamPi.
  Derive EqDec for CLamPi.

  #[refine] Definition sig_lp : signature := {|
    base := EBase;
    eval_base := fun _ => nat;
    ctor := CLamPi;
    ctor_type := fun c => match c with
    | CType => [AT_base Nat]
    | CApp => [AT_term; AT_term]
    | CLam => [AT_bind AT_term]
    | CPi => [AT_term; AT_bind AT_term]
    end
  |}.
  Defined.

  Notation "'mterm'" := (@mexpr sig_lp Kt) (at level 0).
  Notation "'marg' ty" := (@mexpr sig_lp (Ka ty)) (at level 0, ty at level 0).
  Notation "'margs' tys" := (@mexpr sig_lp (Kal tys)) (at level 0, tys at level 0).

  (* λΠ constructors, written in a more accessible way *)
  Definition T {s} (n : nat) : mterm s :=
  @M_ctor sig_lp s CType (
    M_al_cons s (@M_abase sig_lp s Nat n) (M_al_nil s)
  ).

  Definition lambda {s} (t : mterm (S s)) : mterm s :=
  @M_ctor sig_lp s CLam (
    M_al_cons s (M_abind s (M_aterm  (S s) t)) (M_al_nil s)
  ).

  Definition Pi {s} (A : mterm s) (B : mterm (S s)) : mterm s :=
  @M_ctor sig_lp s CPi (
    M_al_cons s (M_aterm s A) (M_al_cons s (M_abind s (M_aterm (S s) B)) (M_al_nil s))
  ).

  Definition App {s} (f u : mterm s) : mterm s :=
  @M_ctor sig_lp s CApp (
    M_al_cons s (M_aterm s f) (M_al_cons s (M_aterm s u) (M_al_nil s))
  ).

  Definition Var {s} (n : nat) (Hs : n < s) : mterm s :=
  @M_var sig_lp s n Hs.

  Definition elambda (t : P.expr Kt) : P.expr Kt :=
  @E_ctor sig_lp CLam (
    E_al_cons (E_abind (E_aterm t)) E_al_nil
  ).
  Definition ePi (A B : P.expr Kt) : P.expr Kt :=
  @E_ctor sig_lp CPi (
    E_al_cons (E_aterm A) (E_al_cons (E_abind (E_aterm B)) E_al_nil)
  ).
  Definition eT (u : nat) : P.expr Kt :=
  @E_ctor sig_lp CType (
    E_al_cons (@E_abase sig_lp Nat u) E_al_nil
  ).
  Definition eApp (f u : P.expr Kt) : P.expr Kt :=
  @E_ctor sig_lp CApp (
    E_al_cons (E_aterm f) (E_al_cons (E_aterm u) E_al_nil)
  ).

  (* Typing rules *)
  Instance LpConvDecl : DeclF := fun X => unit.
  Instance LpConvJdg : JdgF := fun X => (X*X)%type.
  Instance LpConvMakeJdg : MakeJdg := fun X _ t => (t, t).
  (* Might be better to move it? *)
  Instance LpConvNatMakeJdg : NatFromProd LpConvMakeJdg.
  Proof.
    constructor. reflexivity.
  Qed.

  Definition conv_nA := 0.
  Definition conv_nB := 1.
  Definition conv_nA' := 2.
  Definition conv_nB' := 3.
  Definition conv_nt := 4.
  Definition conv_nu := 5.
  Definition conv_nv := 6.
  Definition conv_nt' := 7.
  Definition conv_nu' := 8.
  Definition conv_nv' := 9.
  Definition conv_nb := 10.
  Definition conv_nb' := 11.

  Notation A := (scoped_mvar conv_nA 0).
  Notation B := (scoped_mvar conv_nB 1).
  Notation A' := (scoped_mvar conv_nA' 0).
  Notation B' := (scoped_mvar conv_nB' 1).
  Notation t := (scoped_mvar conv_nt 0).
  Notation u := (scoped_mvar conv_nu 0).
  Notation v := (scoped_mvar conv_nv 0).
  Notation t' := (scoped_mvar conv_nt' 0).
  Notation u' := (scoped_mvar conv_nu' 0).
  Notation v' := (scoped_mvar conv_nv' 0).
  Notation b := (scoped_mvar conv_nb 1).
  Notation b' := (scoped_mvar conv_nb' 1).
  Notation bu := (one_subst conv_nb u).

  Lemma b_bu_mvar :
    forall k k' scopes scopes' Hs Hs' s s',
    b = @M_mvar sig_lp 1 k scopes Hs s ->
    bu = @M_mvar sig_lp 0 k' scopes' Hs' s' ->
    k = k'.
  Proof.
    intros.
    inversion H. inversion H0. reflexivity.
  Qed.

  Definition tRefl : rule(sig:=sig_lp) :=
  {|
    premises := fun (_ : unit) => [];
    conclusion := fun _ => (t, t)
  |}.
  Definition tSym : rule(sig:=sig_lp) :=
  {|
    premises := fun (_ : unit) => [
      prem_ind
        mnil
        (t, u)
    ];
    conclusion := fun _ => (u, t)
  |}.
  Definition tTrans : rule(sig:=sig_lp) :=
  {|
    premises := fun (_ : unit) => [
      prem_ind
        mnil
        (t, u) ;
      prem_ind
        mnil
        (u, v)
    ];
    conclusion := fun _ => (t, v)
  |}.

  Definition tCongrApp : rule :=
  {|
    premises := fun (_ : unit) => [
      prem_ind
        mnil
        (t, t');
      prem_ind
        mnil
        (u, u')
    ];
    conclusion := fun _ =>
      (App t u, App t' u')
  |}.
  Definition tCongrPi : rule :=
  {|
    premises := fun (_ : unit) => [
      prem_ind
        mnil
        (A, A');
      prem_ind
        (mcons tt mnil)
        (B, B')
    ];
    conclusion := fun _ =>
      (Pi A B, Pi A' B')
  |}.
  Definition tCongrLam : rule :=
  {|
    premises := fun (_ : unit) => [
      prem_ind
        (mcons tt mnil)
        (b, b')
    ];
    conclusion := fun _ =>
      (lambda b, lambda b')
  |}.

  Definition tBeta : rule :=
  {|
    premises := fun (_ : unit) => [];
    conclusion := fun _ =>
    (App (lambda b) u, bu)
  |}.

  Definition typ_conv_lampi : jdg_sig := {|rules:=[
    tRefl; tSym; tTrans;
    tCongrApp; tCongrPi; tCongrLam;
    tBeta
  ]|}.

  (* Overwrite notations for lambda pi *)
  #[warnings="-notation-overridden"]
  Notation "Γ ∋ n : A" := (@inctx sig_lp Γ n A) (at level 70, n at level 50).
  #[warnings="-notation-overridden"]
  Notation "Γ ⊢ j" := (proof(jsig:=typ_conv_lampi) Γ j) (at level 70).
  #[warnings="-notation-overridden"]
  Notation "Δ ⊢r ρ : Γ" := (rtyping(sig:=sig_lp) Δ ρ Γ) (at level 70, ρ at level 50).
  #[warnings="-notation-overridden"]
  Notation "Δ ⊢s σ : Γ" := (styping(jsig:=typ_conv_lampi) Δ σ Γ) (at level 70, σ at level 50).

  Notation "Γ ⊢ A ≡ B" := (proof(jsig:=typ_conv_lampi) Γ (A, B)) (at level 70).

  (* Sanity check *)
  Lemma beta_rev n :
    [] ⊢ eT n ≡ eApp (elambda (E_var 0)) (eT n).
  Proof.
    (* Apply symmetry *)
    pose (msym := fun k =>
      if (k.(name)=?conv_nu) then (eT n)
      else if (k.(name)=?conv_nt) then (eApp (elambda (E_var 0)) (eT n))
      else (default_menv k)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact msym. exact tSym. exact tt. repeat (try (left; reflexivity); right).
    3: reflexivity.
    2: {intros. destruct_n H. inversion H. }
    intros. destruct_n H.
    noconf H. simpl.
    (* Just to avoid unfolding too much *)
    unshelve eapply conv_proof_j.
    exact ((eApp (elambda (E_var 0)) (eT n)), eT n).
    2: reflexivity.

    (* Apply beta *)
    pose (mbeta := fun k =>
      if (k.(name)=?conv_nb) then (E_var 0)
      else if (k.(name)=?conv_nu) then (eT n)
      else (default_menv k)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact mbeta. exact tBeta. exact tt. repeat (try (left; reflexivity); right).
    3: reflexivity.
    all: intros; destruct_n H.
  Qed.

  Instance LPConvSubst : SubstJSig typ_conv_lampi.
  constructor; intros; destruct_n H; subst; destruct_n H0; inversion H0.
  Qed.
End LPConv.

(** Example module of typing of Lambda Pi **)
Module LambdaPi.
  #[warnings="-notation-overridden"] Import LPConv.

  Definition nA := 0.
  Definition nB := 1.
  Definition nf := 2.
  Definition nu := 3.
  Definition nb := 4.
  Definition nt := 5.
  Definition nA' := 6.

  Notation A := (scoped_mvar nA 0).
  Notation B := (scoped_mvar nB 1).
  Notation f := (scoped_mvar nf 0).
  Notation u := (scoped_mvar nu 0).
  Notation Bu := (one_subst nB u).
  Notation b := (scoped_mvar nb 1).
  Notation t := (scoped_mvar nt 0).
  Notation A' := (scoped_mvar nA' 0).

  Lemma B_Bu_mvar :
    forall k k' scopes scopes' Hs Hs' s s',
    B = @M_mvar sig_lp 1 k scopes Hs s ->
    Bu = @M_mvar sig_lp 0 k' scopes' Hs' s' ->
    k = k'.
  Proof.
    intros.
    inversion H. inversion H0. reflexivity.
  Qed.

  (* Typing rules *)
  Instance LpDecl : DeclF := fun X => X.
  Instance LpJdg : JdgF := fun X => (X*X)%type.
  Instance LpMakeJdg : MakeJdg := fun X A t => (t, A).
  Instance LpNatMakeJdg : NatFromProd LpMakeJdg.
  Proof.
    constructor. reflexivity.
  Qed.


  Definition tType : rule :=
  {|
    premises := fun _ => [];
    conclusion := fun n => (T(s:=0) n, T (S n))
  |}.

  Definition tPi : rule :=
  {|
    premises := fun '(n, m) =>
    [
      prem_ind
        mnil
        (A, T n) ;
      prem_ind
        (mcons(n:=0) A mnil)
        (B, T m)
    ] ;
    conclusion := fun '(n, m) =>
      (Pi A B, T (Nat.max n m))
  |}.

  Definition tApp : rule :=
  {|
    premises := fun (_ : unit) =>
    [
      prem_ind
        mnil
        (f, Pi A B);
      prem_ind
        mnil
        (u, A)
    ];
    conclusion := fun _ =>
      (App f u, Bu)
  |}.

  Definition tLam : rule :=
  {|
    premises := fun (_ : unit) =>
    [
      prem_ind
        (mcons(n:=0) A mnil)
        (b, B)
    ];
    conclusion := fun _ =>
      (lambda b, Pi A B)
  |}.

  Definition tConv : rule :=
  {|
    premises := fun (_ : unit) =>
    [
      prem_ind
        (mnil)
        (t, A);
      prem_pred (fun Γ m =>
        map (fun _ => tt) Γ ⊢ eval m A ≡ eval m A'
      )
    ];
    conclusion := fun _ =>
      (t, A')
  |}.

  Definition typ_lampi : jdg_sig := {|rules:=[
    tType; tPi; tApp; tLam; tConv
  ]|}.

  (* Overwrite notations for lambda pi *)
  #[warnings="-notation-overridden"]
  Notation "Γ ∋ n : A" := (@inctx sig_lp Γ n A) (at level 70, n at level 50).
  #[warnings="-notation-overridden"]
  Notation "Γ ⊢ j" := (proof(jsig:=typ_lampi) Γ j) (at level 70).
  #[warnings="-notation-overridden"]
  Notation "Δ ⊢r ρ : Γ" := (rtyping(sig:=sig_lp) Δ ρ Γ) (at level 70, ρ at level 50).
  #[warnings="-notation-overridden"]
  Notation "Δ ⊢s σ : Γ" := (styping(jsig:=typ_lampi) Δ σ Γ) (at level 70, σ at level 50).

  Lemma typed_implies_refl Γ t A :
    Γ ⊢ (t, A) ->
    map (fun _ => tt) Γ ⊢ t ≡ t.
  Proof.
    (* I don't really want to do this proof with this formalism, and it is not very interresting for the example *)
  Admitted.

  Lemma styping_to_unit Δ σ Γ :
    Δ ⊢s σ : Γ ->
    styping(jsig:=typ_conv_lampi) (map (fun _ => tt) Δ) σ (map (fun _ => tt) Γ).
  Proof.
    intro Hσ. induction Hσ.
    - constructor.
    - simpl. constructor.
      + apply IHHσ.
      + unfold make_jdg, LpConvMakeJdg in *.
        unfold LpMakeJdg in H. unfold fmap, FMapId in H.
        eapply typed_implies_refl. apply H.
  Qed.

  (* Something that appears multiple times, so making it a lemma might be useful *)
  Lemma subst_minus_plus_zero :
    (fun i => E_var(sig:=sig_lp) (i - 0 + 0)) =₁ sid.
  Proof. intro; unfold sid; f_equal; lia. Qed.

  (* This is the instance we need if we want to use preservation by substitution and renaming *)
  Instance LPTypSubst : SubstJSig typ_lampi.
    constructor; intros; destruct_n H; subst; try destruct x; destruct_n H0; try inversion H0.
    - subst.
      (* Clean the context a bit *)
      clear H0.
      remember (m {|name := nA ; lscope := 0|}) as tA.
      remember (m {|name := nA' ; lscope := 0|}) as tA'.
      simpl.
      rewrite subst_minus_plus_zero. rewrite 2!subst_sid.
      rewrite subst_minus_plus_zero in H2. rewrite 2!subst_sid in H2.
      (* Apply the theorem of preservation by substitution because the predicate is an inductive predicate that we already built *)
      pose (preserve_subst(jsig:=typ_conv_lampi)).
      specialize (p (map (fun _ => tt) Γ) (tA, tA')).
      unfold substitute_jdg, fmap, FMapProd, fmap, FMapId in p.
      apply p. apply H2.
      (* We still need to show that :
        [map (fun _ => tt) Γ ⊢s map (fun _ => tt) Δ]
        This is a part that is more specific to the theory we built. We even [Admitted] a part of this proof that is not comfortable in this framework, and that is not useful for the example
      *)
      apply styping_to_unit. assumption.
    - rewrite subst_minus_plus_zero. subst.
      rewrite subst_minus_plus_zero in H1. rewrite 2!subst_sid in *.
      rewrite <- H2. assumption.
  Qed.

  Lemma proof_type_id n :
    [] ⊢ (elambda (E_var 0), ePi (eT n) (eT n)).
  Proof.
    pose (m := fun k =>
      if (k.(name)=?nb) then (E_var 0)
      else if (k.(name)=?nA) then (eT n)
      else if (k.(name)=?nB) then (eT n)
      else (default_menv k)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact m. exact tLam. exact tt. repeat (try (left; reflexivity); right).
    3: reflexivity.
    2: intros; destruct_n H; noconf H.
    intros. destruct_n H.
    noconf H. simpl.
    eapply conv_proof_j. apply tvar. constructor.
    reflexivity.
  Qed.

  Lemma proof_type_id_app n :
    [eT n] ⊢ (eApp (elambda (E_var 0)) (E_var 0), (eT n)).
  Proof.
    pose (m := fun k =>
      if (k.(name)=?nf) then (elambda (E_var 0))
      else if (k.(name)=?nu) then (E_var 0)
      else if (k.(name)=?nA) then (eT n)
      else if (k.(name)=?nB) then (eT n)
      else (default_menv k)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact m. apply tApp. exact tt. repeat (try (left; reflexivity); right).
    3: reflexivity.
    2: intros; destruct_n H; noconf H.
    intros. destruct_n H.
    - noconf H.
      simpl. unfold fmap, FMapId. simpl.
      eapply conv_proof_j.
      eapply (weaken_typing (jsig:=typ_lampi)).
      apply (proof_type_id n).
      reflexivity.
      Unshelve.
      + (* Typeclass Eq1Functor for declarations *)
        typeclasses eauto.
      + (* Typeclass Eq1Functor for judgments *)
        Fail typeclasses eauto.
        apply Eq1FProd; typeclasses eauto.
      + (* Typeclass NatFromProd for make_jdg *)
        typeclasses eauto.
      + (* Typeclass RenJSig to use preservation by renaming *)
        Fail typeclasses eauto.
        apply SubstJdg_RenJdg; typeclasses eauto.
    - noconf H. simpl.
      eapply conv_proof_j. apply tvar. constructor.
      reflexivity.
  Qed.

  Lemma proof_typee_id_app_lam n :
    [eT n] ⊢ (eApp (elambda (E_var 0)) (E_var 0),
    eApp (elambda (E_var 0)) (eT n)).
  Proof.
    (* Use the conversion rule *)
    pose (m := fun k =>
      if (k.(name)=?nt) then (eApp (elambda (E_var 0)) (E_var 0))
      else if (k.(name)=?nA) then (eT n)
      else if (k.(name)=?nA') then (eApp (elambda (E_var 0)) (eT n))
      else (default_menv k)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact m. apply tConv. exact tt. repeat (try (left; reflexivity); right).
    3: reflexivity.
    - (* Inductive premise *)
      intros. destruct_n H; noconf H.
      unfold eval_jdg, eval_ctx, fmap, FMapProd, fmap, FMapId. simpl. apply proof_type_id_app.
    - (* Predicate premise *)
      intros. destruct_n H; noconf H.
      rewrite subst_minus_plus_zero. rewrite 2! subst_sid.
      simpl. unfold m. simpl.
      (* Need to weaken the context *)
      eapply conv_proof_j.
      eapply (weaken_typing(jsig:=typ_conv_lampi)).
      (* Here Rocq finds the typeclasses *)
      apply (beta_rev n). reflexivity.
  Qed.

End LambdaPi.

(** Example section of simply typed lambda calculus **)
Module SimplLambda.
  Variant EBase :=.
  Variant CLamCalc := CApp | CLam.

  Derive NoConfusion for EBase.
  Derive EqDec for EBase.
  Derive NoConfusion for CLamCalc.
  Derive EqDec for CLamCalc.

  #[refine] Definition sig_lam : signature := {|
    base := EBase;
    eval_base := fun _ => False;
    ctor := CLamCalc;
    ctor_type := fun c => match c with
    | CApp => [AT_term; AT_term]
    | CLam => [AT_bind AT_term]
    end
  |}.
  Defined.

  #[local] Notation "'mterm'" := (@mexpr sig_lam Kt) (at level 0).
  #[local] Notation "'marg' ty" := (@mexpr sig_lam (Ka ty)) (at level 0, ty at level 0).
  #[local] Notation "'margs' tys" := (@mexpr sig_lam (Kal tys)) (at level 0, tys at level 0).

  (* λΠ constructors, written in a more accessible way *)
  Definition lambda {s} (t : mterm (S s)) : mterm s :=
  @M_ctor sig_lam s CLam (
    M_al_cons s (M_abind s (M_aterm  (S s) t)) (M_al_nil s)
  ).

  Definition App {s} (f u : mterm s) : mterm s :=
  @M_ctor sig_lam s CApp (
    M_al_cons s (M_aterm s f) (M_al_cons s (M_aterm s u) (M_al_nil s))
  ).

  Definition Var {s} (n : nat) (Hs : n < s) : mterm s :=
  @M_var sig_lam s n Hs.

  Inductive sType :=
  | sIota
  | sArrow (A B : sType).

  (* Definition of contexts and judments *)
  Instance LamDecl : DeclF := fun _ => sType.
  Instance LamJdg : JdgF := fun X => (X*sType)%type.
  Instance LamMakeJdg : MakeJdg := fun X A t => (t, A).
  Instance LamMakeJdgNat : NatFromProd LamMakeJdg.
  Proof.
    constructor. reflexivity.
  Qed.

  (* Typing rules *)
  Definition nf := 0.
  Definition nu := 1.
  Definition nb := 2.

  Notation f := (scoped_mvar nf 0).
  Notation u := (scoped_mvar nu 0).
  Notation b := (scoped_mvar nb 1).

  Definition tApp : rule :=
  {|
    premises := fun '(A, B) =>
    [
      prem_ind
        mnil
        (f, sArrow A B);
      prem_ind
        mnil
        (u, A)
    ];
    conclusion := fun '(_, B) =>
      (App f u, B)
  |}.

  Definition tLam : rule :=
  {|
    premises := fun '(A, B) =>
    [
      prem_ind
        (mcons(n:=0) A mnil)
        (b, B)
    ];
    conclusion := fun '(A, B) =>
      (lambda b, sArrow A B)
  |}.

  Definition typ_lam : jdg_sig := {|rules:=[tApp; tLam]|}.

  (* Overwrite notations for lambda pi *)
  #[warnings="-notation-overridden"]
  Notation "Γ ∋ n : A" := (@inctx sig_lam Γ n A) (at level 70, n at level 50).
  #[warnings="-notation-overridden"]
  Notation "Γ ⊢ j" := (proof(jsig:=typ_lam) Γ j) (at level 70).
  #[warnings="-notation-overridden"]
  Notation "Δ ⊢r ρ : Γ" := (rtyping(sig:=sig_lam) Δ ρ Γ) (at level 70, ρ at level 50).
  #[warnings="-notation-overridden"]
  Notation "Δ ⊢s σ : Γ" := (styping(jsig:=typ_lam) Δ σ Γ) (at level 70, σ at level 50).

  (* Sanity check *)

  Definition elambda (t : P.expr Kt) : P.expr Kt :=
  @E_ctor sig_lam CLam (
    E_al_cons (E_abind (E_aterm t)) E_al_nil
  ).
  Definition eApp (f u : P.expr Kt) : P.expr Kt :=
  @E_ctor sig_lam CApp (
    E_al_cons (E_aterm f) (E_al_cons (E_aterm u) E_al_nil)
  ).

  Lemma proof_type_id :
    [] ⊢ ((elambda (E_var 0), sArrow sIota sIota)).
  Proof.
    pose (m := fun k =>
      if (k.(name)=?nb) then (E_var(sig:=sig_lam) 0)
      else (default_menv k)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact m. exact tLam. exact (sIota, sIota). repeat (try (left; reflexivity); right).
    3: reflexivity.
    all: intros; destruct_n H; noconf H.
    simpl. unfold eval_jdg, fmap, FMapProd, fmap, FMapId.
    eapply conv_proof_j. apply tvar. constructor.
    reflexivity.
  Qed.

  Instance LambdaSubst : SubstJSig typ_lam.
  constructor; intros; destruct_n H; subst; try destruct x; destruct_n H0; inversion H0.
  Qed.

  Lemma proof_type_id_app :
    [sIota] ⊢ (eApp (elambda (E_var 0)) (E_var 0), (sIota)).
  Proof.
    pose (m := fun k =>
      if (k.(name)=?nf) then (elambda (E_var 0))
      else if (k.(name)=?nu) then (E_var 0)
      else (default_menv k)
    ).
    eapply conv_proof_j.
    unshelve econstructor.
    exact m. apply tApp. exact (sIota, sIota). repeat (try (left; reflexivity); right).
    3: reflexivity.
    all: intros; destruct_n H; noconf H.
    - simpl.
      eapply conv_proof_j.
      eapply (weaken_typing (jsig:=typ_lam)).
      apply (proof_type_id).
      reflexivity.
    - simpl.
      eapply conv_proof_j. apply tvar. constructor.
      reflexivity.
  Qed.
End SimplLambda.