From Sulfur Require Import Prelude Sig Renamings.
From Sulfur Require Import ParamSyntax.
Module P := ParamSyntax.

Section WithSignature.
Context {sig : signature}.

  (** Notations for expressions with known kinds. *)
  #[local] Reserved Notation "'mterm'" (at level 0).
  #[local] Reserved Notation "'marg' ty" (at level 0, ty at level 0).
  #[local] Reserved Notation "'margs' tys" (at level 0, tys at level 0).
  #[local] Reserved Notation "'msubst' s" (at level 0).

  #[local] Notation "'term'" := (P.expr Kt) (at level 0).
  #[local] Notation "'arg' ty" := (P.expr (Ka ty)) (at level 0, ty at level 0).
  #[local] Notation "'args' tys" := (P.expr (Kal tys)) (at level 0, tys at level 0).

  Unset Elimination Schemes.
  (* Meta variables *)
  Record mvar := {
    (* Meta variables do not have binders, so we can use names easily. We use natural numbers for names *)
    index : nat;

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
  | (** Meta variable applyed to a substitution ; might want to change that to only finite substitutions, but maybe by using the identity substitution it can work ? **)
    M_mvar scope :
      mvar -> msubst scope -> mterm scope

  (* Parametrize the meta variables by an arity or a function, something that immediately says "it has n variables that we substitute" *)

  where "'mterm'" := (mexpr Kt)
    and "'marg' ty" := (mexpr (Ka ty))
    and "'margs' tys" := (mexpr (Kal tys))
    and "'msubst' s" := (nat -> mterm s).

  Section ExprInd.
    Context (P : forall k s, mexpr k s -> Prop).

    Context (H_var : forall s i (Hsi : i < s), P _ _ (M_var s i Hsi)).
    Context (H_ctor : forall s c al, P _ _ al -> P _ _ (M_ctor s c al)).
    Context (H_al_nil : forall s, P _ _ (M_al_nil s)).
    Context (H_al_cons : forall s ty tys (a : marg ty _) (al : margs tys _),
      P _ _ a -> P _ _ al -> P _ _ (M_al_cons s a al)).
    Context (H_abase : forall s b x, P _ _ (M_abase s b x)).
    Context (H_aterm : forall s t, P _ _ t -> P _ _ (M_aterm s t)).
    Context (H_abind : forall s ty (a : marg ty _), P _ _ a -> P _ _ (M_abind s a)).
    Context (H_mvar : forall s k σ,
      (forall i, i < lscope k -> P _ _ (σ i)) ->
      P _ _ (M_mvar s k σ)
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

  End ExprInd.

  (** Some basic [msubsts] (i.e. substitutions for meta terms) **)
  (** TODO **)
  (**
    Identity substitution of meta terms, scoped by [s]. We do not depend on the number [l] of substituted variables:
    - If [l < s], then we describe the substitution on more variables than useful: it is not a problem
    - If [s <= l], then there is a problem in what we want to define: the identity substitution is not what we want

    But, if s = 0, then we have a problem... The type [msubst 0] might be empty because [mterm 0] might be...
  **)
  (* Definition msid (s : nat) : msubst s.
  Proof.
    intro i. destruct (i <? s) eqn:Hi.
    - eapply M_var. apply PeanoNat.Nat.ltb_lt. apply Hi.
    -  *)

  (*********************************************************************************)
  (** *** Evaluation of a meta term *)
  (*********************************************************************************)

  Definition menv := mvar -> P.expr Kt.
  Definition default_menv : menv := fun k => E_var (index k).

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
  eval m (M_mvar _ k σ) := substitute
    (fun i =>
      if i<?lscope k then
        eval m (σ i)
      else
        (* [- lscope k] shifts the indexes to take into account the substitution *)
        (* [+ s] takes into account the scope, "the number of lambdas we are under" *)
        E_var (i - lscope k + s)
    ) (m k).
  Locate "=₁".
  #[export] Instance eval_proper_inst {k s} :
    Proper (eq1 ==> eq ==> eq) (@eval s k).
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

  (* This lemma is the commutation lemma in Thiago's thesis *)
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
        rewrite Hi. rewrite H. reflexivity.
        apply PeanoNat.Nat.ltb_lt; assumption.
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

  (** TODO : can this be generalized? **)
  (* A context is a list of terms ; we require the contexts to be closed, so we need an ad-hoc definition *)
  (* It will maybe be a pain to remake every function from [list]... Should I say that [mctx] are lists of dependent pairs, so that I can reuse lists, or is it too complicated for nothing? *)
  (** We need the length of the context in order to scope everything correctly ; so [Γ : mctx s n] means that [Γ] is scoped by [s] and has length [n] **)
  Inductive mctx : nat -> nat -> Type :=
  (* [mctx scope len] *)
  | mnil {scope : nat} : mctx scope 0
  | mcons {scope n : nat}
    (t : mterm (scope+n)) (Γ : mctx scope n) :
    mctx scope (S n).
  Definition ctx := list term.

  (** Evaluation of a context **)
  Equations eval_ctx {s n} (m : menv) (Γ : mctx s n) : ctx :=
  eval_ctx m mnil := [] ;
  eval_ctx m (mcons t Γ) := (eval m t)::eval_ctx m Γ.

  (** Evaluation preserves length **)
  Lemma eval_length {s n} (Γ : mctx s n) :
    forall m, n = Datatypes.length (eval_ctx m Γ).
  Proof.
    induction Γ; intros; simpl. reflexivity. f_equal. apply IHΓ.
  Qed.

  (** Renaming of a context: we need to shift the renamings accordingly **)
  Equations rename_ctx (ρ : ren) (Γ : ctx) : ctx :=
  rename_ctx ρ [] => [];
  rename_ctx ρ (A :: Γ) => rename (up_rens (Datatypes.length Γ) ρ) A :: rename_ctx ρ Γ.

  Lemma scoped_ctx_rename_eval {s n} (Γ : mctx s n) :
    forall m ρ,
    rename_ctx (up_rens s ρ) (eval_ctx m Γ) =
    eval_ctx (fun k => rename (up_rens (lscope k) ρ) (m k)) Γ.
  Proof.
    induction Γ; intros; simpl.
    - reflexivity.
    - rewrite IHΓ. f_equal.
      rewrite <- eval_length. rewrite <- scoped_rename_eval.
      apply rename_proper. 2: reflexivity.
      replace (scope + n) with (n + scope) by lia.
      apply up_rens_add.
  Qed.

  (* Belonging to a context *)
  (* We use the non meta definitions, since we need to evaluate the possible renamings and substitutions *)
  Reserved Notation "Γ ∋ n : A" (at level 70, n at level 50).
  Inductive inctx : ctx -> nat -> term -> Prop :=
  | in_head A Γ :
    A::Γ ∋ 0 : rename rshift A
  | in_tail A B Γ n :
    Γ ∋ n : A ->
    B::Γ ∋ S n : rename rshift A
  where "Γ ∋ n : A" := (inctx Γ n A).

  (* Allows to use existential variables easily *)
  Lemma conv_in_t Γ n A B :
    Γ ∋ n : A ->
    A = B ->
    Γ ∋ n : B.
  Proof. intros; subst; assumption. Qed.
  Lemma conv_in_n Γ n m A :
    Γ ∋ n : A ->
    n = m ->
    Γ ∋ m : A.
  Proof. intros; subst; assumption. Qed.

  (* A judgment is of the form [⊢ t : A], so a pair of (scoped meta) terms *)
  Definition jdgF X := (X * X)%type.
  Definition mjdg (s : nat) := jdgF (mterm s).
  Definition jdg  := jdgF term.

  (** Evaluating and renaming a judgment is much more straightforward **)
  Definition eval_jdg {s} m : mjdg s -> jdg := fmap jdgF (eval m).
  Definition rename_jdg ρ : jdg -> jdg := fmap jdgF (rename ρ).

  Lemma scoped_jdg_rename_eval {s} (j : mjdg s) :
    forall m ρ,
    rename_jdg (up_rens s ρ) (eval_jdg m j) =
    eval_jdg (fun k => rename (up_rens (lscope k) ρ) (m k)) j.
  Proof.
    (* This should be made abstractly at some point I suppose *)
    intros. destruct j as [t A]. unfold rename_jdg, eval_jdg, lift, LiftId in *.
    simpl. rewrite func_comp.
    unfold fmap, FMapProd, fmap, FMapId.
    f_equal; try apply scoped_rename_eval.
  Qed.
  Corollary closed_jdg_rename_eval (j : mjdg 0) :
    forall m ρ,
    rename_jdg ρ (eval_jdg m j) =
    eval_jdg (fun k => rename (up_rens (lscope k) ρ) (m k)) j.
  Proof. apply (@scoped_jdg_rename_eval 0). Qed.

  Reserved Notation "Δ ⊢r ρ : Γ" (at level 70, ρ at level 50).
  Inductive rtyping : ctx -> ren -> ctx -> Prop :=
  | rtyping_empty Δ ρ :
    Δ ⊢r ρ : []
  | rtyping_cons Δ ρ Γ A :
    Δ ⊢r rcomp rshift ρ : Γ ->
    Δ ∋ (ρ 0) : rename (rcomp rshift ρ) A ->
    Δ ⊢r ρ : A::Γ
  where "Δ ⊢r ρ : Γ " := (rtyping Δ ρ Γ).
  Lemma conv_rtyping Δ ρ ρ' Γ :
    Δ ⊢r ρ : Γ ->
    ρ = ρ' ->
    Δ ⊢r ρ' : Γ.
  Proof. intros; subst; assumption. Qed.

  (* Contexts in premises must be closed, and judgments must be scoped by the context *)
  Variant premise :=
  | prem_pred (P : ctx -> Prop)
    (HP : forall Δ ρ Γ, P Γ -> Δ ⊢r ρ : Γ -> P Δ)
  | prem_ind {n} (Δ : mctx 0 n) (j : mjdg n).

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

  (*********************************************************************************)
  (** *** Derivation tree *)
  (*********************************************************************************)

  Context {jsig : jdg_sig}.
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
    (* Satisfy all leaf predicates, depending on Γ *)
    (
      forall P HP, In (prem_pred P HP) (r.(premises) x) ->
      P Γ
    ) ->
    Γ ⊢ eval_jdg m (r.(conclusion) x)
  | tvar (Γ : ctx) (n : nat) (A : term) :
    Γ ∋ n : A ->
    Γ ⊢ (E_var n, A) (* How to generalize this? *)
  where "Γ ⊢ j" := (proof Γ j).
  (* Notation "Γ ⊢( s ) j" := (@proof s Γ j) (at level 70). *)

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

  (*********************************************************************************)
  (** *** "Typing" (hard coded for [ctx = list term] and [jdg = term*term]) of a renaming and a substitution *)
  (*********************************************************************************)

  Reserved Notation "Δ ⊢s σ : Γ" (at level 70, σ at level 50).
  Inductive styping : ctx -> subst -> ctx -> Prop :=
  | styping_empty Δ σ :
    Δ ⊢s σ : []
  | styping_cons Δ σ Γ A :
    Δ ⊢s rscomp rshift σ : Γ ->
    Δ ⊢ ((σ 0), substitute (rscomp rshift σ) A) ->
    Δ ⊢s σ : A::Γ
  where "Δ ⊢s σ : Γ " := (styping Δ σ Γ).

  (*********************************************************************************)
  (** *** Renaming lemmas *)
  (*********************************************************************************)
  Lemma rtyping_proper :
    Proper (eq ==> eq1 ==> eq ==> Basics.impl) rtyping.
  Proof.
    intros Δ' Δ HΔ ρ ρ' Hρ Γ' Γ HΓ H; subst.
    induction H in ρ', Hρ |- *; intros; constructor.
    - apply IHrtyping. apply congr_rcomp. reflexivity. assumption.
    - rewrite <- Hρ. assumption.
  Qed.
  Lemma conv_rtype_r Δ ρ ρ' Γ :
    Δ ⊢r ρ : Γ ->
    ρ =₁ ρ' ->
    Δ ⊢r ρ' : Γ.
  Proof.
    intros Hρ Heq. Fail rewrite <- Heq.
    eapply rtyping_proper. reflexivity. apply Heq. reflexivity. assumption.
  Qed.

  Lemma rename_in Δ Γ ρ n A :
    Γ ∋ n : A ->
    Δ ⊢r ρ : Γ ->
    Δ ∋ ρ n : rename ρ A.
  Proof.
    intros HΓ Hρ. induction HΓ in Δ, ρ, Hρ |- *; intros;
    inversion Hρ; subst; rewrite ren_ren.
    - assumption.
    - eapply conv_in_n. apply IHHΓ. assumption.
      reflexivity.
  Qed.

  Lemma rtyping_comp Γ Δ Θ ρ ρ' :
    Δ ⊢r ρ : Γ ->
    Θ ⊢r ρ' : Δ ->
    Θ ⊢r rcomp ρ ρ' : Γ.
  Proof.
    intros Hρ Hρ'. induction Hρ in Θ, ρ', Hρ' |- *; intros; constructor.
    - eapply rtyping_proper. reflexivity. 2: reflexivity.
      apply rcomp_assoc. apply IHHρ. assumption.
    - eapply conv_in_t. unfold rcomp. eapply rename_in. apply H. assumption.
      rewrite ren_ren, rcomp_assoc. reflexivity.
  Qed.

  Lemma weaken_rtyping Γ ρ Δ A :
    Δ ⊢r ρ : Γ ->
    A::Δ ⊢r rcomp ρ S : Γ.
  Proof.
    intros Hρ. induction Hρ in A |- *; intros; constructor.
    - apply IHHρ.
    - eapply conv_in_t. constructor. apply H.
      rewrite ren_ren, rcomp_assoc. reflexivity.
  Qed.

  Lemma up_rtyping Γ ρ Δ A :
    Δ ⊢r ρ : Γ ->
    (rename ρ A)::Δ ⊢r up_ren ρ : A::Γ.
  Proof.
    intros Hρ. constructor.
    - apply weaken_rtyping. assumption.
    - eapply conv_in_t. simpl. constructor.
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
    replace a with (rename rid a) at 1 by apply ren_rid.
    Fail rewrite <- up_ren_rid.
    eapply conv_rtype_r.
    - apply up_rtyping. assumption.
    - apply up_ren_rid.
  Qed.

  Theorem preserve_renaming Γ j Δ ρ :
    Γ ⊢ j ->
    Δ ⊢r ρ : Γ ->
    Δ ⊢ rename_jdg ρ j.
  Proof.
    intros Hj Hρ.
    induction Hj in Δ, ρ, Hρ |- *.
    (* We apply rule [r x] *)
    eapply conv_proof_j.
    unshelve econstructor.
    shelve.
    exact r. exact x.
    assumption.
    3: {symmetry. apply closed_jdg_rename_eval. }
    (* Case of an inductive premise *)
    - intros.
      rewrite <- scoped_jdg_rename_eval. eapply H1. apply H3.
      rewrite <- scoped_ctx_rename_eval. simpl.
      eapply conv_rtyping.
      eapply up_rtyping_n. assumption.
      f_equal. symmetry. apply eval_length.
    (* Case of a predicate premise *)
    - intros.
      eapply HP. 2: apply Hρ. eapply H2. apply H3.
    (* Case of a variable *)
    - unfold rename_jdg, fmap, FMapProd, fmap, FMapId.
      constructor. eapply rename_in. apply H. assumption.
  Qed.
End WithSignature.
Notation "Γ ∋ n : A" := (inctx Γ n A) (at level 70, n at level 50).
Notation "Γ ⊢( s ) j" := (@proof _ s Γ j) (at level 70).
Notation "Γ ⊢ j" := (proof Γ j) (at level 70).

Notation "Δ ⊢r ρ : Γ" := (rtyping Δ ρ Γ) (at level 70, ρ at level 50).
Notation "Δ ⊢s σ : Γ" := (styping Δ σ Γ) (at level 70, σ at level 50).

Section LambdaPi.
  (** Example of Lambda Pi **)

  Variant EBase := Nat.
  Variant CLamPi := CType | CApp | CLam | CPi.

  Program Definition sig_lp : signature := {|
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
  Next Obligation. destruct x, y; left; reflexivity. Qed.
  Next Obligation.
    destruct x, y; try (left; reflexivity); right; intro H; inversion H.
  Qed.

  #[local] Notation "'mterm'" := (@mexpr sig_lp Kt) (at level 0).
  #[local] Notation "'marg' ty" := (@mexpr sig_lp (Ka ty)) (at level 0, ty at level 0).
  #[local] Notation "'margs' tys" := (@mexpr sig_lp (Kal tys)) (at level 0, tys at level 0).

  (* Overwrite the notation for lambda pi *)
  Notation "Γ ∋ n : A" := (@inctx sig_lp Γ n A) (at level 70, n at level 50).

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

  (* Some common meta variables *)
  Definition A : mvar := {|index:=0;lscope:=0|}.
  Definition B : mvar := {|index:=1;lscope:=1|}.
  Definition f : mvar := {|index:=2;lscope:=1|}.
  Definition u : mvar := {|index:=3;lscope:=0|}.
  Definition b : mvar := {|index:=4;lscope:=0|}.

  (* Typing rules *)

  Definition tType : rule :=
  {|
    premises := fun _ => [];
    conclusion := fun u => (T u, T (S u))
  |}.

  (* Need to have something cleaner for msubst *)
  Fail Definition tPi : rule :=
  {|
    premises := fun '(u, v) =>
    [
      prem_ind
        mnil
        (M_mvar 0 A (fun n => M_var n), T u) ;
      prem_ind
        (mcons (M_mvar 0 A default_menv) mnil)
        (M_mvar 0 B default_menv, T v)
    ] ;
    conclusion := fun '(u, v) =>
      (Pi (M_mvar 0 A default_menv) (M_mvar 0 B default_menv), T (Nat.max u v))
  |}.

  (*
  Definition tPi : rule :=
  {|
    premises:= fun '(u, v) =>
    [
      prem_ind [] (A, T u);
      prem_ind [A] (B, T v)
    ];
    conclusion:= fun '(u, v) =>
      (Pi A B, T (Nat.max u v))
  |}.
  Definition tApp : rule :=
  {|
    premises:= fun (_ : unit) =>
      [
        prem_ind [] (f, Pi A B);
        prem_ind [] (u, A)
      ];
    conclusion:= fun _ =>
      (App f u, M_subst (mscons u msid) B)
  |}.
  Definition tLam : rule :=
  {|
    premises:= fun (_ : unit) => [
      prem_ind [A] (b, B)
    ];
    conclusion := fun _ =>
      (lambda b, Pi A B)
  |}.

  Definition typ_lambpi : @jdg_sig sig_lp := {|
    rules := [
      tType;
      tVar;
      tPi;
      tApp;
      tLam
    ]
  |}.

  (* Overwrite notations for lambda pi *)
  Notation "Γ ⊢ j" := (@proof _ typ_lambpi Γ j) (at level 70).
  Notation "Δ ⊢r ρ : Γ" := (@rtyping sig_lp Δ ρ Γ) (at level 70, ρ at level 50).
  Notation "Δ ⊢s σ : Γ" := (@styping _ typ_lambpi Δ σ Γ) (at level 70, σ at level 50).

  (* It is absolutely horrible to use, obviously *)
  Definition elambda (t : P.expr Kt) : P.expr Kt :=
  @E_ctor sig_lp CLam (
    E_al_cons (E_abind (E_aterm t)) E_al_nil
  ).
  (* Lemma proof_type_id u :
    [] ⊢ (elambda (@E_var 0), Pi (T u) (T u)).
  Proof.
    eapply conv_proof.
    unshelve econstructor. exact tLam. repeat split. shelve. shelve. shelve.
    4: {
      simpl. reflexivity.
    }
    - repeat (try (left; reflexivity); right).
    - intros. inversion H.
      + inversion H0; subst.
        simpl. clear H H0.
        eapply conv_proof.
        unshelve econstructor. exact tVar. simpl. split; shelve.
        repeat (try (left; reflexivity); right).
        3: {
          simpl. reflexivity.
        }
        intros. inversion H. inversion H0. inversion H0.
        intros. inversion H. 2: {inversion H0. }
        inversion H0; subst. constructor.
      + inversion H0.
    - intros. inversion H. inversion H0. inversion H0.
  Qed. *) *)

End LambdaPi.