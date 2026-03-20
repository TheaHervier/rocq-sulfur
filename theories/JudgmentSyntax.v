From Sulfur Require Import Prelude Sig Renamings.
From Sulfur Require Import ParamSyntax.

Section WithSignature.
  Context {sig : signature}.

  #[local] Notation "'term'" := (expr Kt) (at level 0).
  #[local] Notation "'arg' ty" := (expr (Ka ty)) (at level 0, ty at level 0).
  #[local] Notation "'args' tys" := (expr (Kal tys)) (at level 0, tys at level 0).

  Definition weaken {k} (e : expr k) := rename rshift e.

  (** TODO : can this be generalized? **)
  (* A context is a list of terms *)
  Definition ctx := list term.
  (* Definition singl_context : term -> ctx := fun t => [t]. *)
  (* I suppose Coercion works weirdly *)
  (* #[local] Coercion singl_context : term >-> ctx. *)
  (* #[local] Notation "Γ , Δ" := (Δ ++ Γ : ctx) (at level 60, right associativity). *)
  (* Without Coercion, we need to write [Γ, [A]] instead of [Γ, A] *)


  (* Belonging to a context *)
  Reserved Notation "Γ ∋ n : A" (at level 70, n at level 50).
  Inductive inctx : ctx -> nat -> term -> Prop :=
  | in_head A Γ :
    A::Γ ∋ 0 : weaken A
  | in_tail A B Γ n :
    Γ ∋ n : A ->
    B::Γ ∋ S n : weaken A
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

  (* A judgment is of the form [⊢ t : A], so a pair of terms *)
  Definition jdg : Type := term * term.

  Variant premise :=
  | prem_pred (P : ctx -> Prop)
  | prem_ind (c : ctx) (j : jdg).

  Record rule := {
    param : Type; (* A rule is parametrized by a functor, that will be applied to [term] (TODO) *)
    premises : param -> list premise;
    conclusion : param -> jdg;
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
  | step (Γ : ctx) (r : rule) (x : r.(param)) :
    (* The rule must be in the signature *)
    In r (jsig.(rules)) ->
    (* Satisfy all inductive premises *)
    (
      forall Δ j, In (prem_ind Δ j) (r.(premises) x) ->
      (Δ ++ Γ) ⊢ j
    ) ->
    (* Satisfy all leaf predicates, depending on Γ *)
    (
      forall P, In (prem_pred P) (r.(premises) x) ->
      P Γ
    ) ->
    Γ ⊢ (r.(conclusion) x)
  where "Γ ⊢ j" := (proof Γ j).
  (* Notation "Γ ⊢( s ) j" := (@proof s Γ j) (at level 70). *)

  Lemma conv_proof Γ j j' :
    Γ ⊢ j ->
    j = j' ->
    Γ ⊢ j'.
  Proof. intros; subst; assumption. Qed.

  (*********************************************************************************)
  (** *** "Typing" (hard coded for [ctx = list term] and [jdg = term*term]) of a renaming and a substitution *)
  (*********************************************************************************)
  Reserved Notation "Δ ⊢r ρ : Γ" (at level 70, ρ at level 50).
  Inductive rtyping : ctx -> ren -> ctx -> Prop :=
  | rtyping_empty Δ ρ :
    Δ ⊢r ρ : []
  | rtyping_cons Δ ρ Γ A :
    Δ ⊢r rcomp rshift ρ : Γ ->
    Δ ∋ (ρ 0) : rename (rcomp rshift ρ) A ->
    Δ ⊢r ρ : A::Γ
  where "Δ ⊢r ρ : Γ " := (rtyping Δ ρ Γ).

  Definition rename_jdg : ren -> jdg -> jdg := fun ρ '(t, A) =>
    (rename ρ t, rename ρ A).

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
  (* TODO : We will need to add more hypothesis at some point *)
  Lemma rtyping_proper :
    Proper (eq ==> eq1 ==> eq ==> Basics.impl) rtyping.
  Proof.
    intros Δ' Δ HΔ ρ ρ' Hρ Γ' Γ HΓ H; subst.
    revert ρ' Hρ. induction H; intros; constructor.
    - apply IHrtyping. apply congr_rcomp. reflexivity. assumption.
    - rewrite <- Hρ. assumption.
  Qed.
  Lemma conv_rtype_r Δ ρ ρ' Γ :
    Δ ⊢r ρ : Γ ->
    ρ =₁ ρ' ->
    Δ ⊢r ρ' : Γ.
  Proof.
    intros. Fail rewrite <- H0.
    eapply rtyping_proper. reflexivity. apply H0. reflexivity. assumption.
  Qed.

  Lemma rename_in Δ Γ ρ n A :
    Γ ∋ n : A ->
    Δ ⊢r ρ : Γ ->
    Δ ∋ ρ n : rename ρ A.
  Proof.
    intro. revert Δ ρ. induction H; intros; unfold weaken in *.
    - inversion H; subst. rewrite ren_ren. assumption.
    - inversion H0; subst. rewrite ren_ren.
      eapply conv_in_n. apply IHinctx. assumption.
      reflexivity.
  Qed.

  Lemma rtyping_comp Γ Δ Θ ρ ρ' :
    Δ ⊢r ρ : Γ ->
    Θ ⊢r ρ' : Δ ->
    Θ ⊢r rcomp ρ ρ' : Γ.
  Proof.
    intro. revert ρ' Θ. induction H; intros; constructor.
    - eapply rtyping_proper. reflexivity. 2: reflexivity.
      apply rcomp_assoc. apply IHrtyping. assumption.
    - eapply conv_in_t. unfold rcomp. eapply rename_in. apply H0. assumption.
      rewrite ren_ren, rcomp_assoc. reflexivity.
  Qed.

  Lemma weaken_rtyping Γ ρ Δ A :
    Δ ⊢r ρ : Γ ->
    A::Δ ⊢r rcomp ρ S : Γ.
  Proof.
    intro. revert A. induction H; intros; constructor.
    - apply IHrtyping.
    - eapply conv_in_t. constructor. apply H0.
      unfold weaken. rewrite ren_ren, rcomp_assoc. reflexivity.
  Qed.

  Lemma up_rtyping Γ ρ Δ A :
    Δ ⊢r ρ : Γ ->
    (rename ρ A)::Δ ⊢r up_ren ρ : A::Γ.
  Proof.
    intros. constructor.
    - apply weaken_rtyping. assumption.
    - eapply conv_in_t. simpl. constructor.
      unfold weaken. rewrite ren_ren. reflexivity.
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
    intros.
    induction H.
    eapply conv_proof. unshelve econstructor. exact r.
    shelve. (* Will be a kind of renaming of [x] *)
    assumption.
    3: {
      shelve. (* Will come from a naturality condition on [param] *)
    }
    (* Show that we have what we want for all inductive premises *)
    - intros. admit.
    - intros. admit.
  Admitted.


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

  #[local] Notation "'term'" := (@expr sig_lp Kt) (at level 0).
  #[local] Notation "'arg' ty" := (@expr sig_lp (Ka ty)) (at level 0, ty at level 0).
  #[local] Notation "'args' tys" := (@expr sig_lp (Kal tys)) (at level 0, tys at level 0).

  (* Overwrite the notation for lambda pi *)
  Notation "Γ ∋ n : A" := (@inctx sig_lp Γ n A) (at level 70, n at level 50).

  (* λΠ constructors, written in a more accessible way *)
  Definition T (n : nat) : term :=
  @E_ctor sig_lp CType (
    E_al_cons (@E_abase sig_lp Nat n) E_al_nil
  ).

  Definition lambda (t : term) : term :=
  @E_ctor sig_lp CLam (
    E_al_cons (E_abind (E_aterm t)) E_al_nil
  ).

  Definition Pi (A B : term) : term :=
  @E_ctor sig_lp CPi (
    E_al_cons (E_aterm A) (E_al_cons (E_abind (E_aterm B)) E_al_nil)
  ).

  Definition App (f u : term) : term :=
  @E_ctor sig_lp CApp (
    E_al_cons (E_aterm f) (E_al_cons (E_aterm u) E_al_nil)
  ).

  Definition Var (n : nat) : term :=
  @E_var sig_lp n.

  (* Typing rules *)

  Definition tType : rule :=
  {|
    premises:= fun _ => [];
    conclusion:= fun u =>(T u, T (S u))
  |}.
  Definition tVar : rule :=
  {|
    premises:= fun '(n, A) =>
    [
      prem_pred (fun Γ => Γ ∋ n : A)
    ];
    conclusion := fun '(n, A) =>
      (E_var n, A)
  |}.
  Definition tPi : rule :=
  {|
    premises:= fun '(A, u, B, v) =>
    [
      prem_ind [] (A, T u);
      prem_ind [A] (B, T v)
    ];
    conclusion:= fun '(A, u, B, v) =>
      (Pi A B, T (Nat.max u v))
  |}.
  Definition tApp : rule :=
  {|
    premises:= fun '(f, A, B, u) =>
      [
        prem_ind [] (f, Pi A B);
        prem_ind [] (u, A)
      ];
    conclusion:= fun '(f, A, B, u) =>
      (App f u, substitute (scons u sid) B)
  |}.
  Definition tLam : rule :=
  {|
    premises:= fun '(A, b, B) => [
      prem_ind [A] (b, B)
    ];
    conclusion := fun '(A, b, B) =>
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
  Lemma proof_type_id u :
    [] ⊢ (lambda (Var 0), Pi (T u) (T u)).
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
  Qed.

End LambdaPi.