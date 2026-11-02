(** λΠ-calculus (sorta) *)

From Stdlib Require Import Utf8 String.
From Sulfur Require Import Prelude Sig Renamings All.
From Sulfur Require Import ParamSyntax JudgmentSyntaxScoped.
From Sulfur Require Import ConcreteSyntax JdgDesc.

Sulfur Syntax {{
  tm : Type

  | tTy : nat → tm
  | tPi : tm → (tm → tm) → tm
  | tlam : tm → (tm → tm) → tm
  | tapp : tm → tm → tm
}}.

Existing Instance sign.

Sulfur Judgment typing {{
| type_Ty i :
    ⟹ typing (tTy i) (tTy (S i))

(* | type_Pi i j A B :
    typing A (tTy i)
    ⟹ typing (tPi A B) (tTy (max i j)) *)

(* | type_lam i j A B t : *)

(* | type_app A B f u :
    typing f (tPi A B) ;
    typing u A
    ⟹ typing (tapp f u) A *)
}}.

Print typing_desc.
Print typing.

Check typing_wf : wf_desc typing_desc.
Check typing_rules : rules_type typing_desc typing.
Check typing_sound : sound_jdg typing_desc typing.
Check typing_complete : complete_jdg typing_desc typing.
Check typing_subst :
  ∀ Γ Δ σ t A,
    typing Γ t A →
    cstyping typing Δ σ Γ →
    typing Δ (substitute σ t) (substitute σ A).

Print Assumptions typing_subst.
