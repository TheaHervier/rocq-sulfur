From Sulfur Require Export All.

Sulfur Generate
{{
  term : Type

  Ty : {{nat}} -> term
  Pi : term -> (bind term in term) -> term
  lam : (bind term in term) -> term
  app : term -> term -> term
}}.

Ren Generate [[
  Relation uconv : term -> term -> Prop;

  Rule my_urefl :
    Variables : (t : term)
    Premises :
    Conclusion : uconv t t
  ;
  Rule my_usym :
    Variables : (s t : term)
    Premises :
      Ind( uconv s t )
    Conclusion : uconv s t
  ;
  Rule my_utrans :
    Variables : (s t u : term)
    Premises :
      Ind (uconv s t)
      Ind (uconv t u)
    Conclusion : uconv s u
  ;

  Rule my_ucongr_app :
    Variables : (t u t' u' : term)
    Premises :
      Ind (uconv t t')
      Ind (uconv u u')
    Conclusion :
      uconv (app t u) (app t' u')
  ;
  Rule my_ucongr_Pi :
    Variables : (A B A' B' : term)
    Premises :
      Ind (uconv A A')
      Ind (uconv B B')
    Conclusion :
      uconv (Pi A B) (Pi A' B')
  ;
  Rule my_ucongr_lam :
    Variables : (b b' : term)
    Premises :
      Ind (uconv b b')
    Conclusion :
      uconv (lam b) (lam b')
  ;

  Rule my_ubeta :
    Variables : (b u : term)
    Premises :
    Conclusion :
      uconv (app (lam b) u) (substitute (scons u sid) b)
  ;
]].

Ren Generate [[
  Relation type : (list term) -> term -> term -> Prop;

  Rule my_type_Ty :
    Variables : (Γ : (list term)) (n : nat)
    Premises :
    Conclusion :
      type Γ (Ty n) (Ty (S n))
  ;
  Rule my_type_Pi :
    Variables : (Γ : (list term)) (n m : nat) (A B : term)
    Premises :
      Ind (type Γ A (Ty n))
      Ind (type Γ B (Ty m))
    Conclusion :
      type Γ (Pi A B) (Ty (Nat.max n m))
  ;

  Rule my_type_app :
    Variables : (Γ : (list term)) (A B t u : term)
    Premises :
      Ind (type Γ t (Pi A B))
      Ind (type Γ u A)
    Conclusion :
      type Γ (app t u) (substitute (scons u sid) B)
  ;
  Rule my_type_lam :
    Variables : (Γ : (list term)) (A B b : term)
    Premises :
      Ind (type (cons A Γ) b B)
    Conclusion :
      type Γ (lam b) (Pi A B)
  ;

  Rule my_type_conv :
    Variables : (Γ : (list term)) (A A' t : term)
    Premises :
      Ind (type Γ t A)
      Pred (uconv A A')
    Conclusion :
      type Γ t A'
  ;
]].

Print type.

Ren Generate [[
  Relation conv : (list term) -> term -> term -> term -> Prop;
  Relation typ : (list term) -> term -> term -> Prop;

  (* Conversion rules *)
  Rule my_refl :
    Variables : (Γ : (list term)) (t A : term)
    Premises :
      Ind (typ Γ t A)
    Conclusion : conv Γ t t A
  ;
  Rule my_sym :
    Variables : (Γ : (list term)) (s t A : term)
    Premises :
      Ind(conv Γ s t A)
    Conclusion : conv Γ s t A
  ;
  Rule my_trans :
    Variables : (Γ : (list term)) (s t u A : term)
    Premises :
      Ind (conv Γ s t A)
      Ind (conv Γ t u A)
    Conclusion : conv Γ s u A
  ;

  Rule my_congr_app :
    Variables : (Γ : (list term)) (t u t' u' A B : term)
    Premises :
      Ind (conv Γ t t' (Pi A B))
      Ind (conv Γ u u' A)
    Conclusion :
      conv Γ (app t u) (app t' u') (substitute (scons u sid) B)
  ;
  Rule my_congr_Pi :
    Variables : (Γ : (list term)) (A B A' B' : term) (n m : nat)
    Premises :
      Ind (conv Γ A A' (Ty n))
      Ind (conv Γ B B' (Ty m))
    Conclusion :
      conv Γ (Pi A B) (Pi A' B') (Ty (Nat.max n m))
  ;
  Rule my_congr_lam :
    Variables : (Γ : (list term)) (b b' A B : term)
    Premises :
      Ind (conv (cons A Γ) b b' B)
    Conclusion :
      conv Γ (lam b) (lam b') (Pi A B)
  ;

  Rule my_beta :
    Variables : (Γ : (list term)) (b u A B : term)
    Premises :
      Ind (typ (cons A Γ) b B)
      Ind (typ Γ u A)
    Conclusion :
      conv Γ (app (lam b) u) (substitute (scons u sid) b) (substitute (scons u sid) B)
  ;

  (* Typing rules *)
  Rule my_typ_Ty :
    Variables : (Γ : (list term)) (Γ : (list term)) (n : nat)
    Premises :
    Conclusion :
      typ Γ (Ty n) (Ty (S n))
  ;
  Rule my_typ_Pi :
    Variables : (Γ : (list term)) (n m : nat) (A B : term)
    Premises :
      Ind (typ Γ A (Ty n))
      Ind (typ Γ B (Ty m))
    Conclusion :
      typ Γ (Pi A B) (Ty (Nat.max n m))
  ;

  Rule my_typ_app :
    Variables : (Γ : (list term)) (A B t u : term)
    Premises :
      Ind (typ Γ t (Pi A B))
      Ind (typ Γ u A)
    Conclusion :
      typ Γ (app t u) (substitute (scons u sid) B)
  ;
  Rule my_typ_lam :
    Variables : (Γ : (list term)) (A B b : term)
    Premises :
      Ind (typ (cons A Γ) b B)
    Conclusion :
      typ Γ (lam b) (Pi A B)
  ;

  Rule my_typ_conv :
    Variables : (Γ : (list term)) (A A' t : term) (n : nat)
    Premises :
      Ind (typ Γ t A)
      Ind (conv Γ A A' (Ty n))
    Conclusion :
      typ Γ t A'
  ;
]].

Print conv.