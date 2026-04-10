From Utils Require Import Generalities.
From Stdlib Require Import List. Import ListNotations.

(* This files defines utils about functors *)
Class FMap (F : Type -> Type) := fmap : forall {X Y : Type}, (X -> Y) -> (F X -> F Y).
Arguments fmap (F) {_ _ _}.

Class Functor (F : Type -> Type) `{FMap F} := {
  func_id : forall {X : Type},
    fmap F (fun x : X => x) =₁ (fun x => x);

  func_comp : forall {X Y Z : Type} (f : X -> Y) (g : Y -> Z),
    (fun x => fmap F g (fmap F f x)) =₁ fmap F (fun x => g (f x))
}.

(** Examples of functors **)
(* Identity functor *)
#[export] Instance FMapId : FMap (fun X : Type => X) :=
  fun _ _ f => f.
#[export] Instance FId : Functor (fun X => X).
Proof.
  constructor; unfold fmap; repeat intro; reflexivity.
Qed.

(* Constant functor *)
#[export] Instance FMapConst (C : Type) : FMap (fun _ => C) :=
  fun _ _ _ => (fun c => c).
#[export] Instance FConst (C : Type) : Functor (fun _ => C).
Proof.
  constructor; unfold fmap; repeat intro; reflexivity.
Qed.

(* Lists *)
#[export] Instance FMapList : FMap list := map.
#[export] Instance Flist : Functor list.
Proof.
  constructor; unfold fmap, FMapList; repeat intro.
  - apply map_id.
  - induction a; simpl.
    reflexivity.
    rewrite IHa. reflexivity.
Qed.

(* Product of functors *)
#[export] Instance FMapProd F G `{FMap F} `{FMap G} : FMap (fun X => (F X * G X)%type) :=
  fun X Y (f : X -> Y) '(xf, xg) => (fmap F f xf, fmap G f xg).
#[export] Instance FProf F G `{Functor F} `{Functor G} : Functor (fun X => (F X * G X)%type).
Proof.
  constructor; unfold fmap, FMapProd; repeat intro; destruct a as [xf xg].
  - rewrite 2!func_id. reflexivity.
  - rewrite 2!func_comp. reflexivity.
Qed.

(* Sanity check *)
Goal Functor (fun X => (X*nat*X)%type). typeclasses eauto. Qed.

(** Lifting of a predicate to a functor **)
Class Lift (F : Type -> Type) := lift : forall X, (X -> Prop) -> (F X -> Prop).
Arguments lift (F) {_ _}.

(* We will see what axioms we need *)
Class Predicator (F : Type -> Type) `{Lift F}
:= {}.

#[export] Instance LiftList : Lift list := Forall.
#[export] Instance PList : Predicator list.
Qed.

#[export] Instance LiftId : Lift (fun X => X) := fun _ P => P.
#[export] Instance PId : Predicator (fun X => X).
Qed.

#[export] Instance LiftProd F G `{Lift F} `{Lift G} : Lift (fun X => (F X * G X)%type) :=
fun _ P '(xf, xg) => (lift F P xf) /\ (lift G P xg).
#[export] Instance PProd F G `{Predicator F} `{Predicator G} : Predicator (fun X => (F X * G X)%type).
Qed.