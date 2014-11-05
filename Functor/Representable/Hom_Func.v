Require Import Category.Main.
Require Import Functor.Functor.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Ext_Cons.Prod_Cat.


Set Primitive Projections.

Set Universe Polymorphism.

Program Instance Hom_Func (C : Category) : Functor (Prod_Cat C ^op C) Type_Cat :=
{
  FO := fun x => @Hom C (fst x) (snd x);
  FA := fun x y f => fun g => (@compose C _ _ _) (fst f) ((@compose C^op _ _ _) (snd f) g)
}.

(* Hom_Func defined *)





