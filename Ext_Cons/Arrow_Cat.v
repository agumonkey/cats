Require Import Category.Main.
Require Import Ext_Cons.Arrow.

(*
   The Arrow Category of C:
     Objects : Arrows of C
     Arrows: for g : a → b and h : c → d, an arrow from g to h is a pair of arrows (f,f') s.t. the ollowing commutes:

             g
         a ––––→ b
         ∣       ∣
        f∣       ∣f'
         ↓       ↓
         c –——–→ d
             h
*)

Section Arrow_Cat.
  Context `(C : Category Obj Hom).

  Program Instance Arrow_Cat : Category (Arrow C) (@Arrow_Hom _ _ C) :=
    {
      compose := λ _ _ _ f g, Arrow_Hom_compose _ f g;
      
      id := λ a, Arrow_id _
    }.

  (* Arrow_Cat defined *)

End Arrow_Cat.


