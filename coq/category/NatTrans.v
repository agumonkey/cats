Require Export Category.
Require Export Functor.

Generalizable All Variables.
Open Scope signature.

Section natrual_transformation.
Check @Functor.
Context (C D : Type)
        {aC:Arrows C} {aD:Arrows D}
        {catC:Category C} {catD:Category D}
       `{@Functor C aC catC D aD catD F Fmor}
       `{@Functor C aC catC D aD catD G Gmor}.
     
Notation " a ~{ X }{ Y }~> b " := (@Hom X Y a b) (at level 40).

Class NatTrans 
  (trans : forall x : C, (F x) ~> (G x))
  :=
  { nt_trans := trans
  ; nt_natural : forall (x y : C) (f : x ~> y),
    (nt_trans y) ∘ (Fmor x y f) == (Gmor x y f) ∘ (nt_trans x)
  }.

Notation "η_{ x }" := (nt_trans x) (at level 40).
End natrual_transformation.

Section id_nat_trans.
Context `{aC:Arrows C} `{aD:Arrows D}
        {catC:Category C} {catD:Category D}
        `(F : C->D) `(F_f : @Functor C aC catC D aD catD F Fmor).

Definition idN (x:C) := @cat_id D aD catD (F x).
Global Program Instance : 
  @NatTrans C D aC aD catD F Fmor F Fmor idN.
Next Obligation.
  unfold idN. 
  rewrite id_r. symmetry. apply id_l.
  Qed.

End id_nat_trans.