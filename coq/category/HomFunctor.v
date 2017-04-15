(**** Covariant Hom-functor ***)
Require Export Coq.Program.Program.

Require Export Category.
Require Export Functor.
Require Export Setoids.

Generalizable All Variables.
Open Scope signature.

Section hom_functor.

Context `{Category C} (O : C).

Definition HOM_F : C -> Objects := fun a => obj (Hom O a) _.
Program Definition hom_fmap (a b : C) (f : a ~> b) : (HOM_F a ~> HOM_F b) :=
  Build_SetoidMorphism _ _ _ _ (fun (g : O ~> a) => f ∘ g) _.
Next Obligation.
  repeat intro. rewrite H1. reflexivity. Qed.

Global Program Instance : Functor HOM_F hom_fmap.
Next Obligation.
  (* fmap id == id *)
  apply id_r. Qed.
Next Obligation.
  (* fmap (g . f) == fmap g . fmap f *)
  unfold compose. symmetry. apply comp_assoc.
  Qed.
Next Obligation.
  (* fmap respects equivalence *)
  repeat intro. simpl.
  rewrite H1. reflexivity.
  Qed.  

End hom_functor.

