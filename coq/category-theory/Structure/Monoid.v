Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section MonoidObject.

Context {C : Category}.
Context `{@Monoidal C}.

Class MonoidObject (mon : C) := {
  mempty  : I ~> mon;
  mappend : mon ⨂ mon ~> mon;

  (* I ⨂ mon ≈ mon, mon ⨂ I ≈ mon *)
  mempty_left : mappend ∘ bimap mempty id ≈ to (@unit_left C _ mon);
  mempty_right : mappend ∘ bimap id mempty ≈ to (@unit_right C _ mon);

  (* (mon ⨂ mon) ⨂ mon ≈ mon ⨂ (mon ⨂ mon) *)
  mappend_assoc :
    mappend ∘ bimap mappend id ≈ mappend ∘ bimap id mappend ∘ to tensor_assoc
}.

End MonoidObject.

Notation "mempty[ M ]" := (@mempty _ _ _ M)
  (at level 9, format "mempty[ M ]") : category_scope.
Notation "mappend[ M ]" := (@mappend _ _ _ M)
  (at level 9, format "mappend[ M ]") : category_scope.
