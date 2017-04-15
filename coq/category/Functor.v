Require Export Category.

Generalizable All Variables.
Open Scope signature.

Section functor.

Context `{Category C} `{Category D}.

(* The functor class is defined by a function 'F' that maps objects
   to objects and a function 'fmap' that maps morphisms to morphisms *)
Class Functor (F: C -> D) 
  (fmap : forall {a b: C}, (a ~> b) -> (F a ~> F b)) :=
  { (* fmap must preserve the identity arrow *)
    fmap_preserve_id : forall {a}, 
    fmap (cat_id : a ~> a) == (cat_id : (F a ~> F a))
    (* fmap must respect the composition operator *)
  ; fmap_respects_comp : forall `(f: a ~> b) `(g : b ~> c),
    fmap (g ∘ f) == fmap g ∘ fmap f
    (* fmap must respect the equivalence relation *) 
  ; fmap_proper :> forall {a b : C} , Proper (equiv ==> equiv) (@fmap a b)
  }.

End functor.

Section id_functor.
Context `(Category C).

Global Program Instance : Functor (id : C -> C) (fun _ _ => id).
Solve Obligations using try(reflexivity).
Next Obligation.
  repeat intro. unfold id. assumption.
  Qed.

End id_functor.
