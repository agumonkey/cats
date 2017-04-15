Require Export Coq.Classes.Morphisms.
Export Coq.Classes.Morphisms.ProperNotations.
Require Export Coq.Classes.SetoidClass.

Generalizable All Variables.
Open Scope signature.

(* A separate class for arrows allows for easy and liberal use of notation *)
Class Arrows (X: Type) : Type := Hom : X -> X -> Type.
Infix "~>" := Hom (at level 90, right associativity).

(* Typeclass for categories *)
Class Category Obj `{Arrows Obj} := 
  { (* Hom-sets have to be setoids, e.g. each hom-set has to be 
       equiped with an equivalence relation *)
    arrows_setoid :> forall x y, Setoid (x ~> y)
    
    (* Morphisms must be composable .. *)
  ; comp : forall {x y z}, `(y ~> z) -> `(x ~> y) -> (x ~> z)
    (* .. and the composition has to be associative *)
  ; comp_assoc : forall `(f : a ~> b) `(g : b ~> c) `(h : c ~> d),
    comp h (comp g f) == comp (comp h g) f
    (* Additionally the composition operator has to respect the 
       equivalence relations *)
  ; comp_proper :> forall a b c, Proper (equiv ==> equiv ==> equiv) (@comp a b c)

    (* Each hom-set must contain an id arrow *)
  ; cat_id : forall {a}, a ~> a
    (* .. that respects certain laws *)
  ; id_l : forall `(f : a ~> b), comp f cat_id == f
  ; id_r : forall `(f : a ~> b), comp cat_id f == f
  }.

Notation " x '∘' y " := (comp x y) (at level 40, left associativity).
