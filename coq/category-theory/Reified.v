Require Import Lib.
Require Export BiCCC.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Inductive Obj : Type :=
  | One_    : Obj
  | Prod_   : Obj -> Obj -> Obj
  | Exp_    : Obj -> Obj -> Obj
  | Zero_   : Obj
  | Coprod_ : Obj -> Obj -> Obj.

Fixpoint denote `(o : Obj) :
  ∀ `{C : Category}
    `{A : @Cartesian C}
    `{@Closed C A}
    `{@Cocartesian C}
    `{@Terminal C}
    `{@Initial C}, C := fun _ _ _ _ _ _ =>
  match o with
  | One_        => One
  | Prod_ x y   => denote x × denote y
  | Exp_ x y    => denote y ^ denote x
  | Zero_       => Zero
  | Coprod_ x y => denote x + denote y
  end.

Inductive Hom : Obj -> Obj -> Type :=
  | Id      : ∀ {a}, Hom a a
  | Compose : ∀ {a b c}, Hom b c -> Hom a b -> Hom a c

  | One'    : ∀ {a}, Hom a One_

  | Exl     : ∀ {a b}, Hom (Prod_ a b) a
  | Exr     : ∀ {a b}, Hom (Prod_ a b) b
  | Fork    : ∀ {a c d}, Hom a c -> Hom a d -> Hom a (Prod_ c d)

  | Curry   : ∀ {a b c}, Hom (Prod_ a b) c -> Hom a (Exp_ b c)
  | Uncurry : ∀ {a b c}, Hom a (Exp_ b c) -> Hom (Prod_ a b) c

  | Zero'   : ∀ {a}, Hom Zero_ a

  | Inl     : ∀ {a b}, Hom a (Coprod_ a b)
  | Inr     : ∀ {a b}, Hom b (Coprod_ a b)
  | Merge   : ∀ {a c d}, Hom c a -> Hom d a -> Hom (Coprod_ c d) a.

Program Fixpoint interp `(c : Hom a b) :
  ∀ `{C : Category}
    `{A : @Cartesian C}
    `{@Closed C A}
    `{@Cocartesian C}
    `{@Terminal C}
    `{@Initial C}, denote a ~{C}~> denote b := fun _ _ _ _ _ _ =>
  match c with
  | Id          => id
  | Compose f g => interp f ∘ interp g

  | One'        => one

  | Exl         => exl
  | Exr         => exr
  | Fork f g    => fork (interp f) (interp g)

  | Curry f     => curry (interp f)
  | Uncurry f   => uncurry (interp f)

  | Zero'       => zero

  | Inl         => inl
  | Inr         => inr
  | Merge f g   => merge (interp f) (interp g)
  end.

Local Obligation Tactic := simpl; intros; auto; cat.

Program Instance DSL : Category := {
  hom := Hom;
  id := @Id;
  compose := @Compose;
  eqv := fun _ _ f g =>
           forall `{C : Category}
                  `{A : @Cartesian C}
                  `{@Closed C A}
                  `{@Cocartesian C}
                  `{@Terminal C}
                  `{@Initial C},
             @eqv C _ _ (interp f) (interp g)
}.
Obligation 1.
  constructor.
  - intros ??????.
    reflexivity.
  - intros ????????.
    symmetry.
    apply H.
  - intros ??? HA HB ??????.
    rewrite HA, HB.
    reflexivity.
Defined.
Obligation 2.
  intros ?? HA ?? HB ??????.
  simpl.
  rewrite HA, HB.
  reflexivity.
Qed.
Obligation 5.
  rewrite comp_assoc.
  reflexivity.
Qed.

Program Instance Hom_Terminal : @Terminal _ := {
  One := One_;
  one := @One'
}.

Program Instance Hom_Cartesian : @Cartesian _ := {
  Prod := Prod_;
  fork := @Fork;
  exl  := @Exl;
  exr  := @Exr
}.
Obligation 1.
  intros ?? HA ?? HB ?? ????.
  simpl.
  rewrite HA, HB.
  reflexivity.
Qed.
Obligation 2.
  split; intros HA.
    split; intros; rewrite HA; cat.
  intros.
  destruct HA as [HA HB].
  rewrite <- HA, <- HB.
  rewrite fork_comp; cat.
Qed.

Program Instance Hom_Closed : @Closed _ _ := {
  Exp := Exp_;
  curry := @Curry;
  uncurry := @Uncurry
}.
Obligation 1.
  constructor; simpl; intros; cat.
  - intros ?? HA ??????.
    simpl.
    rewrite HA.
    reflexivity.
  - intros ?? HA ??????.
    simpl.
    rewrite HA.
    reflexivity.
Defined.

Program Instance Hom_Initial : @Initial _ := {
  Zero := Zero_;
  zero := @Zero'
}.

Program Instance Hom_Cocartesian : @Cocartesian _ := {
  Coprod  := Coprod_;
  merge := @Merge;
  inl  := @Inl;
  inr  := @Inr
}.
Obligation 1.
  intros ?? HA ?? HB ??????.
  simpl.
  rewrite HA, HB.
  reflexivity.
Qed.
Obligation 2.
  split; intros HA.
    split; intros; rewrite HA; cat.
  intros.
  destruct HA as [HA HB].
  rewrite <- HA, <- HB.
  rewrite merge_comp; cat.
Qed.

Section Reified.

Context `{C : Category}.
Context `{A : @Cartesian C}.
Context `{@Closed C A}.
Context `{@Cocartesian C}.
Context `{@Terminal C}.
Context `{@Initial C}.

Local Obligation Tactic :=
  simpl; intros; auto; cat; try reflexivity; auto.

Global Program Instance Hom_Functor : DSL ⟶ C := {
  fobj := fun x => denote x;
  fmap := fun _ _ f => interp f
}.

Global Program Instance Hom_TerminalFunctor : TerminalFunctor := {
  map_one := id
}.

Global Program Instance Hom_CartesianFunctor : CartesianFunctor := {
  fobj_prod_iso := _
}.

Global Program Instance Hom_ClosedFunctor : ClosedFunctor := {
  fobj_exp_iso := _
}.

Global Program Instance Hom_InitialFunctor : InitialFunctor := {
  map_zero := id
}.

Global Program Instance Hom_CocartesianFunctor : CocartesianFunctor := {
  fobj_coprod_iso := _
}.

End Reified.
