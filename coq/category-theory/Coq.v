Require Import Lib.
Require Export BiCCC.
Require Export Morphisms.
Require Export Constant.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Program Instance Coq : Category := {
  ob      := Type;
  hom     := fun A B : Type => A -> B;
  id      := fun _ x => x;
  compose := fun _ _ _ g f x => g (f x);
  eqv     := fun _ _ f g => forall x, f x = g x
}.
Obligation 1.
  constructor.
  - intros ??; auto.
  - intros ????; auto.
  - intros ??????; congruence.
Defined.
Obligation 2.
  intros ?? HA ?? HB ?.
  rewrite HA, HB.
  reflexivity.
Defined.

Program Instance Coq_Terminal : @Terminal _ := {
  One := unit : Type;
  one := fun _ a => tt
}.
Obligation 1.
  destruct (f x), (g x).
  reflexivity.
Qed.

Program Instance Coq_Cartesian : @Cartesian _ := {
  Prod := prod;
  fork := fun _ _ _ f g x => (f x, g x);
  exl  := fun _ _ p => fst p;
  exr  := fun _ _ p => snd p
}.
Obligation 1.
  intros ?? HA ?? HB ?.
  rewrite HA, HB.
  reflexivity.
Defined.
Obligation 2.
  split; intros Hcart; subst.
    split; intros;
    rewrite Hcart; reflexivity.
  destruct Hcart as [HA HB].
  subst; intros.
  rewrite <- HA, <- HB.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.

Program Instance Coq_Closed : @Closed _ _ := {
  Exp := fun A B : Type => A -> B;
  curry := fun _ _ _ f a b => f (a, b);
  uncurry := fun _ _ _ f p => f (fst p) (snd p)
}.
Obligation 1.
  constructor; intros; simpl; auto.
  - intros.
    rewrite <- surjective_pairing.
    reflexivity.
  - intros ?? HA ?.
    extensionality b.
    rewrite HA.
    reflexivity.
  - intros ?? HA ?.
    rewrite HA.
    reflexivity.
Defined.

Program Instance Coq_Initial : Initial _ := {
  Zero := False;
  zero := fun _ _ => False_rect _ _
}.
Obligation 2. contradiction. Qed.

Program Instance Coq_Cocartesian : @Cocartesian _ := {
  Coprod := sum;
  merge := fun _ _ _ f g x =>
            match x with
            | Datatypes.inl v => f v
            | Datatypes.inr v => g v
            end;
  inl  := fun _ _ p => Datatypes.inl p;
  inr  := fun _ _ p => Datatypes.inr p
}.
Obligation 1.
  intros ?? HA ?? HB ?.
  destruct x1.
    rewrite HA; reflexivity.
  rewrite HB; reflexivity.
Defined.
Obligation 2.
  split; intros Hcocart; subst.
    split; intros;
    rewrite Hcocart; reflexivity.
  destruct Hcocart.
  subst; simpl; intros.
  destruct x; auto.
Qed.

Program Instance Coq_Constant : @Constant _ _ := {
  Const := fun A => A;
  constant := fun _ => Basics.const
}.

Lemma injectivity_is_monic `(f : X ~> Y) :
  (∀ x y, f x = f y → x = y) ↔ Monic f.
Proof. split.
- intros.
  autounfold in *; intros.
  simpl in *; intros.
  apply H.
  apply H0.
- intros.
  autounfold in *.
  simpl in *.
  pose (fun (_ : unit) => x) as const_x.
  pose (fun (_ : unit) => y) as const_y.
  specialize (H unit const_x const_y).
  unfold const_x in H.
  unfold const_y in H.
  simpl in H.
  apply H; intros.
    assumption.
  exact tt.
Qed.

Lemma surjectivity_is_epic `(f : X ~> Y) :
  (∀ y, ∃ x, f x = y)%type ↔ Epic f.
Proof. split.
- intros.
  autounfold in *; intros.
  simpl in *; intros.
  specialize (H x).
  destruct H.
  rewrite <- H.
  apply H0.
- intros.
  unfold Epic in H.
  specialize H with (Z := Prop).
  specialize H with (g1 := fun y0 => (∃ x0, f x0 = y0)%type).
  simpl in *.
  specialize H with (g2 := fun y  => True).
  erewrite H. constructor.
  intros.
  apply propositional_extensionality.
  exists x.
  reflexivity.
Qed.
