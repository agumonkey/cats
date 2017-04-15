(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Cat: Category Theory with classes.
 *
 * This module defines functors and some standard instances.
 * 
 * Author: Matthieu Sozeau <mattam@mattam.org>
 *)

Set Implicit Arguments.
Unset Strict Implicit.


Require Export Cat.Category.

Require Import Coq.Program.Tactics.
Obligation Tactic := program_simpl ; auto with category.

(** Definition of a [Functor] between two categories with its two components, on objects and morphisms.
   We keep them as parameters because they are an essential part of the definition and we will quantify on them
   and mention them in later specifications. *)

Class  Functor `(C : Category obj hom, D : Category obj' hom') 
  (Fobj : obj -> obj') (Fmor : forall a b, hom a b -> hom' (Fobj a) (Fobj b) ) := {
  functor_map_morphism :> forall a b, Morphism (equiv ++> equiv) (Fmor a b) ;

  preserve_ident : forall a, Fmor a a id == id ;
  
  preserve_assoc : forall a b c (f : hom a b) (g : hom b c), 
    Fmor a c (compose f g) == Fmor b c g ∘ Fmor a b f
}.

Implicit Arguments Functor [obj hom obj' hom'].

Program Instance identity_Functor `(C : Category obj hom) : 
  Functor C C Datatypes.id (fun a b => Datatypes.id).

  Solve Obligations using program_simpl ; unfold Datatypes.id ; try reflexivity.

(** Class Abbreviations needed ? Fundep problem : the obj and hom should uniquely determine the category ? *)

Class EndoFunctor `( Functor obj hom obj hom Fobj Fmor).

Definition endo_functor obj hom c Fobj Fmor : _ := @Functor obj hom c obj hom c Fobj Fmor.

(** A Natural Transformation is determined by an [eta] component for each object of the domain category giving
   a morphism in the codomain category between the images of the object by the two functors. *)  

Class NaturalTransformation 
  `( C : Category obj hom, D : Category obj' hom', 
     CD : ! Functor C D Fobj F, DC : ! Functor C D Gobj G)
:= {
  eta : forall ob : obj, hom' (Fobj ob) (Gobj ob) ;
  eta_law : forall a b (f : hom a b), eta b ∘ F a b f == G a b f ∘ eta a
}.

(** Bijection is invertibility of a function, here we do it up to setoids. *)

Definition bijective `(Setoid A, Setoid B) (f : A -> B) : _ := 
  forall y, { x : A | f x == y /\ forall z : A, f z == y -> x == z }.
Implicit Arguments bijective [A H B H0].

(** Finally, the concept of an adjunction between two functors is defined. It is an isomorphism
   between the section by F of the homset of category C and the points category induced by G in D. 
   Hopefully we'll have an example of a useful adjunction in the examples below... 
   For now it just demonstrates how we might define complex constructions using this system.
   *)

Class Adjunction `(C : Category obj hom, D : Category obj' hom',
                   F : !Functor C D Fobj Fm, G : !Functor D C Gobj Gm) := {
  phi : forall (x : obj) (y : obj'),
    hom x (Gobj y) -> hom' (Fobj x) y;
    
  phi_law : forall x y, bijective (@phi x y)
}.

(** Constructions to hide the Fobj and Fmor components. *)
Notation "( x & y )" := (@existT _ _ x y) : core_scope.

Definition functor (c d : category) :=
  let (obj, hom, cat) := c in
  let (obj', hom', cat') := d in
    { Fobj : obj -> obj' &
      { Fmor : forall a b : obj, hom a b -> hom' (Fobj a) (Fobj b) &
        Functor cat cat' Fobj Fmor } }.

Definition identity_functor (c : category) : functor c c :=
  match c with mkCat obj hom categ =>
    (Datatypes.id & (fun a b : obj => Datatypes.id & identity_Functor categ))
  end.

Instance composition_morphism  (A B C : Type) 
  `(m : !Morphism (R' ++> R'') (g : B -> C))
  `(n : !Morphism (R ++> R') (f : A -> B))
  : Morphism (R ++> R'') (g ∘ f)%prg.
Proof.
  do 2 red ; intros.
  unfold Basics.compose.
  apply (respect (Morphism:=m)).
  apply (respect (Morphism:=n)).
  assumption.
Qed.

Implicit Arguments composition_morphism [A B C R' R'' g m R f n]. 


Ltac setoid_refl := 
  match goal with
    | [ |- @equiv ?A ?s ?x _ ] => apply (@reflexive A (@equiv A s) (@setoid_refl A s) x)
    | [ |- @JMeq ?A ?x _ _ ] => apply JMeq_refl
  end.

Ltac reflex := setoid_refl || reflexivity.

Program Instance composed_Functor 
  `( C : Category obj₁ hom₁, D : Category obj₂ hom₂, E : Category obj₃ hom₃,
     F : !Functor C D fobj fmor, G : !Functor D E gobj gmor )
  : Functor C E (gobj ∘ fobj)%prg
    (fun a b => gmor (fobj a) (fobj b) ∘ fmor a b)%prg.

  Next Obligation.
  Proof.
    do 2 red ; intros.
    pose (functor_map_morphism (Functor:=F)).
    pose (functor_map_morphism (Functor:=G)).
    pose (composition_morphism (m:=m0 (fobj a) (fobj b)) (n:=m a b)).
    apply (respect (Morphism:=m1)).
    assumption.
  Qed.
  
  Next Obligation.
  Proof.
    intros.
    pose (functor_map_morphism (Functor:=F)). 
    pose (functor_map_morphism (Functor:=G)).
    unfold Basics.compose.
    rewrite (preserve_ident a). 
    rewrite (preserve_ident (fobj a)).
    reflex.
  Qed.

  Next Obligation.
  Proof.
    pose (functor_map_morphism (Functor:=F)) as Fm. 
    pose (functor_map_morphism (Functor:=G)) as Gm.
    unfold Basics.compose.
    rewrite (preserve_assoc f g).
    apply (preserve_assoc (fmor a b f) (fmor b c g)).
  Qed.
Implicit Arguments composed_Functor [obj₁ hom₁ obj₂ hom₂ obj₃ hom₃ fobj fmor gobj gmor C D E F G].

Definition functor_composition (c d e : category) : functor c d -> functor d e -> functor c e := 
  match c, d, e with
    | mkCat obj₁ hom₁ cat₁,
      mkCat obj₂ hom₂ cat₂,
      mkCat obj₃ hom₃ cat₃ =>
      fun f g =>
        let '(Fobj & (Fmor & F)) := f in
        let '(Gobj & (Gmor & G)) := g in
          (_ & (_ & composed_Functor (F:=F) (G:=G)))
  end.

Definition subst_hom {obj hom} {C : Category obj hom} {objorig} (f g : objorig -> obj)
  {a b} (p : f = g) (m : hom (f a) (f b)) : hom (g a) (g b).
Proof. intros ; subst. exact m. Defined.


Definition functor_equality {c d : category} : functor c d -> functor c d -> Prop :=
  match c, d return relation (functor c d) with
    | mkCat obj₁ hom₁ cat₁,
      mkCat obj₂ hom₂ cat₂ =>
      fun f g =>
        let '(Fobj & (Fmor & F)) := f in
        let '(Gobj & (Gmor & G)) := g in
          exists H : Fobj = Gobj, JMeq Fmor Gmor
  end.

Definition functor_equivalence (c d : category) : Equivalence (@functor_equality c d).
Proof.
  intros [obj₁ hom₁ cat₁]. 
  intros [obj₂ hom₂ cat₂].

  simpl.
  constructor ; red ; try red ; intros.
  destruct x as [Fobj [Fmor F]] ; simpl.
  exists (refl_equal Fobj). 
  reflex.

  destruct x as [Fobj [Fmor F]] ; simpl.
  destruct y as [Gobj [Gmor G]] ; simpl.
  destruct H. exists (sym_eq x). now symmetry.

  destruct x as [Fobj [Fmor F]] ; simpl.
  destruct y as [Gobj [Gmor G]] ; simpl.
  destruct z as [Iobj [Imor I]] ; simpl.
  destruct_conjs. split_dep. now transitivity Gobj.
  eapply trans_JMeq; eauto.
Qed.

(* Definition functor_equality {c d : category} : functor c d -> functor c d -> Prop := *)
(*   match c, d return relation (functor c d) with *)
(*     | mkCat obj₁ hom₁ cat₁, *)
(*       mkCat obj₂ hom₂ cat₂ => *)
(*       fun f g => *)
(*         let '(Fobj & (Fmor & F)) := f in *)
(*         let '(Gobj & (Gmor & G)) := g in *)
(*           exists H : Gobj = Fobj, *)
(*             forall a b (m : hom₁ a b), equiv (A:=hom₂ (Fobj a) (Fobj b)) (Fmor _ _ m)  *)
(*               (subst_hom (C:=cat₂) H (Gmor _ _ m)) *)
(*   end. *)

(* Definition functor_equivalence (c d : category) : Equivalence (@functor_equality c d). *)
(* Proof. *)
(*   intros [obj₁ hom₁ cat₁].  *)
(*   intros [obj₂ hom₂ cat₂]. *)

(*   simpl. *)
(*   constructor ; red ; try red ; intros. *)
(*   destruct x as [Fobj [Fmor F]] ; simpl. *)
(*   exists (refl_equal Fobj).  *)
(*   reflex. *)

(*   destruct x as [Fobj [Fmor F]] ; simpl. *)
(*   destruct y as [Gobj [Gmor G]] ; simpl. *)
(*   destruct H. exists (sym_eq x). intros. *)
(*   move x at top. *)
(*   generalize dependent Fobj. simplify_dep_elim.  *)
(*   specialize (H a b m). unfold subst_hom in *; simpl in *. *)
(*   unfold eq_rect_r in *. simpl in *. rewrite H. reflex. *)
    
(*   destruct x as [Fobj [Fmor F]] ; simpl. *)
(*   destruct y as [Gobj [Gmor G]] ; simpl. *)
(*   destruct z as [Iobj [Imor I]] ; simpl. *)
(*   destruct_conjs. move H at top; move H0 at top. generalize dependent obj₁.  *)
(*   simplify_dep_elim. unfold subst_hom, eq_rect_r in *. simpl in *.  *)
(*   exists (refl_equal Iobj). simpl. intros. rewrite H2, H1. reflex. *)
(* Qed. *)

Program Instance functor_setoid (a b : category) : Setoid (functor a b) := {
  equiv := functor_equality
}.

  Next Obligation.
    apply functor_equivalence.
  Qed.
