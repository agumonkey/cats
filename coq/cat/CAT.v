(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Cat: Category Theory with classes.
 *
 * This module implements the category [CAT] of categories and functors.
 * 
 * Author: Matthieu Sozeau <mattam@mattam.org>
 *)

Require Import Coq.Program.Program.
Require Import SetoidClass.
Require Import Setoid.
Require Import Cat.Functor.

Typeclasses Transparent Datatypes.id.

Program Instance CAT : Category category functor := {
  morphisms := functor_setoid ;
  id := identity_functor ;
  compose := functor_composition
}.

  Next Obligation.
  Proof.
    revert a.
    intros [obj₁ hom₁ cat₁]. 
    do 2 red ; simpl.

    split_dep; reflex.
  Qed.

  Next Obligation.
  Proof.
    revert a b c.
    intros [obj₁ hom₁ cat₁]. 
    intros [obj₂ hom₂ cat₂].
    intros [obj₃ hom₃ cat₃].
    do 2 red. 
    intros [Fobj [Fmor F]].
    intros [Gobj [Gmor G]].
    intros Heq.
    red.
    intros [Fobj' [Fmor' F']].
    intros [Gobj' [Gmor' G']].
    simpl.

    simpl in Heq.
    intros. destruct_conjs.
    subst ; simpl_JMeq ; subst.
    split_dep ; reflex.
  Qed.

  Next Obligation.
  Proof.
    revert a b f.
    intros [obj₁ hom₁ cat₁]. 
    intros [obj₂ hom₂ cat₂].
    intros [Fobj [Fmor F]].
    
    simpl.
    split_dep.
      apply compose_id_left.
      unfold Datatypes.id, Basics.compose.
      apply eq_eqdep.
      extensionality a ; extensionality b ; extensionality h.
      reflex.
  Qed.

  Next Obligation.
  Proof.
    revert a b f.
    intros [obj₁ hom₁ cat₁]. 
    intros [obj₂ hom₂ cat₂].
    intros [Fobj [Fmor F]].
    
    simpl.
    split_dep.
      apply compose_id_right.
      unfold Datatypes.id, Basics.compose.
      apply eq_eqdep.
      extensionality a ; extensionality b ; extensionality h.
      reflex.
  Qed.

  Next Obligation.
  Proof.
    revert a b c d f g h.
    intros [obj₁ hom₁ cat₁]. 
    intros [obj₂ hom₂ cat₂].
    intros [obj₃ hom₃ cat₃].
    intros [obj₄ hom₄ cat₄].
    intros [Fobj [Fmor F]].
    intros [Gobj [Gmor G]].
    intros [Hobj [Hmor H]].

    simpl.
    split_dep. 
      apply compose_assoc.

      unfold Datatypes.id, Basics.compose.
      apply eq_eqdep.
      reflex.
  Qed.

