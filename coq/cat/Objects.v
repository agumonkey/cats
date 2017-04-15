(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Cat: Category Theory with classes.
 *
 * This module defines standard notions on objects in a category.
 * 
 * Author: Matthieu Sozeau <mattam@mattam.org>
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Program.Program.

Require Export Cat.Category.

Require Import Coq.Classes.SetoidClass.
Require Import Coq.Classes.Functions.

(** Example definition of a predicate on objects _in_ a particular category. *)

Definition terminal `(cat : Category obj hom) (x : obj) : Type :=  
  forall y, { f : hom y x & forall f g : hom y x, f == g }.

(** The same using a Class instead.
   Only the object and the category are needed, [obj] and [hom] are implicit. *)

Class Terminal `(cat : Category obj hom )  (one : obj) := {
  bang : forall x, hom x one ;
  unique : forall x (f g : hom x one), f == g
}.
Implicit Arguments Terminal [obj hom].

(** Two objects are isomorphic if the morphism between them are unique and inverses. *)

Definition isomorphic `(cat : Category obj hom) a b : _ :=
  { f : hom a b & { g : hom b a |
    f ∘ g == id /\ g ∘ f == id } }.
Implicit Arguments isomorphic [obj hom cat].

(** A proof using abstract instances of typeclasses, no explicitation needed whatsoever. *)

(* begin show *)
Lemma terminal_isomorphic `(C : Category obj hom, ! Terminal C x, ! Terminal C y) : isomorphic x y.
Proof.
  intros.
  unfold isomorphic in *.
  exists (bang (one:=y) x).
  exists (bang (one:=x) y). (* eauto not using constraint from the goal, we can always drive a little if needed *)
  intuition. 
  apply unique.
  apply unique.
Qed.
(* end show *)

(** Isomorphism again, class-style. *)

Class Isomorphic `(C : Category obj hom) (a : obj) (b : obj) := {
  isomorphisms : { f : hom a b & { g : hom b a |
    f ∘ g == id /\ g ∘ f == id } }
}.
