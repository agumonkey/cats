(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Cat: Category Theory with classes.
 *
 * This module implements the category [TYPE] of Types and Coq function spaces
 * between them.
 * 
 * Author: Matthieu Sozeau <mattam@mattam.org>
 *)


Require Import Cat.Functor.
Require Import Coq.Classes.SetoidTactics.

(** The [arrow] homset takes Type's [A] and [B] to the [A -> B] function space. *)

Definition arrow A B := A -> B.

(** Here we build a setoid instance for functions which relates the ones which argree on every input. *)

Program Instance arrow_setoid `(s : Setoid b) : Setoid (a -> b) := {
  equiv f g := forall x, f x == g x
}.
Next Obligation.
Proof.
  constructor ; red ; intros.
  reflexivity.

  symmetry ; auto.
  
  transitivity (y x0) ; auto.
Qed.
Implicit Arguments arrow_setoid [a b s].

(** Not an instance, would make any setoid constraint trivial. *)
Program Definition eq_setoid A : Setoid A :=
  @Build_Setoid A (@Logic.eq A) _.

Next Obligation.
  apply eq_equivalence.
Qed.

(** We can build the corresponding category of types and functions (our Set category) from [arrow_setoid]. *)

Program Instance TYPE : Category Type arrow := {
  morphisms a b := arrow_setoid (s:=eq_setoid b) ;
  id a x := x;
  compose a b c f g x := g (f x)
}.

  Next Obligation.
  Proof.
    unfold arrow.
    constructor ; intros.
  Qed.

  Next Obligation.
  Proof.
    do 3 (red ; intros).
    rewrite (H x1).
    rewrite (H0 (y x1)).
    reflexivity.
  Qed.

(** Some interesting endo-functors in this category: *)

Require Import Coq.Lists.List.

(** Lists with map. *)

(* Program Instance list_map_functor : Functor TYPE TYPE list map. *)

(*   Next Obligation. *)
(*   Proof. *)
(*     do 2 red ; intros. *)
(*     induction x0 ; auto. *)
(*     simpl. *)
(*     rewrite IHx0. *)
(*     rewrite H.  *)
(*     reflexivity. *)
(*   Qed. *)

(*   Next Obligation. *)
(*   Proof. *)
(*     induction x ; auto. *)
(*     simpl ; rewrite IHx. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Next Obligation. *)
(*   Proof. *)
(*     induction x ; auto. *)
(*     simpl ; rewrite IHx. *)
(*     reflexivity. *)
(*   Qed. *)

(** The option map. *)

(* Program Instance option_functor : Functor TYPE TYPE option *)
(*   (fun a b f x => match x return _ with Some a => Some (f a) | None => None end). *)
  
(*   Next Obligation. *)
(*   Proof. *)
(*     do 2 red ; intros. *)
(*     induction x0 ; auto. *)
(*     f_equal. *)
(*     apply H. *)
(*   Qed. *)
  
(*   Next Obligation. *)
(*   Proof. *)
(*     destruct x ; auto. *)
(*   Qed. *)
  
(*   Next Obligation. *)
(*   Proof. *)
(*     destruct x ; auto. *)
(*   Qed. *)

(** Representation functors. *)

Require Import Coq.Classes.SetoidAxioms.

(** The section functor, or covariant functor for any category [C] on an object [A]. *)

Program Instance section_functor `(C : Category obj hom, ! Object C a ) : 
  Functor C TYPE (hom a) (fun x y (f : hom x y) (g : hom a x) => f ∘ g).

  Next Obligation.
  Proof.
    do 2 red ; intros.
    (* BUG when using H and no extensionality *)
    setoid_extensionality.
    rewrite H.
    reflex.
  Qed.
  
  Next Obligation.
  Proof.
    setoid_extensionality.
    apply id_unit_left.
  Qed.
  
  Next Obligation.
  Proof.
    setoid_extensionality.
    apply assoc.
  Qed.
  
(** The points functor, or contravariant functor induced by an object [b] into [opposite Type] for any category [C]. *)

Class ContravariantFunctor `(C : Category (opposite obj) (flip hom), D : Category obj' hom' ) Fobj Fmor := {
  contravariant_functor :> Functor C D Fobj Fmor
}.

(* Definition ContravariantFunctor [ C : Category (opposite obj) (flip hom), D : Category obj' hom' ] Fobj Fmor :=  *)
(*   Functor C D Fobj Fmor. *)

(* Typeclasses unfold SetoidClass.equiv. *)
(* Typeclasses unfold flip. *)
(* Typeclasses unfold @opposite. *)

Program Instance points_functor `(Cop : Category (opposite obj) (flip hom), ! Object Cop b ) :
  Functor Cop TYPE ((flip hom) b) (fun x y (f : (flip hom) x y) (g : (flip hom) b x) => f ∘ g).

  Next Obligation.
  Proof.
    do 2 red ; intros.
    setoid_extensionality.
    rewrite H. reflexivity.
  Qed.
  
  Next Obligation.
  Proof.
    setoid_extensionality.
    apply id_unit_left.
  Qed.
  
  Next Obligation.
  Proof.
    setoid_extensionality.
    apply assoc.
  Qed.

