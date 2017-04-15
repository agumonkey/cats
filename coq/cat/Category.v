(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Cat: Category Theory with classes.
 *
 * This module defines categories and some standard instances.
 * 
 * Author: Matthieu Sozeau <mattam@mattam.org>
 *)

Set Implicit Arguments.
Unset Strict Implicit.

(** We first define setoids on a carrier, it amounts to an equivalence relation. 
   Now [equiv] is overloaded for every [Setoid].
*)

Require Export Coq.Program.Program.

(** This declares a [Setoid] for any [A] type (implicit quantification is going on as before).
   This means that every [Setoid] constraint will be trivially satisfied by this instance so we better
   add more specific instances after this one to get a finer definition. *)

Require Export Setoid.
Require Export Coq.Classes.SetoidClass.
Require Export Coq.Classes.Functions.

Instance id_morphism `(A : Type) `(R : relation A) : Morphism (R ++> R) id.
Proof. do 2 red ; intuition. Qed.

Hint Resolve id_morphism : category.

(** The type of homsets of objects of type [A] *)

Definition homomorphisms A := A -> A -> Type.

(** A [Category] is a set of objects and morphisms with a distinguished [id] morphism and a 
   [compose] law satisfiying the monoid laws. We use setoids for objects and morphisms because we may
   want to redefine equality, e.g. to use extensional equality for functions. *)

Class Category obj (hom : homomorphisms obj) := {
  (* For nicer, user defined equalities. *)
  morphisms :> forall a b : obj, Setoid (hom a b) ;

  (* Definitional components: the id_A arrow and composition. *)
  id : forall {a}, hom a a;
    
  id_morphisms_morphism :> forall a, Morphism equiv (id (a:=a)) ;
    
  compose : forall {a b c}, hom a b -> hom b c -> hom a c;

  compose_morphism :> forall a b c, 
    Morphism (equiv ==> equiv ==> equiv) 
    (@compose a b c) ;
  
  (* Laws (composition reverses the arguments, hence the names) *)
  id_unit_left  : forall a b (f : hom a b), compose f id == f;

  id_unit_right : forall a b (f : hom a b), compose id f == f;

  assoc : forall a b c d (f : hom a b) (g : hom b c) (h : hom c d),
    compose f (compose g h) == compose (compose f g) h
}.

Implicit Arguments Category [].

(** Overloaded composition operator. *)

Notation " x '∘' y " := (compose y x) (at level 40, left associativity).

Hint Resolve @id_morphisms_morphism @id_unit_left @id_unit_right @assoc : category.

(** Definining the opposite category by reversing the arrows. *)

(** [opposite X] takes the opposite of the object's set: itself. *)

Definition opposite (X : Type) := X.

(** Adding hints because [opposite obj] is convertible to [obj], and [(flip hom) x x] is convertible to [hom x x].
   When we use [id] against the goal [forall a : opposite obj, Hom a a], we have to find an instance
   of [Category (opposite obj) (flip hom)] (which we are actually building), hence we have an unsolvable contraint.
   But we know we can use the [id] definition on the [Category obj hom] as [forall a : opposite obj, (flip hom) a a] is 
   convertible to [forall a : obj, hom a a] hence the forcing suffices. Similarly for compose, the unspecialized
   compose instance is too general but the constrained one is ok due to conversions. *)

Program Instance opposite_category `(cat :  Category obj hom )  : Category (opposite obj) (flip hom) := {
  morphisms a b := morphisms b a ;
  id a := id (hom := hom) ;
  compose a b c := flip (compose (hom:=hom))
}.

  Solve Obligations using unfold flip in * ; program_simpl; auto with category.
  
  Next Obligation.
  Proof.
    do 3 (red ; intros).
    unfold flip in *.
    setoid_rewrite H.
    clrewrite H0.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    unfold flip in *.
    symmetry ; apply assoc.
  Qed.

Record category := mkCat {
  objs : Type ;
  homs : homomorphisms objs ;
  cat : Category objs homs }.

Definition category_equality (c d : category) : Prop :=
  let 'mkCat obj₁ hom₁ cat₁ := c in
  let 'mkCat obj₂ hom₂ cat₂ := d in
    obj₁ = obj₂ /\ JMeq hom₁ hom₂.

Instance category_equality_equivalence : Equivalence category_equality.
Proof. constructor ; do 2 red ; intros.
  destruct x ; simpl.
  split ; subst ; auto.

  destruct x ; destruct y ; simpl.
  red in H.
  intuition.

  destruct x ; destruct y ; destruct z ; simpl.
  red in H, H0.
  intuition ; subst ; auto.
  simpl_JMeq.
  subst ; auto.
Qed.

Hint Resolve category_equality_equivalence.

(** We first need to show that every type constructor is a morphism for leibiniz [eq]. *)

Instance type_constructor_morphism (T : Type -> Type) : Morphism (eq ++> eq) T.
Proof. 
  do 2 red; intros.
  refine (match H in eq _ y return T x = T y with
            refl_equal => refl_equal (T x)
          end).
Qed.

Ltac split_dep := 
  match goal with
    [ |- ex (fun _ : ?H => _) ] => let hyp := fresh "H" in assert (hyp:H) ; [ idtac | exists hyp ]
  end.

Lemma eq_eqdep : forall (A : Type) (x y : A), x = y -> JMeq x y.
Proof.
  intros ; subst.
  apply JMeq_refl. 
Qed.

Program Instance category_setoid : Setoid category := {
  equiv := category_equality
}.
