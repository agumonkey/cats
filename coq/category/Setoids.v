(******* The category of setoids *******)
Require Export Coq.Program.Program.
Require Export Category.

Generalizable All Variables.
Open Scope signature.

Inductive Objects := obj 
  { Carrier :> Type 
  ; proof :> Setoid Carrier
  }.

Notation " '∥' x '∥' " := (Carrier x) (at level 40).

Record SetoidMorphism `{SFrom: Setoid A} `{STo: Setoid B}
  := 
  { morph :> A -> B
  ; proper_morph :> Proper (equiv ==> equiv) morph
  }.

Global Program Instance proper_arrows: Arrows Objects
  := fun a b => @SetoidMorphism a (proof a) b (proof b).

(* Notation " a =={ X } b " := (@equiv X _ a b) (at level 40). *)

Global Program Instance : forall (A B : Objects), Setoid (A ~> B) :=
  {| equiv := fun f g => forall x, @equiv B (proof B) (f x) (g x) |}.
(* Next Obligation. *)
(*   destruct B. auto. Qed. *)
Next Obligation.
  constructor; repeat intro.
  reflexivity.
  symmetry. apply (H x0).
  transitivity (y x0); [apply (H x0) | apply (H0 x0)].
Qed.

Program Definition sm_comp {a b c} (g : b ~> c) (f : a ~> b) : a ~> c :=
  @Build_SetoidMorphism _ _ _ _ (compose (morph g) (morph f)) _.
Next Obligation.
  repeat intro. unfold compose. 
  destruct a; destruct b; destruct c; simpl.
  destruct g. destruct f. simpl.
  rewrite H. reflexivity. Qed.

Lemma sm_comp_assoc : forall {a b c d} (h : c ~> d) (g : b ~> c) (f : a ~> b), 
  sm_comp h (sm_comp g f) == sm_comp (sm_comp h g) f.
Proof.
  intros. unfold sm_comp. simpl.
  unfold compose. intros. reflexivity. 
Qed.

Definition sm_id a : a ~> a := {| morph := id; proper_morph := _ |}.
  
Global Program Instance setoid_cat : @Category Objects proper_arrows :=
  {
    comp := @sm_comp
  ; comp_assoc a b f c g d h := sm_comp_assoc h g f
  ; cat_id := @sm_id
  }.
Next Obligation.
  repeat intro. unfold sm_comp. simpl.
  unfold compose. 
  destruct x0. destruct y0. destruct x. destruct y. simpl.
  rewrite (H0 x1). simpl.
  apply (H (morph1 x1)).
Qed.
Next Obligation.
  destruct f. simpl. 
  reflexivity. 
Qed.
Next Obligation.
  destruct f. simpl.
  reflexivity.
Qed.
