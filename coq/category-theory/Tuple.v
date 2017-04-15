(* jww (2017-04-13): TODO
Require Import Lib.
Require Export Coq.

Program Instance Pair {X Y : Set} : @Product Type _ (X * Y)%type Y X (@fst X Y) (@snd X Y).
Obligation 1. (* product ump *)
  exists (fun x => (x1 x, x2 x)).
  intros. constructor.
    intros. unfold fst. reflexivity.
  split.
    intros. unfold snd. reflexivity.
  intros.
  inversion H.
  extensionality e.
  rewrite <- H0.
  rewrite <- H1.
  destruct (v e).
  reflexivity.
Defined.

Definition Tuple_map {Z X Y} (f : X → Y) (p : Z * X) : Z * Y :=
  match p with
  | pair z x => @pair Z Y z (f x)
  end.

Program Instance Tuple_Functor {Z} : Sets ⟶ Sets :=
{ fobj := fun X => Z * X
; fmap := @Tuple_map Z
}.
Obligation 1. extensionality e. crush. Defined.
Obligation 2. extensionality e. crush. Defined.

Notation "C ⟶ D" := (Functor C D) (at level 90, right associativity).
*)