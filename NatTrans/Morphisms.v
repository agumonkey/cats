Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops.
Require Import Cat.Cat.
Require Import NatTrans.NatTrans NatTrans.Func_Cat.

Local Open Scope nattrans_scope.

(** If all components of a natural transformation are monic then
so is that natural transformation. *)
Section is_Monic_components_is_Monic.
  Context
    {C D : Category}
    {F G : (C –≻ D)%functor}
    (N : F –≻ G)
    (H : ∀ c, is_Monic (Trans N c))
  .

  Definition is_Monic_components_is_Monic :
    @is_Monic (Func_Cat _ _) _ _ N.
  Proof.
    intros I g h H2.
    apply NatTrans_eq_simplify.
    extensionality x.
    apply H.
    apply (fun x => f_equal (fun w => Trans w x) H2).
  Qed.

End is_Monic_components_is_Monic.
