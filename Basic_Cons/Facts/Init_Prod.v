Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Main.

Require Import Basic_Cons.CCC.

Require Import NatTrans.NatTrans NatTrans.NatIso.
Require Import Yoneda.Yoneda.

(** 0 × a ≡ 0. where 0 is the initial object *)
Section Init_Prod.
  Context {C : Category} {C_CCC : CCC C} {init : Initial C}.

  (** Natural transformations to be used with Yoneda. *)
  
  Program Definition Init_Prod_lr a :
    (((((CoYoneda C) _o) ((Prod_Func C) _o (@terminal _ init, a)))%object)
      –≻ (((CoYoneda C) _o) init)%object)%nattrans
    :=
      {|
        Trans := fun b f => @t_morph _ init b
      |}.

  Next Obligation.
  Proof.
    extensionality g.
    apply t_morph_unique.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Init_Prod_lr_obligation_1.
  Qed.

  Program Definition Init_Prod_rl a :
    (((((CoYoneda C) _o) init)%object)
       –≻ (((CoYoneda C) _o) ((Prod_Func C) _o (@terminal _ init, a)))%object)%nattrans
    :=
      {|
        Trans := fun c g => compose C (Pi_1 (CCC_HP C init a)) (t_morph init c)
      |}.
  
  Next Obligation.
  Proof.
    extensionality g.
    simpl_ids.
    rewrite <- assoc.
    apply f_equal.
    apply (t_morph_unique init).
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Init_Prod_rl_obligation_1.
  Qed.

  Theorem Init_Prod a :
    (((Prod_Func C) _o (@terminal _ init, a)) ≃ init)%isomorphism.
  Proof.
    apply (@CoIso (C^op)).
    CoYoneda.
    apply (NatIso _ _ (Init_Prod_lr a) (Init_Prod_rl a)).
    {
      intros c.
      extensionality g; simpl.
      apply (t_morph_unique init).
    }
    {
      intros c.
      eapply functional_extensionality; intros g; simpl; simpl_ids.
      match goal with
          [|- ?A = ?B] =>
          erewrite <- uncurry_curry with(f := A);
            erewrite <- uncurry_curry with (f := B)
      end.
      apply f_equal.
      apply (t_morph_unique init).
    }
  Qed.

End Init_Prod.
