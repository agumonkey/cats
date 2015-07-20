Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import Basic_Cons.Product.
Require Import Basic_Cons.Exponential.
Require Import NatTrans.NatTrans NatTrans.Func_Cat NatTrans.NatIso.
Require Import Cat.Cat_Product Cat.Cat_Exponential.

(** Facts about exponentials in Cat. *)

Local Open Scope functor_scope.

Section Exp_Cat_morph_ex_compose.
  Context {C C' C'' : Category}
          (F : (Prod_Cat C'' C) –≻  C')
          {B : Category}
          (G : B –≻ C'')
  .

  (** This is the more specific case of curry_compose. Proven separately for cat because of universe polymorphism issues that prevent cat to both have expoenentials and type_cat in it. *)
  Theorem Exp_Cat_morph_ex_compose :
    Exp_Cat_morph_ex (F ∘ (Prod_Functor G (Functor_id C))) = (Exp_Cat_morph_ex F) ∘ G.
  Proof.
    Func_eq_simpl.
    {
      FunExt.
      apply NatTrans_eq_simplify.
      apply JMeq_eq.
      ElimEq; trivial.
    }
    {
      FunExt; cbn.
      Func_eq_simpl.
      FunExt.
      cbn; auto.
    }
  Qed.

End Exp_Cat_morph_ex_compose.

Section Exp_Cat_morph_ex_compose_Iso.
  Context {C C' C'' : Category}
          (F : (Prod_Cat C'' C) –≻  C')
          {B : Category}
          (G : B –≻ C'').

  Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.
  
  Program Definition Exp_Cat_morph_ex_compose_Iso_RL :
    ((Exp_Cat_morph_ex (F ∘ (Prod_Functor G (Functor_id C)))) –≻ ((Exp_Cat_morph_ex F) ∘ G))%nattrans :=
    {|
      Trans :=
        fun c =>
          {|
            Trans := fun d => id
          |}
    |}.

  Program Definition Exp_Cat_morph_ex_compose_Iso_LR :
    (((Exp_Cat_morph_ex F) ∘ G) –≻ (Exp_Cat_morph_ex (F ∘ (Prod_Functor G (Functor_id C)))))%nattrans
    :=
    {|
      Trans :=
        fun c =>
          {|
            Trans := fun d => id
          |}
    |}.
    
  (** This is the isomorphic form of the theorem above. *)
  Program Definition Exp_Cat_morph_ex_compose_Iso : ((Exp_Cat_morph_ex (F ∘ (Prod_Functor G (Functor_id C))))%functor ≃ ((Exp_Cat_morph_ex F) ∘ G)%functor)%natiso :=
    {|
      iso_morphism := Exp_Cat_morph_ex_compose_Iso_RL;
      inverse_morphism := Exp_Cat_morph_ex_compose_Iso_LR
    |}.

End Exp_Cat_morph_ex_compose_Iso.

Section Exp_Cat_morph_ex_NT.
  Context {C C' C'' : Category}
          {F F' : (Prod_Cat C'' C) –≻  C'}
          (N : (F –≻ F')%nattrans).
  (** If we have a natural transformation from F to F' then we have a natural transformation from (curry F) to (curry F'). *)
  Program Definition Exp_Cat_morph_ex_NT :
    ((Exp_Cat_morph_ex F) –≻ (Exp_Cat_morph_ex F'))%nattrans :=
    {|
      Trans := fun d =>
                 {|
                   Trans := fun c => Trans N (d, c);
                   Trans_com := fun c c' h => @Trans_com _ _ _ _ N (d, c) (d ,c') (id,  h);
                   Trans_com_sym := fun c c' h => @Trans_com_sym _ _ _ _ N (d, c) (d ,c') (id,  h)
                 |}
    |}.

  Next Obligation.
  Proof.  
    apply NatTrans_eq_simplify; FunExt; cbn.
    apply Trans_com.
  Qed.    

  Next Obligation.
  Proof.
    symmetry.
    apply Exp_Cat_morph_ex_NT_obligation_1.
  Qed.

End Exp_Cat_morph_ex_NT.

Section Exp_Cat_morph_ex_Iso.
  Context {C C' C'' : Category}
          {F F' : (Prod_Cat C'' C) –≻ C'}
          (N : (F ≃ F')%natiso)
  .

  (** If F is naturally isomorphic to F' then (curry F) is naturally isomorphic to (curry F'). *)
  Program Definition Exp_Cat_morph_ex_Iso : (Exp_Cat_morph_ex F ≃ Exp_Cat_morph_ex F')%natiso :=
    {|
      iso_morphism := Exp_Cat_morph_ex_NT (iso_morphism N);
      inverse_morphism := Exp_Cat_morph_ex_NT (inverse_morphism N)
    |}.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality x; cbn.
    apply NatTrans_eq_simplify; extensionality y; cbn.
    change (Trans N ⁻¹ (x, y) ∘ Trans (iso_morphism N) (x, y))%morphism with (Trans (N⁻¹ ∘ N)%morphism (x, y)).
    rewrite left_inverse; trivial.
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality x; cbn.
    apply NatTrans_eq_simplify; extensionality y; cbn.
    change (Trans (iso_morphism N) (x, y) ∘ Trans N⁻¹ (x, y))%morphism with (Trans (N ∘ N⁻¹)%morphism (x, y)).
    rewrite right_inverse; trivial.
  Qed.

End Exp_Cat_morph_ex_Iso.

Section Exp_Cat_morph_ex_inverse_NT.
  Context {C C' C'' : Category}
          {F F' : (Prod_Cat C'' C) –≻  C'}
          (N : ((Exp_Cat_morph_ex F) –≻ (Exp_Cat_morph_ex F'))%nattrans).


  (** If we have a natural transformation from (curry F) to (curry F') then we have a natural transformation from F to F'. *)
  Program Definition Exp_Cat_morph_ex_inverse_NT : (F –≻ F')%nattrans :=
    {|
      Trans := fun d => Trans (Trans N (fst d)) (snd d)
    |}.

  Local Obligation Tactic := idtac.
  
  Next Obligation.
  Proof.  
    intros [d1 d2] [d1' d2'] [h1 h2]; cbn in *.
    replace (F @_a (_, _) (_, _) (h1, h2))%morphism with ((F @_a (_, _) (_, _) (id d1', h2)) ∘ (F @_a (_, _) (_, _) (h1, id d2)))%morphism by auto.
    rewrite assoc_sym.   
    cbn_rewrite (Trans_com (Trans N d1') h2).
    rewrite assoc.
    cbn_rewrite (f_equal (fun w => Trans w d2) (Trans_com N h1)).
    rewrite assoc_sym.
    rewrite <- F_compose.
    cbn; auto.
  Qed.    

  Next Obligation.
  Proof.
    symmetry.
    apply Exp_Cat_morph_ex_inverse_NT_obligation_1.
  Qed.

End Exp_Cat_morph_ex_inverse_NT.

Section Exp_Cat_morph_ex_inverse_Iso.
  Context {C C' C'' : Category}
          {F F' : (Prod_Cat C'' C) –≻  C'}
          (N : (Exp_Cat_morph_ex F ≃ Exp_Cat_morph_ex F')%natiso)
  .

  (** If (curry F) is naturally isomorphic  to (curry F') then we have that F is naturally isomorphic to F'. *)
  Program Definition Exp_Cat_morph_ex_inverse_Iso :  (F ≃ F')%natiso :=
    {|
      iso_morphism := Exp_Cat_morph_ex_inverse_NT (iso_morphism N);
      inverse_morphism := Exp_Cat_morph_ex_inverse_NT (inverse_morphism N)
    |}.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality x; cbn.
    match goal with
      [|- ?U = _] =>
      match U with
         (Trans (Trans ?A ?X) ?Y ∘ Trans (Trans ?B ?X) ?Y)%morphism =>
         change U with (Trans (Trans (A ∘ B) X) Y)
      end
    end.
    cbn_rewrite (left_inverse N); trivial. 
  Qed.
  
  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality x; cbn.
    match goal with
      [|- ?U = _] =>
      match U with
        (Trans (Trans ?A ?X) ?Y ∘ Trans (Trans ?B ?X) ?Y)%morphism =>
        change U with (Trans (Trans (NatTrans_compose B A) X) Y)
      end
    end.
    cbn_rewrite (right_inverse N); trivial.
  Qed.

End Exp_Cat_morph_ex_inverse_Iso.
