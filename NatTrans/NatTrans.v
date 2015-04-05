Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.

Section NatTrans.
  Context {C C' : Category}.

  Class NatTrans (F F' : Functor C C') :=
    {
      Trans (c : C) : Hom (F _o c) (F' _o c);
      Trans_com {c c' : C} (h : Hom c c') : (Trans c') ∘ F _a _ _ h = F' _a _ _ h ∘ (Trans c);
      Trans_com_sym {c c' : C} (h : Hom c c') : F' _a _ _ h ∘ (Trans c) = (Trans c') ∘ F _a _ _ h
    }.

  Arguments Trans {_ _} _ _.

  (* NatTrans_Setoid defined *)

  Lemma NatTrans_eq_simplify {F F' : Functor C C'} (N N' : NatTrans F F') : (@Trans _ _ N) = (@Trans _ _ N') -> N = N'.
  Proof.
    intros H1.
    destruct N as [NT NC NCs]; destruct N' as [NT' NC' NCs']; cbn in *.
    destruct H1.
    destruct (proof_irrelevance _ NC NC').
    destruct (proof_irrelevance _ NCs NCs').    
    trivial.
  Qed.

  Program Instance NatTrans_compose {F F' F'' : Functor C C'} (tr : NatTrans F F') (tr' : NatTrans F' F'') : NatTrans F F'' :=
    {
      Trans := fun c : Obj => (Trans tr' c) ∘ (Trans tr c)
    }.

  Next Obligation. (* Trans_com*)
  Proof.
    rewrite assoc.
    rewrite Trans_com.
    match goal with [|- ?A ∘ ?B ∘ ?C = ?D] => reveal_comp A B end.
    rewrite Trans_com; auto.
  Qed.

  Next Obligation. (* Trans_com_sym *)
  Proof.
    symmetry.
    apply NatTrans_compose_obligation_1.
  Qed.
  
  (* NatTrans_compose defined *)

  Program Instance NatTrans_id (F : Functor C C') : NatTrans F F :=
    {
      Trans := fun x : Obj => F _a _ _ id
    }.

  (* NatTrans_id defined *)

End NatTrans.

Arguments Trans {_ _ _ _} _ _.
Arguments Trans_com {_ _ _ _} _ {_ _} _.

Hint Resolve NatTrans_eq_simplify.

Local Hint Extern 1 => apply NatTrans_eq_simplify; simpl.

Program Instance Func_Cat (C C' : Category) : Category :=
{
  Obj := Functor C C';

  Hom := NatTrans;

  compose := @NatTrans_compose _ _;

  id := @NatTrans_id _ _
}.

Section NatIso.
  Context {C C' : Category} (F G : Functor C C') (n : NatTrans F G) (n' : NatTrans G F).

  Theorem NatIso : (∀ (c : Obj), (Trans n c) ∘ (Trans n' c) = G _a _ _ (@id _ c)) →
                   (∀ (c : Obj), (Trans n' c) ∘ (Trans n c) = F _a _ _ (@id _ c)) →
                   F ≡≡ G ::> Func_Cat _ _.
  Proof.
    intros H1 H2.
    apply (Build_Isomorphism (Func_Cat _ _) _ _ n n'); auto.
  Qed.

End NatIso.

Section Opposite_NatTrans.
  Context {C D : Category} {F F' : Functor C D} (N : NatTrans F F').

  Instance Opposite_NatTrans : NatTrans (Opposite_Functor F') (Opposite_Functor F) :=
    {
      Trans := Trans N;
      Trans_com := fun c c' h => (@Trans_com_sym _ _ _ _ N _ _ h);
      Trans_com_sym := fun c c' h => (@Trans_com _ _ _ _ N _ _ h)
    }.
  
End Opposite_NatTrans.

(* Composition of opposite nat transes *)

Section Compose_NOP.
  Context {C D : Category} {F F' F'' : Functor C D} (N : NatTrans F F') (N' : NatTrans F' F'').

  Theorem NatTrans_compose_Op : Opposite_NatTrans (NatTrans_compose N N') = NatTrans_compose (Opposite_NatTrans N') (Opposite_NatTrans N).
  Proof.
    apply NatTrans_eq_simplify.
    trivial.
  Qed.

End Compose_NOP.

(* Opposite of NatTrans_id *)

Section NatTrans_id_Op.
  Context {C D : Category} (F : Functor C D).

  Theorem NatTrans_id_Op : Opposite_NatTrans (NatTrans_id F) = NatTrans_id (Opposite_Functor F).
  Proof.
    apply NatTrans_eq_simplify.
    trivial.
  Qed.

End NatTrans_id_Op.

(* Horizontal composition of natural transformations *)

Program Instance NatTrans_hor_comp {C D E : Category} {F G : Functor C D} {F' G' : Functor D E} (tr : NatTrans F G) (tr' : NatTrans F' G') : NatTrans (Functor_compose F F') (Functor_compose G G') :=
{
  Trans := fun c : Obj => (G' _a _ _ (Trans tr c)) ∘ (Trans tr' (F _o c))
}.

Next Obligation. (* Trans_com*)
Proof.
  rewrite assoc.
  rewrite Trans_com.
  match goal with [|- ?A ∘ ?B ∘ ?C = ?D] => reveal_comp A B end.
  rewrite <- F_compose.
  rewrite Trans_com.
  rewrite F_compose.
  auto.
Qed.

Next Obligation. (* Trans_com*)
Proof.
  symmetry.
  apply NatTrans_hor_comp_obligation_1.
Qed.

Section Hor_Compose_NOP.
  Context {C D E : Category} {F G : Functor C D} {F' G' : Functor D E} (N : NatTrans F G) (N' : NatTrans F' G').

  Theorem NatTrans_hor_comp_Op : Opposite_NatTrans (NatTrans_hor_comp N N') = NatTrans_hor_comp (Opposite_NatTrans N) (Opposite_NatTrans N').
  Proof.
    apply NatTrans_eq_simplify.
    simpl.
    extensionality c.
    rewrite Trans_com.
    trivial.
  Qed.

End Hor_Compose_NOP.

Program Instance NatTrans_to_compose_id {C D : Category} (F : Functor C D) : NatTrans F (Functor_compose F (Functor_id _)) :=
{
  Trans := fun c => id
}.

Program Instance NatTrans_from_compose_id {C D : Category} (F : Functor C D) : NatTrans (Functor_compose F (Functor_id _)) F :=
{
  Trans := fun c => id
}.

Program Instance NatTrans_to_id_compose {C D : Category} (F : Functor C D) : NatTrans F (Functor_compose (Functor_id _) F) :=
{
  Trans := fun c => id
}.

Program Instance NatTrans_from_id_compose {C D : Category} (F : Functor C D) : NatTrans (Functor_compose (Functor_id _) F) F :=
{
  Trans := fun c => id
}.

Program Instance NatTrans_Functor_assoc {C1 C2 C3 C4 : Category}
        (F : Functor C1 C2)
        (G : Functor C2 C3)
        (H : Functor C3 C4)
: NatTrans (Functor_compose F (Functor_compose G H)) (Functor_compose (Functor_compose F G) H) :=
{
  Trans := fun c => id
}.

Program Instance NatTrans_Functor_assoc_sym {C1 C2 C3 C4 : Category}
        (F : Functor C1 C2)
        (G : Functor C2 C3)
        (H : Functor C3 C4)
: NatTrans (Functor_compose (Functor_compose F G) H) (Functor_compose F (Functor_compose G H)) :=
{
  Trans := fun c => id
}.

Section NatTrans_id_Iso.
  Context {C D : Category} (F : Functor C D).

  Program Instance NatTrans_id_Iso : F ≡≡ F ::> Func_Cat _ _ :=
    {
      iso_morphism := NatTrans_id _;
      inverse_morphism := NatTrans_id _
    }.

End NatTrans_id_Iso.

Section NatTrans_comp_hor_comp.
  Context {C D E  : Category} {F F' F'' : Functor C D} {G G' G'' : Functor D E} (N1 : NatTrans F F') (N2 : NatTrans G G') (N3 : NatTrans F' F'') (N4 : NatTrans G' G'').

  Theorem NatTrans_comp_hor_comp : NatTrans_compose (NatTrans_hor_comp N1 N2) (NatTrans_hor_comp N3 N4) = NatTrans_hor_comp (NatTrans_compose N1 N3) (NatTrans_compose N2 N4).
  Proof.
    apply NatTrans_eq_simplify.
    extensionality c.
    cbn.
    rewrite F_compose.
    repeat rewrite assoc.
    match goal with
      [|- ?A ∘ ?B = ?A ∘ ?C] =>
      let H := fresh in
      cut (B = C); [intros H; rewrite H; trivial|]
    end.
    repeat rewrite assoc_sym.
    match goal with
      [|- ?A ∘ ?B = ?C ∘ ?B] =>
      let H := fresh in
      cut (A = C); [intros H; rewrite H; trivial|]
    end.
    apply Trans_com.
  Qed.    

End NatTrans_comp_hor_comp.
    
Section NatIso_hor_comp.
  Context {C D E : Category} {F F' : Functor C D} {G G' : Functor D E} (N : F ≡≡ F' ::> Func_Cat _ _) (N' : G ≡≡ G' ::> Func_Cat _ _).

  Local Obligation Tactic := idtac.

  Program Instance NatIso_hor_comp : Functor_compose F G ≡≡ Functor_compose F' G' ::> Func_Cat _ _ :=
    {
      iso_morphism := NatTrans_hor_comp (iso_morphism N) (iso_morphism N');
      inverse_morphism := NatTrans_hor_comp (inverse_morphism N) (inverse_morphism N')
    }.

  Next Obligation.
  Proof.
    cbn.
    rewrite NatTrans_comp_hor_comp.
    set (H := left_inverse N); cbn in H; rewrite H; clear H.
    set (H := left_inverse N'); cbn in H; rewrite H; clear H.
    auto.
  Qed.

  Next Obligation.
  Proof.
    cbn.
    rewrite NatTrans_comp_hor_comp.
    set (H := right_inverse N); cbn in H; rewrite H; clear H.
    set (H := right_inverse N'); cbn in H; rewrite H; clear H.
    auto.
  Qed.

End NatIso_hor_comp.

Section Opposite_Func_Cat.
  Context (C D : Category).

  Instance Op_Func_Cat_to_Func_Cat_Op : Functor (Func_Cat C D)^op (Func_Cat C^op D^op) :=
    {
      FO := Opposite_Functor;
      FA := fun _ _ => Opposite_NatTrans;
      F_id := fun _ => NatTrans_id_Op _;
      F_compose := fun _ _ _ _ _ => NatTrans_compose_Op _ _ 
    }.

  Instance Func_Cat_Op_to_Op_Func_Cat : Functor (Func_Cat C^op D^op) (Func_Cat C D)^op :=
    {
      FO := Opposite_Functor;
      FA := fun _ _ => Opposite_NatTrans;
      F_id := fun F => NatTrans_id_Op F;
      F_compose := fun _ _ _ N N' => NatTrans_compose_Op N N'
    }.

  Program Instance Func_Cat_Op_Iso : (Func_Cat C D)^op ≡≡ (Func_Cat C^op D^op) ::> Cat :=
    {
      iso_morphism := Op_Func_Cat_to_Func_Cat_Op;
      inverse_morphism := Func_Cat_Op_to_Op_Func_Cat
    }.

End Opposite_Func_Cat.

Section Opposite_NatIso.
  Context {C D : Category} {F G : Functor C D} (N : F ≡≡ G ::> Func_Cat _ _).

  Program Instance Opposite_NatIso : Opposite_Functor F ≡≡ Opposite_Functor G ::> Func_Cat _ _ :=
    {
      iso_morphism := (Opposite_NatTrans (inverse_morphism N));
      inverse_morphism := (Opposite_NatTrans (iso_morphism N))
    }.

  Next Obligation.
  Proof.
    rewrite <- NatTrans_compose_Op.
    change (NatTrans_compose (iso_morphism N) N⁻¹) with (N⁻¹ ∘ N).
    rewrite left_inverse.
    apply NatTrans_id_Op.
  Qed.

  Next Obligation.
  Proof.
    rewrite <- NatTrans_compose_Op.
    change (NatTrans_compose N⁻¹ (iso_morphism N)) with (N ∘ N⁻¹).
    rewrite right_inverse.
    apply NatTrans_id_Op.
  Qed.

End Opposite_NatIso.

Section NatIso_compose.
  Context {C D : Category} {F G H : Functor C D} (N : F ≡≡ G ::> Func_Cat _ _) (N' : G ≡≡ H ::> Func_Cat _ _).

  Local Obligation Tactic := idtac.

  Program Instance NatIso_compose : F ≡≡ H ::> Func_Cat _ _ :=
    {
      iso_morphism := (NatTrans_compose (iso_morphism N) (iso_morphism N'));
      inverse_morphism := (NatTrans_compose (inverse_morphism N') (inverse_morphism N))
    }.

  Next Obligation.
  Proof.
    change (NatTrans_compose (iso_morphism N) (iso_morphism N')) with (N' ∘ N).
    change (NatTrans_compose N'⁻¹ N⁻¹) with (N⁻¹ ∘ N'⁻¹).
    rewrite assoc.
    rewrite (assoc_sym N _ _).
    rewrite left_inverse.
    simpl_ids.
    apply left_inverse.
  Qed.

  Next Obligation.
  Proof.
    change (NatTrans_compose (iso_morphism N) (iso_morphism N')) with (N' ∘ N).
    change (NatTrans_compose N'⁻¹ N⁻¹) with (N⁻¹ ∘ N'⁻¹).
    rewrite assoc.
    rewrite (assoc_sym _ _ N).
    rewrite right_inverse.
    simpl_ids.
    apply right_inverse.
  Qed.

End NatIso_compose.
