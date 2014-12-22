Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import Basic_Cons.Product.

Set Primitive Projections.

Set Universe Polymorphism.

(* Prod_Cat_morph_ex defined *)

Local Obligation Tactic := idtac.

Program Instance Cat_Products (C C' : Category) : @Product Cat C C' :=
{
  product := (Prod_Cat C C');

  Pi_1 := Cat_Proj1 C C';

  Pi_2 := Cat_Proj2 C C';

  Prod_morph_ex := fun P => fun F G =>  Functor_compose (Diag_Func P) (Prod_Functor F G)
}.

Next Obligation. (* Prod_morph_com1 *)
Proof.
  intros C C' p' r1 r2.
  apply Functor_eq_simplify; simpl; trivial.
Qed.

Next Obligation. (* Prod_morph_com2 *)
Proof.
  intros C C' p' r1 r2.
  apply Functor_eq_simplify; simpl; trivial.
Qed.

Lemma pair_JM_eq (A B C D : Type) (a : A * B) (c : C * D) : fst a ≃ fst c -> snd a ≃ snd c -> a ≃ c.
Proof.
  intros H1 H2.
  dependent destruction H1; dependent destruction H2.
  cutrewrite (a = c); trivial.
  destruct a; destruct c;
  simpl in *;
  repeat match goal with [H : _ = _|-_] => rewrite H end; trivial.
Qed.

Lemma pair_eq (A B : Type) (a b : A * B) : fst a = fst b -> snd a = snd b -> a = b.
Proof.
  intros H1 H2.
  destruct a; destruct b;
  simpl in *;
  repeat match goal with [H : _ = _|-_] => rewrite H end; trivial.
Qed.

Next Obligation. (* Prod_morph_unique *)
Proof.
  intros C C' p' r1 r2 f g H1 H2 H3 H4.
  destruct H1; destruct H2.
  cut (f _o = g _o); [intros HO|].
  {
    apply Functor_eq_simplify.
    {
      trivial.
    }
    {
      FA_extensionality a b F.
      apply pair_JM_eq.
      {
        match type of H3 with
            ?A = ?B =>
            eapply (@JMeq_trans _ _ _ _ (A _a _ _ F) _); [rewrite H3|]; trivial
        end.
      }
      {
        match type of H4 with
            ?A = ?B =>
            eapply (@JMeq_trans _ _ _ _ (A _a _ _ F) _); [rewrite H4|]; trivial
        end.
      }
    }
  }
  {
    extensionality z.
    apply pair_eq.
    {
      match type of H3 with
          ?A = ?B =>
          transitivity (A _o z); [rewrite H3|]; trivial
      end.
    }
    {
      match type of H4 with
          ?A = ?B =>
          transitivity (A _o z); [rewrite H4|]; trivial
      end.
    }
  }
Qed.


(* Cat_Products defined *)

Program Instance Cat_Has_Products : Has_Products Cat.




