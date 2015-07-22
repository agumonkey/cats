Require Import Category.Main.
Require Import Basic_Cons.Product.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Local Obligation Tactic := basic_simpl; auto 2.

(** The sum of types in coq is the categorical notion of sum in category of types. *)
Program Definition sum_Sum (A B : Type) : @Sum Type_Cat A B :=
{|
  product := (A + B)%type;
  Prod_morph_ex :=
    fun (p' : Type)
        (r1 : A → p')
        (r2 : B → p')
        (X : A + B) =>
      match X return p' with
      | inl a => r1 a
      | inr b => r2 b
      end
|}.

Local Obligation Tactic := idtac.

Next Obligation. (* Sum_morph_unique *)
Proof.
  intros A B p' r1 r2 f g H1 H2 H3 H4.
  rewrite <- H3 in H1.
  rewrite <- H4 in H2.
  clear H3 H4.
  extensionality x.
  destruct x;
    match goal with
        [|- f (?m ?y) = g (?m ?y)] =>
        apply (@equal_f _ _ (fun x => f (m x)) (fun x => g (m x)))
    end; auto.
Qed.

(* sum_Sum defined *)

Program Instance Type_Cat_Has_Sums : Has_Sums Type_Cat := sum_Sum.

