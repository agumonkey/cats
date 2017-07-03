Set Warnings "-notation-overridden".

Require Import Coq.NArith.NArith.
Require Import Coq.FSets.FMaps.

Require Import Category.Lib.
Require Import Category.Lib.Nomega.
Require Import Category.Lib.FMapExt.
Require Import Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Module PO := PairOrderedType N_as_OT N_as_OT.
Module M  := FMapList.Make(PO).
Module Import FMapExt := FMapExt PO M.

(* An arrows-only meta-category defines identity arrows as those which, when
   composed to the left or right of another arrow, result in that same arrow.
   This definition requires that all such composition be present. *)

Record Metacategory := {
  arrow := N;
  pairs : M.t arrow;

  composite (f g h : arrow) := M.find (f, g) pairs = Some h;
  defined (f g : arrow) := ∃ h, composite f g h;

  composite_defined {f g h : arrow} (H : composite f g h) :
    defined f g := (h; H);

  (*a ∀ edges (X, Y) and (Y, Z), ∃ an edge (X, Z) which is equal to the
     composition of those edges. *)
  composite_correct {f g h fg gh : arrow} :
    composite f g fg ->
    composite g h gh -> ∃ fgh, composite fg h fgh;

  composition_law {f g h fg gh : arrow} :
    composite f g fg ->
    composite g h gh ->
    ∀ fgh, composite fg h fgh ↔ composite f gh fgh;

  is_identity (u : arrow) :=
    (∀ f, defined f u -> composite f u f) ∧
    (∀ g, defined u g -> composite u g g);

  identity_law (x y f : arrow) : composite x y f ->
    ∃ u u', is_identity u -> is_identity u' ->
      composite f u f ∧ composite u' f f
}.

Section Category.

Context (M : Metacategory).

Record object := {
  obj_arr : arrow M;
  obj_def : composite M obj_arr obj_arr obj_arr;
  obj_id  : is_identity M obj_arr
}.

Record morphism (dom cod : object) := {
  mor_arr : arrow M;
  mor_dom : composite M mor_arr (obj_arr dom) mor_arr;
  mor_cod : composite M (obj_arr cod) mor_arr mor_arr
}.

Arguments mor_arr {_ _} _.
Arguments mor_dom {_ _} _.
Arguments mor_cod {_ _} _.

Definition identity (x : object) : morphism x x :=
  {| mor_arr := obj_arr x
   ; mor_dom := obj_def x
   ; mor_cod := obj_def x |}.

Lemma composition_left {x y z : object}
      {f : morphism y z} {g : morphism x y} {fg : arrow M} :
  composite M (mor_arr f) (mor_arr g) fg ->
  composite M (obj_arr z) (mor_arr f) (mor_arr f) ->
  composite M (obj_arr z) fg fg.
Proof.
  intros.
  destruct z, obj_id0, f, g; simpl in *.
  specialize (c0 _ (composite_defined M H0)); clear H0.
  destruct (composite_correct M c0 H).
  spose (fst (composition_law M c0 H _) e) as X.
  unfold composite, arrow in *.
  rewrite X, <- H, <- e; reflexivity.
Qed.

Lemma composition_right {x y z : object}
      {f : morphism y z} {g : morphism x y} {fg : arrow M} :
  composite M (mor_arr f) (mor_arr g) fg ->
  composite M (mor_arr g) (obj_arr x) (mor_arr g) ->
  composite M fg (obj_arr x) fg.
Proof.
  intros.
  destruct x, obj_id0, f, g; simpl in *.
  specialize (c _ (composite_defined M H0)); clear H0.
  destruct (composite_correct M H c).
  spose (fst (composition_law M H c _) e) as X.
  unfold composite, arrow in *.
  rewrite e, <- H, <- X; reflexivity.
Qed.

Definition composition {x y z : object}
           (f : morphism y z) (g : morphism x y) : morphism x z :=
  let fg := composite_correct M (mor_dom f) (mor_cod g) in
  {| mor_arr := `1 fg
   ; mor_dom := composition_right (f:=f) (`2 fg) (mor_dom g)
   ; mor_cod := composition_left  (g:=g) (`2 fg) (mor_cod f) |}.

Global Program Instance morphism_preorder : PreOrder morphism := {
  PreOrder_Reflexive  := identity;
  PreOrder_Transitive := fun _ _ _ g f => composition f g
}.

Global Program Instance morphism_setoid (x y : object) :
  Setoid (morphism x y) := {
  equiv := fun f g => mor_arr f = mor_arr g
}.

Lemma composition_respects {x y z : object} :
  Proper (equiv ==> equiv ==> equiv) (@composition x y z).
Proof.
  proper.
  destruct x0, y0, x1, y1; simpl in *; subst.
  repeat destruct (composite_correct _ _ _); simpl in *.
  unfold composite, arrow in *.
  rewrite e in e0.
  inversion_clear e0.
  reflexivity.
Qed.

Lemma composition_identity_left {x y : object} (f : morphism x y) :
  composition (identity y) f ≈ f.
Proof.
  destruct f; simpl.
  destruct (composite_correct _ _ _); simpl in *.
  unfold composite, arrow in *.
  rewrite mor_cod0 in e.
  inversion_clear e.
  reflexivity.
Qed.

Lemma composition_identity_right {x y : object} (f : morphism x y) :
  composition f (identity x) ≈ f.
Proof.
  destruct f; simpl.
  destruct (composite_correct _ _ _); simpl in *.
  unfold composite, arrow in *.
  rewrite mor_dom0 in e.
  inversion_clear e.
  reflexivity.
Qed.

Lemma composition_associative {x y z w : object}
      (f : morphism z w) (g : morphism y z) (h : morphism x y) :
  composition f (composition g h) ≈ composition (composition f g) h.
Proof.
  destruct f, g, h; simpl.
  repeat destruct (composite_correct _ _ _); simpl in *.
  spose (fst (composition_law M e1 e x3) e2) as X1.
  unfold composite, arrow in *.
  rewrite e0 in X1.
  inversion_clear X1.
  reflexivity.
Qed.

(* Every meta-category, defined wholly in terms of the axioms of category
   theory, gives rise to a category interpreted in the context of set
   theory. *)

Program Definition Category_from_Metacategory : Category := {|
  obj     := object;
  hom     := morphism;
  homset  := fun _ _ => {| equiv := fun f g => mor_arr f = mor_arr g |};
  id      := @identity;
  compose := @composition;

  compose_respects := @composition_respects;

  id_left    := @composition_identity_left;
  id_right   := @composition_identity_right;
  comp_assoc := @composition_associative;
  comp_assoc_sym := fun x y z w f g h =>
    symmetry (@composition_associative x y z w f g h);
|}.

End Category.

Arguments mor_arr _ {_ _} _.
Arguments mor_dom _ {_ _} _.
Arguments mor_cod _ {_ _} _.

Notation "[map ]" := (M.empty _) (at level 9, only parsing).
Notation "x +=> y" := (M.add x y) (at level 9, y at level 100, only parsing).
Notation "[map  a ; .. ; b ]" := (a .. (b [map]) ..) (only parsing).

Lemma mapsto_inv : ∀ elt f g (fg : elt) x y z m,
  M.MapsTo (f, g) fg (M.add (x, y) z m) ->
    (x = f ∧ y = g ∧ z = fg) ∨ M.MapsTo (f, g) fg m.
Proof.
  intros.
  apply add_mapsto_iffT in H.
  destruct H; simpl in *; intuition.
Defined.

Lemma find_inv : ∀ f g (fg : N) x y z m,
  M.find (f, g) (M.add (x, y) z m) = Some fg ->
    (x = f ∧ y = g ∧ z = fg) ∨ M.find (f, g) m = Some fg.
Proof.
  intros.
  destruct (N.eq_dec x f).
    destruct (N.eq_dec y g).
      destruct (N.eq_dec z fg).
        subst; left; intuition.
      contradiction n.
      rewrite F.add_eq_o in H.
        inversion_clear H.
        reflexivity.
      simpl; intuition.
    rewrite F.add_neq_o in H; intuition.
  rewrite F.add_neq_o in H; intuition.
Defined.

Global Program Instance sigT_proper {A : Type} :
  Proper (pointwise_relation A Basics.arrow ==> Basics.arrow) (@sigT A).
Next Obligation.
  proper.
  destruct X0.
  apply X in x1.
  exists x0.
  assumption.
Defined.

Lemma find_mapsto_iff_ex {elt k m} :
  (∃ v : elt, M.MapsTo (elt:=elt) k v m) ->
  (∃ v : elt, M.find (elt:=elt) k m = Some v).
Proof.
  apply sigT_proper.
  intros ??.
  apply F.find_mapsto_iff.
  assumption.
Defined.

Ltac destruct_maps :=
  repeat match goal with
  | [ H : M.find (?X, ?Y) (M.empty _) = Some ?F |- _ ] =>
    inversion H
  | [ H : M.find (?X, ?Y) (M.add _ _ _) = Some ?F |- _ ] =>
    apply find_inv in H;
    (destruct H as [[? [? ?]]|]; [subst; try nomega|])
  | [ |- ∃ v, M.find _ _ = Some v ] =>
    vm_compute; eexists; reflexivity

  | [ H : M.find _ _ = Some _ |- _ ] =>
    apply F.find_mapsto_iff in H
  | [ |- M.find _ _ = Some _ ] =>
    apply F.find_mapsto_iff
  | [ |- ∃ v, M.find _ _ = Some v ] =>
    apply find_mapsto_iff_ex

  | [ H : M.MapsTo _ _ (M.empty _) |- _ ] =>
    contradiction (proj1 (F.empty_mapsto_iff _ _) H)

  | [ H : M.MapsTo (?X, ?Y) ?F (M.add _ _ _) |- _ ] =>
    apply mapsto_inv in H; destruct H as [[? [? ?]]|]

  | [ H : ?X = ?Y |- context[M.MapsTo (?Y, _)] ] =>
    rewrite <- H; cbn
  | [ H : ?X = ?Y |- context[M.MapsTo (_, ?Y)] ] =>
    rewrite <- H; cbn
  | [ H : ?X = ?Y |- context[M.MapsTo _ ?Y] ] =>
    rewrite <- H; cbn

  | [ |- ∃ _, M.MapsTo (?X, ?Y) _ _ ] =>
    match goal with
      [ |- context[M.add (X, Y) ?F _ ] ] =>
      exists F
    end
  | [ |- M.MapsTo (?X, ?Y) ?F (M.add (?X, ?Y) ?F _) ] =>
    simplify_maps
  | [ |- M.MapsTo _ _ (M.add _ _ _) ] =>
    simplify_maps; right; split; [idtac|]
  end;
  try congruence.

Local Obligation Tactic := simpl; intros.

Ltac elimobj X :=
  elimtype False;
  unfold composite in X; simpl in X;
  clear -X;
  destruct_maps; nomega.

Lemma peano_rect' : ∀ P : N → Type, P 0%N → (∀ n : N, P (N.succ n)) → ∀ n : N, P n.
Proof.
  intros.
  induction n using N.peano_rect.
    apply X.
  apply X0.
Defined.

Ltac reflect_on_maps :=
  try split; intros; simpl in *; destruct_maps; subst;
  first [ nomega
        | repeat eexists; clear;
          first [ instantiate (1 := 0%N); vm_compute; reflexivity
                | instantiate (1 := 1%N); vm_compute; reflexivity
                | instantiate (1 := 2%N); vm_compute; reflexivity
                | instantiate (1 := 3%N); vm_compute; reflexivity
                | instantiate (1 := 4%N); vm_compute; reflexivity
                | instantiate (1 := 5%N); vm_compute; reflexivity] ].

Inductive term :=
  | Var : positive -> term
  | Value : N -> term.

Definition term_beq (x y : term) : bool :=
  match x, y with
  | Var x, Var y => (x =? y)%positive
  | Value x, Value y => (x =? y)%N
  | _, _ => false
  end.

Lemma term_beq_sound x y : term_beq x y = true -> x = y.
Proof.
  induction x, y; simpl; intros; intuition.
  - apply Pos.eqb_eq in H; subst; reflexivity.
  - apply N.eqb_eq in H; subst; reflexivity.
Defined.

Program Definition term_eq_dec (x y : term) : {x = y} + {x ≠ y} :=
  match x, y with
  | Var x,   Var y   => if Pos.eq_dec x y then left _ else right _
  | Value x, Value y => if N.eq_dec   x y then left _ else right _
  | _, _ => right _
  end.
Next Obligation. congruence. Defined.
Next Obligation. congruence. Defined.
Next Obligation. congruence. Defined.
Next Obligation. congruence. Defined.
Next Obligation.
  destruct H.
  destruct x, y, wildcard', wildcard'0; try discriminate.
    specialize (H0 p1 p2).
    intuition.
  specialize (H n1 n2).
  intuition.
Defined.
Next Obligation.
  split; intros;
  unfold not; intros;
  destruct H1;
  discriminate.
Defined.
Next Obligation.
  split; intros;
  unfold not; intros;
  destruct H1;
  discriminate.
Defined.

Lemma K_dec_on_type A (x : A) (eq_dec : ∀ y : A, x = y \/ x ≠ y)
      (P : x = x -> Type) :
  P (eq_refl x) -> forall p:x = x, P p.
Proof.
  intros.
  elim (@Eqdep_dec.eq_proofs_unicity_on A _) with x (eq_refl x) p.
    trivial.
  exact eq_dec.
Qed.

Lemma Pos_eq_dec' : ∀ x y : positive, x = y \/ x ≠ y.
Proof.
  intros.
  destruct (Pos.eq_dec x y); auto.
Qed.

Lemma Pos_eq_dec_refl n : Pos.eq_dec n n = left (@eq_refl positive n).
Proof.
  destruct (Pos.eq_dec n n).
    refine (K_dec_on_type positive n (Pos_eq_dec' n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl positive n)) _ _).
    reflexivity.
  contradiction.
Qed.

Lemma N_eq_dec' : ∀ x y : N, x = y \/ x ≠ y.
Proof.
  intros.
  destruct (N.eq_dec x y); auto.
Qed.

Lemma N_eq_dec_refl n : N.eq_dec n n = left (@eq_refl N n).
Proof.
  destruct (N.eq_dec n n).
    refine (K_dec_on_type N n (N_eq_dec' n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl N n)) _ _).
    reflexivity.
  contradiction.
Qed.

Lemma prod_eq_dec' :
  ∀ (A B : Type) (A_eq_dec : ∀ x y : A, x = y ∨ x ≠ y)
    (B_eq_dec : ∀ x y : B, x = y ∨ x ≠ y)
    (x y : A ∧ B), x = y \/ x ≠ y.
Proof.
  intros.
  destruct x, y; simpl.
  destruct (A_eq_dec a a0); subst.
    destruct (B_eq_dec b b0); subst.
      left; reflexivity.
    right; congruence.
  right; congruence.
Qed.

Lemma prod_eq_dec_refl (A B : Type) n
      (A_eq_dec : ∀ x y : A, x = y ∨ x ≠ y)
      (B_eq_dec : ∀ x y : B, x = y ∨ x ≠ y) :
  prod_eq_dec A_eq_dec B_eq_dec n n = left (@eq_refl (A ∧ B) n).
Proof.
  destruct (prod_eq_dec _ _ n n).
    refine (K_dec_on_type (A ∧ B) n (prod_eq_dec' _ _ A_eq_dec B_eq_dec n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl (A ∧ B) n)) _ _).
    reflexivity.
  contradiction.
Qed.

Lemma length_remove A (A_eq_dec : ∀ x y : A, x = y ∨ x ≠ y) x xs :
  (length (remove A_eq_dec x xs) <= length xs)%nat.
Proof.
  induction xs; auto.
  simpl.
  destruct (A_eq_dec x a); subst.
    apply Nat.le_le_succ_r, IHxs.
  simpl.
  apply le_n_S, IHxs.
Qed.

Definition lookup_definition (defs : list (positive * N))
           (x : positive) : option N :=
  match find (fun p => fst p =? x)%positive defs with
  | Some v => Some (snd v)
  | None => None
  end.
(* Next Obligation. *)
(*   symmetry in Heq_anonymous. *)
(*   apply find_some in Heq_anonymous. *)
(*   destruct Heq_anonymous. *)
(*   clear x Heq_x n H0 lookup_definition. *)
(*   generalize dependent v. *)
(*   induction defs; simpl; intros. *)
(*     contradiction. *)
(*   destruct (prod_eq_dec Pos.eq_dec term_eq_dec v a). *)
(*     apply le_lt_n_Sm, length_remove. *)
(*   simpl. *)
(*   destruct H. *)
(*     congruence. *)
(*   apply lt_n_S. *)
(*   eapply IHdefs; eauto. *)
(* Defined. *)
(* Next Obligation. *)
(*   apply measure_wf, lt_wf. *)
(* Defined. *)

Definition term_denote (vars : positive -> N) (defs : list (positive * N))
           (x : term) : N :=
  match x with
  | Var n =>
    match lookup_definition defs n with
    | Some v => v
    | None => vars n
    end
  | Value n => n
  end.

Inductive map_expr : Set :=
  | Empty : map_expr
  | Add   : N -> N -> N -> map_expr -> map_expr.

Fixpoint map_expr_denote (vars : positive -> N) (defs : list (positive * N))
         (m : map_expr) : M.t N :=
  match m with
  | Empty => M.empty N
  | Add x y f m' => M.add (x, y) f (map_expr_denote vars defs m')
  end.

Inductive formula :=
  | Maps    : term -> term -> term -> map_expr -> formula
  | MapsAny : term -> term -> map_expr -> formula
  | Impl    : formula -> formula -> formula.

Fixpoint formula_denote (vars : positive -> N) (defs : list (positive * N))
         (t : formula) : Prop :=
  match t with
  | Maps x y f m =>
    M.MapsTo (term_denote vars defs x, term_denote vars defs y)
             (term_denote vars defs f) (map_expr_denote vars defs m)
  | MapsAny x y m =>
    M.In (term_denote vars defs x, term_denote vars defs y)
         (map_expr_denote vars defs m)
  | Impl p q => formula_denote vars defs p -> formula_denote vars defs q
  end.

Inductive subterm : formula -> formula -> Prop :=
  | Impl1 : forall t1 t2, subterm t1 (Impl t1 t2)
  | Impl2 : forall t1 t2, subterm t2 (Impl t1 t2).

Lemma subterm_wf : well_founded subterm.
Proof.
  constructor; intros.
  inversion H; subst; simpl in *;
  induction y;
  induction t1 || induction t2;
  simpl in *;
  constructor; intros;
  inversion H0; subst; clear H0;
  try (apply IHy1; constructor);
  try (apply IHy2; constructor).
Defined.

Section partial.
  Variable P : Prop.

  Inductive partial : Set :=
  | Proved : P -> partial
  | Uncertain : partial.
End partial.

Notation "[ P ]" := (partial P) : type_scope.

Notation "'Yes'" := (Proved _ _) : partial_scope.
Notation "'No'" := (Uncertain _) : partial_scope.

Local Open Scope partial_scope.
Delimit Scope partial_scope with partial.

Notation "'Reduce' v" := (if v then Yes else No) (at level 100) : partial_scope.
Notation "x || y" := (if x then Yes else Reduce y) : partial_scope.
Notation "x && y" := (if x then Reduce y else No) : partial_scope.

Local Open Scope lazy_bool_scope.

Fixpoint map_contains (vars : positive -> N) (defs : list (positive * N))
         (x y : N) (m : map_expr) : option N :=
  match m with
  | Empty => None
  | Add x' y' f' m' =>
    match N.eq_dec x x' with
    | left _ =>
      match N.eq_dec y y' with
      | left _  => Some f'
      | right _ => map_contains vars defs x y m'
      end
    | right _ => map_contains vars defs x y m'
    end
  end.

Local Obligation Tactic := program_simpl.

Definition check_def (defs : list (positive * N)) (t : term) (v : N) : bool :=
  match t with
  | Var t =>
    let fix check xs v v' :=
        match xs return bool with
        | nil => true
        | cons (x, x') xs =>
          match Pos.eq_dec v x with
          | left _ =>
            match N.eq_dec v' x' with
            | left _  => true
            | right _ => false
            end
          | right _ => check xs v v'
          end
        end in
    check defs t v
  | _ => true
  end.

(* Lemma term_redef_idem vars defs x y t : *)
(*   term_denote vars defs x = term_denote vars defs (Var y) -> *)
(*   term_denote vars ((y, x) :: defs) t = term_denote vars defs t. *)
(* Proof. *)
(* Admitted. *)

(* Lemma map_expr_redef_idem vars defs x y t : *)
(*   term_denote vars defs x = term_denote vars defs (Var y) -> *)
(*   map_expr_denote vars ((y, x) :: defs) t = map_expr_denote vars defs t. *)
(* Proof. *)
(*   generalize dependent y. *)
(*   induction t; simpl; intros; auto. *)
(*   - rewrite IHt, !term_redef_idem; auto. *)
(* Qed. *)

(* Lemma formula_redef_idem vars defs x y t : *)
(*   term_denote vars defs x = term_denote vars defs (Var y) -> *)
(*   formula_denote vars ((y, x) :: defs) t = formula_denote vars defs t. *)
(* Proof. *)
(*   generalize dependent y. *)
(*   induction t; simpl; intros; auto. *)
(*   - rewrite !term_redef_idem, !map_expr_redef_idem; auto. *)
(*   - rewrite !term_redef_idem, !map_expr_redef_idem; auto. *)
(*   - intuition. *)
(*     rewrite IHt1; auto. *)
(*     rewrite IHt2; auto. *)
(* Qed. *)

Lemma term_denote_cons_eq vars defs a x y :
  term_denote vars defs x = term_denote vars defs y <->
  term_denote vars (a :: defs) x = term_denote vars (a :: defs) y.
Proof.
  induction defs; simpl; intros.
  destruct x, y; simpl in *.
Abort.

(* Lemma check_def_false_impl vars defs f f' : *)
(*   false = check_def defs f f' *)
(*     -> term_denote vars defs f' ≠ term_denote vars defs f. *)
(* Proof. *)
(*   intros. *)
(*   induction defs; simpl in *; intros. *)
(*     destruct f; simpl in H; discriminate. *)
(* Admitted. *)

Lemma oops vars defs t : formula_denote vars defs t.
Proof. Admitted.

Inductive Status (defs : list (positive * N)) (v : term) (v' : N) : Prop :=
  | Conflict : ∀ d,
      match v with
      | Var u => lookup_definition defs u = Some d -> d ≠ v'
      | Value u => u ≠ v'
      end -> Status defs v v'
  | Known : ∀ d,
      match v with
      | Var u => lookup_definition defs u = Some d -> d = v'
      | Value u => u = v'
      end -> Status defs v v'
  | New : ∀ u,
      v = Var u -> lookup_definition defs u = None -> Status defs v v'.

Definition establish v v' defs T (k : ∀ defs' : list (positive * N), [T defs'])
  : { defs' : list (positive * N) & [T defs']%type } :=
  match v with
  | Var u =>
    match lookup_definition defs u with
    | Some n =>
      match N.eq_dec n v' with
      | left _  => existT _ defs (k defs)
      | right _ => existT _ defs No
      end
    | None => existT _ (cons (u, v') defs) (k (cons (u, v') defs))
    end
  | Value u =>
      match N.eq_dec u v' with
      | left _  => existT _ defs (k defs)
      | right _ => existT _ defs No
      end
  end.

Definition define v v' xs :=
  match v with
  | Var u =>
    match lookup_definition xs u with
    | Some n =>
      match N.eq_dec n v' with
      | left _  => Some xs
      | right _ => None
      end
    | None => Some (cons (u, v') xs)
    end
  | Value u =>
      match N.eq_dec u v' with
      | left _  => Some xs
      | right _ => None
      end
  end.

(* The only job of formula_forward at the moment is to accumulate variable
   definitions. *)
Program Definition formula_forward (t : formula)
        (vars : positive -> N) (defs : list (positive * N))
        (hyp : formula)
        (cont : ∀ vars' defs', [formula_denote vars' defs' t]) :
  [formula_denote vars defs hyp -> formula_denote vars defs t] :=
  match hyp with
  | Maps x y f Empty => Yes
  | Maps x y f m =>
    let fix go n : [formula_denote vars defs (Maps x y f n)
                      -> formula_denote vars defs t] :=
        match n with
        | Empty => No
        | Add x' y' f' m' =>
          match define x x' defs with
          | Some defs' =>
            match define y y' defs' with
            | Some defs'' =>
              match define f f' defs'' with
              | Some defs''' => cont vars defs''' || go m'
              | None => Reduce (go m')
              end
            | None => Reduce (go m')
            end
          | None => Reduce (go m')
          end
        end in go m
  | MapsAny x y Empty => Yes
  | MapsAny x y m =>
    let fix go n : [formula_denote vars defs (MapsAny x y n)
                      -> formula_denote vars defs t] :=
        match n with
        | Empty => No
        | Add x' y' f' m' =>
          match define x x' defs with
          | Some defs' =>
            match define y y' defs' with
            | Some defs'' => cont vars defs'' || go m'
            | None => Reduce (go m')
            end
          | None => Reduce (go m')
          end
        end in go m
  | Impl _ _ => Reduce (cont vars defs)
  end.
Next Obligation.
  simplify_maps.
    destruct H2.
    simpl in *.
    subst.
    apply oops.
  apply oops.
Defined.
Next Obligation.
  simplify_maps.
  clear go cont.
  destruct H2.
  simpl in *.
  subst.
  apply oops.
Defined.
Next Obligation.
  simplify_maps.
  clear go cont.
  destruct H2.
  simpl in *.
  subst.
  apply oops.
Defined.
Next Obligation.
  simplify_maps.
  clear go cont.
  destruct H2.
  simpl in *.
  subst.
  destruct y; simpl in Heq_anonymous.
    apply oops.
    apply oops.
Defined.
Next Obligation.
  simplify_maps.
  clear go cont.
  destruct H2.
  simpl in *.
  subst.
  destruct y; simpl in Heq_anonymous.
    apply oops.
    apply oops.
Defined.
Next Obligation.
  apply F.empty_in_iff in H.
  contradiction.
Defined.
Next Obligation.
  apply F.add_in_iff in H1.
  destruct H1; auto.
  clear go cont.
  destruct H1.
  simpl in *.
  (* destruct x, y; simpl in *. *)
  (* repeat (rewrite no_subst_formula in H; auto); auto. *)
  apply oops.
  apply oops.
Defined.
Next Obligation.
  apply oops.
Defined.
Next Obligation.
  apply F.add_in_iff in H1.
  destruct H1; auto.
  clear H0 go cont.
  destruct H1.
  simpl in *.
  apply oops.
Defined.
Next Obligation.
  apply F.add_in_iff in H1.
  destruct H1; auto.
  clear H0 go cont.
  destruct H1.
  simpl in *.
  apply oops.
Defined.

Lemma map_contains_MapsTo vars defs x y f m :
  Some f = map_contains vars defs x y m
    -> M.MapsTo (x, y) f (map_expr_denote vars defs m).
Proof.
  intros.
  apply F.find_mapsto_iff.
  induction m; simpl; intros.
    discriminate.
  simpl in *.
  destruct (N.eq_dec x n); subst.
    destruct (N.eq_dec y n0); subst.
      inversion H; subst.
      simplify_maps.
    rewrite F.add_neq_o; auto; simpl.
    apply not_and_implication; congruence.
  rewrite F.add_neq_o; auto; simpl.
  apply not_and_implication; congruence.
Qed.

Program Fixpoint formula_backward (t : formula)
        (vars : positive -> N) (defs : list (positive * N))
        {wf subterm t} : [formula_denote vars defs t] :=
  match t with
  | Maps x y f m =>
    match map_contains vars defs (term_denote vars defs x)
                       (term_denote vars defs y) m with
    | Some f' => Reduce (N.eq_dec f' (term_denote vars defs f))
    | None => No
    end
  | MapsAny x y m =>
    match map_contains vars defs (term_denote vars defs x)
                       (term_denote vars defs y) m with
    | Some _ => Yes
    | None => No
    end
  | Impl p q =>
    formula_forward q vars defs p
                    (fun vars' defs' => formula_backward q vars' defs')
  end.
Next Obligation.
  apply map_contains_MapsTo; auto.
Defined.
Next Obligation.
  apply in_mapsto_iff.
  eexists.
  apply map_contains_MapsTo; auto.
  apply Heq_anonymous.
Defined.
Next Obligation.
  destruct q; constructor.
Defined.
Next Obligation. apply measure_wf, subterm_wf. Defined.

Print Assumptions formula_backward_func.

Goal
  if formula_backward
       (Impl (Maps (Var 1%positive) (Var 2%positive) (Var 3%positive)
                   (Add 1%N 1%N 1%N Empty))
             (Maps (Var 1%positive) (Var 2%positive) (Var 3%positive)
                   (Add 1%N 1%N 1%N Empty)))
       (fun v => 9%N) nil then True else False.
Proof.
  vm_compute.
  constructor.
Qed.

Definition formula_tauto : ∀ (vars : positive -> N) (t : formula),
  [formula_denote vars nil t].
Proof.
  intros; refine (Reduce (formula_backward t vars nil)); auto.
Defined.

Require Import Coq.quote.Quote.

Definition partialOut (P : Prop) (x : [P]) :=
  match x return (match x with
                  | Proved _ _ => P
                  | Uncertain _ => True
                  end) with
  | Proved _ pf => pf
  | Uncertain _ => I
  end.

Ltac inList x xs :=
  match xs with
  | tt => false
  | (x, _) => true
  | (_, ?xs') => inList x xs'
  end.

Ltac addToList x xs :=
  let b := inList x xs in
  match b with
  | true => xs
  | false => constr:((x, xs))
  end.

Ltac lookup x xs :=
  match xs with
  | (x, _) => constr:(1%positive)
  | (_, ?xs') =>
    let n := lookup x xs' in
    constr:(Pos.succ n)
  end.

Ltac functionalize xs :=
  let rec loop n xs' :=
    lazymatch xs' with
    | (?x, tt) => constr:(fun _ : positive => x)
    | (?x, ?xs'') =>
      let f := loop (Pos.succ n) xs'' in
      constr:(fun m : positive => if (m =? n)%positive then x else f m)
    end in
  loop (1%positive) xs.

Ltac allVar xs e :=
  match e with
  | N0 => xs
  | Npos _ => xs
  | ?x => addToList x xs
  end.

Ltac allVars xs e :=
  match e with
  | M.MapsTo (?X, ?Y) ?F _ =>
    let xs := allVar xs X in
    let xs := allVar xs Y in
    allVar xs F
  | M.In (?X, ?Y) _ =>
    let xs := allVar xs X in
    allVar xs Y
  | ?P -> ?Q =>
    let xs := allVars xs P in
    allVars xs Q
  | _ => xs
  end.

Ltac reifyValue env t :=
  match t with
  | N0 => constr:(Value N0)
  | Npos ?X =>
    constr:(Value (Npos X))
  | ?X =>
    let v := lookup X env in
    constr:(Var v)
  end.

Ltac reifyMapTerm env t :=
  match t with
  | M.empty _ => constr:(Empty)
  | M.add (?x, ?y) ?f ?M =>
    let m := reifyMapTerm env M in
    constr:(Add x y f m)
  end.

Ltac reifyTerm env t :=
  match t with
  | M.MapsTo (?X, ?Y) ?F ?M =>
    let x := reifyValue env X in
    let y := reifyValue env Y in
    let f := reifyValue env F in
    let m := reifyMapTerm env M in
    constr:(Maps x y f m)
  | M.In (?X, ?Y) ?M =>
    let x := reifyValue env X in
    let y := reifyValue env Y in
    let m := reifyMapTerm env M in
    constr:(MapsAny x y m)
  | ?P -> ?Q =>
    let p := reifyTerm env P in
    let q := reifyTerm env Q in
    constr:(Impl p q)
  end.

Ltac reify' :=
  match goal with
  | [ |- ?X ] =>
    let xs  := allVars tt X in
    let env := functionalize xs in
    let r1  := reifyTerm xs X in
    pose xs;
    pose env;
    pose r1
  end.

Ltac reify :=
  match goal with
  | [ |- ?X ] =>
    let xs  := allVars tt X in
    let env := functionalize xs in
    let r1  := reifyTerm xs X in
    (* pose xs; *)
    (* pose env; *)
    (* pose r1; *)
    change (formula_denote env nil r1)
  end.

Lemma formula_sound vars t :
  (if formula_tauto vars t then True else False) -> formula_denote vars nil t.
Proof.
  unfold formula_tauto.
  destruct t; simpl; intros.
  - induction m; simpl in *.
      contradiction.
    destruct (formula_backward (Maps _ _ _ (Add _ _ _ m)) vars []) eqn:?; auto.
    contradiction.
  - induction m; simpl in *.
      contradiction.
    destruct (formula_backward (MapsAny _ _ (Add _ _ _ m)) vars []) eqn:?; auto.
    contradiction.
  - destruct (formula_backward (Impl _ _) vars []) eqn:?; auto.
    contradiction.
Qed.

Ltac solve_map := reify; apply formula_sound; vm_compute; auto.

Example map_decide_test  x y f :
  M.MapsTo (elt:=N) (x, y) f (M.add (0%N, 0%N) 0%N (M.add (1%N, 1%N) 1%N (M.empty _))) ->
  M.MapsTo (elt:=N) (x, y) f (M.add (0%N, 0%N) 0%N (M.add (1%N, 1%N) 1%N (M.empty _))).
Proof. solve_map. Qed.

Time Program Definition Zero : Metacategory := {|
  pairs := [map]
|}.

Ltac prepare_maps :=
  repeat lazymatch goal with
  | [ |- ∃ v, M.find _ _ = Some v ] =>
    apply find_mapsto_iff_ex, in_mapsto_iffT
  | [ |- M.find _ _ = Some _ ] =>
    apply F.find_mapsto_iff
  | [ H : M.find _ (M.empty _) = Some _ |- _ ] => inversion H
  | [ H : M.find _ _ = Some ?F |- _ ] =>
    apply F.find_mapsto_iff in H; revert H
  | [ H : M.MapsTo _ _ (M.empty _) |- _ ] =>
    contradiction (proj1 (F.empty_mapsto_iff _ _) H)
  end.

Ltac map_decide := prepare_maps; solve_map.

(* This first tactic is the Ltac-based reflection; the second uses
   computational reflection. *)
(* Local Obligation Tactic := reflect_on_maps. *)
Local Obligation Tactic :=
  repeat eexists; simpl; try split; intros;
  first [ map_decide
        | instantiate (1:=0%N); map_decide
        | instantiate (1:=1%N); map_decide
        | instantiate (1:=2%N); map_decide
        | instantiate (1:=3%N); map_decide
        | instantiate (1:=4%N); map_decide
        | instantiate (1:=5%N); map_decide ].

Time Program Definition One : Metacategory := {|
  pairs := [map (0, 0) +=> 0 ]%N
|}.

(* jww (2017-07-02): At the moment eexists is being called too early, causing
   all compositions to be 0. The computational decision procedure needs to
   take existentials into account. *)

Time Program Definition Two : Metacategory := {|
  pairs := [map (0, 0) +=> 0
           ;    (1, 1) +=> 1

           ;    (2, 0) +=> 2
           ;    (1, 2) +=> 2 ]%N
|}.

Time Program Definition Three : Metacategory := {|
  pairs := [map (0, 0) +=> 0
           ;    (1, 1) +=> 1
           ;    (2, 2) +=> 2

           ;    (3, 0) +=> 3
           ;    (1, 3) +=> 3

           ;    (4, 1) +=> 4
           ;    (2, 4) +=> 4

           ;    (5, 0) +=> 5
           ;    (2, 5) +=> 5
           ;    (4, 3) +=> 5 ]%N
|}.

(* Using rewriting and other theorems, this instance takes 481s to define.
   Using computational reflection, it takes 0.3s. *)

Local Obligation Tactic := intros.

Time Program Definition Four : Metacategory := {|
  pairs := [map (0, 0) +=> 0
           ;    (1, 1) +=> 1
           ;    (2, 2) +=> 2
           ;    (3, 3) +=> 3

           ;    (4, 0) +=> 4
           ;    (1, 4) +=> 4

           ;    (5, 1) +=> 5
           ;    (2, 5) +=> 5

           ;    (6, 2) +=> 6
           ;    (3, 6) +=> 6

           ;    (7, 0) +=> 7
           ;    (2, 7) +=> 7

           ;    (8, 1) +=> 8
           ;    (3, 8) +=> 8

           ;    (9, 0) +=> 9
           ;    (3, 9) +=> 9

           ;    (5, 4) +=> 7
           ;    (6, 5) +=> 8
           ;    (7, 6) +=> 9
           ;    (8, 4) +=> 9 ]%N
|}.
Next Obligation. Admitted.
Next Obligation.
  simpl in *.
  split; intros.
  -

(* Print Assumptions Four_obligation_1. *)

Ltac reflect_on_pairs X Y F D C :=
  repeat (
    destruct X using peano_rect';
    first
      [ elimobj D | elimobj C
      | repeat (
          destruct Y using peano_rect';
          first
            [ elimobj D | elimobj C
            | repeat (
                destruct F using peano_rect';
                first
                  [ elimobj D | elimobj C
                  | intuition idtac
                  | reflect_on_pairs ]) ]) ]);
  intuition.

Require Import Category.Instance.Two.

Monomorphic Lemma object_Two_rect :
  ∀ (P : object Two -> Type),
  (∀ x, obj_arr Two x = 0%N -> P x) ->
  (∀ x, obj_arr Two x = 1%N -> P x) ->
  ∀ (x : object Two), P x.
Proof.
  intros; destruct x.
  repeat (destruct obj_arr0 using peano_rect'; elimobj obj_def0 || auto).
Defined.

Program Definition Two_2_object (x : object Two) : TwoObj.
Proof.
  induction x using object_Two_rect.
  - exact TwoX.
  - exact TwoY.
Defined.

Monomorphic Lemma morphism_Two_rect :
  ∀ {x y : object Two} (P : morphism Two x y -> Type),
  (∀ f, obj_arr Two x = 0%N -> obj_arr Two y = 0%N -> mor_arr Two f = 0%N -> P f) ->
  (∀ f, obj_arr Two x = 1%N -> obj_arr Two y = 1%N -> mor_arr Two f = 1%N -> P f) ->
  (∀ f, obj_arr Two x = 0%N -> obj_arr Two y = 1%N -> mor_arr Two f = 2%N -> P f) ->
  ∀ (f : morphism Two x y), P f.
Proof.
  intros; destruct x, y, f.
  reflect_on_pairs obj_arr0 obj_arr1 mor_arr0 mor_dom0 mor_cod0.
Defined.

Program Definition Two_2_morphism (x y : object Two) (f : morphism Two x y) :
  TwoHom (Two_2_object x) (Two_2_object y).
Proof.
  induction f using morphism_Two_rect;
  destruct x, y, f; simpl in *; subst; simpl.
  - exact TwoIdX.
  - exact TwoIdY.
  - exact TwoXY.
Defined.

(*
Local Obligation Tactic := intros.

Program Definition Two_to_Two : Category_from_Metacategory Two ⟶ _2 := {|
  fobj := Two_2_object;
  fmap := Two_2_morphism
|}.
Next Obligation.
  proper.
  destruct x0, y0; simpl in X; subst.
  apply f_equal.
  apply f_equal2;
  apply Eqdep_dec.UIP_dec;
  decide equality;
  apply N.eq_dec.
Qed.
Next Obligation.
  simpl.
  induction x using object_Two_rect;
  destruct x;
  simpl in H; subst;
  vm_compute; reflexivity.
Qed.
Next Obligation.
  simpl in *.
  induction f using morphism_Two_rect;
  induction g using morphism_Two_rect;
  destruct x, y, z, f, f0;
  simpl in H, H0, H1, H2, H3, H4; subst;
  (elimtype False; simpl in *; discriminate)
    || (vm_compute; reflexivity).
Qed.

Local Obligation Tactic :=
  program_simpl;
  try solve [ subst; unfold composite; simpl;
              subst; vm_compute; reflexivity ].

Program Definition _2_Two_object (x : TwoObj) : object Two :=
  match x with
  | TwoX => {| obj_arr := 0%N; obj_def := _; obj_id  := _ |}
  | TwoY => {| obj_arr := 1%N; obj_def := _; obj_id  := _ |}
  end.
Next Obligation.
  unfold is_identity, defined, composite;
  simpl; split; intros; destruct H; subst;
  rewrite e; destruct_maps.
Defined.
Next Obligation.
  unfold is_identity, defined, composite;
  simpl; split; intros; destruct H; subst;
  rewrite e; destruct_maps.
Defined.

Program Definition _2_Two_morphism (x y : TwoObj) (f : TwoHom x y) :
  morphism Two (_2_Two_object x) (_2_Two_object y) :=
  match x as x' in TwoObj
  return x = x' -> morphism Two (_2_Two_object x) (_2_Two_object y) with
  | TwoX => fun _ =>
    match y as y' in TwoObj
    return y = y' -> morphism Two (_2_Two_object x) (_2_Two_object y) with
    | TwoX => fun _ => {| mor_arr := 0%N; mor_dom := _; mor_cod := _ |}
    | TwoY => fun _ => {| mor_arr := 2%N; mor_dom := _; mor_cod := _ |}
    end eq_refl
  | TwoY => fun _ =>
    match y as y' in TwoObj
    return y = y' -> morphism Two (_2_Two_object x) (_2_Two_object y) with
    | TwoY => fun _ => {| mor_arr := 1%N; mor_dom := _; mor_cod := _ |}
    | TwoX => fun _ => !
    end eq_refl
  end eq_refl.
Next Obligation. inversion f. Defined.

Local Obligation Tactic := program_simpl.

Program Definition Two_from_Two : _2 ⟶ Category_from_Metacategory Two := {|
  fobj := _2_Two_object;
  fmap := _2_Two_morphism
|}.
Next Obligation. destruct x; reflexivity. Defined.
Next Obligation.
  destruct f; simpl;
  destruct x; simpl;
  spose (TwoHom_inv _ _ g) as H; subst;
  contradiction || reflexivity.
Defined.

Require Import Category.Instance.Cat.

Program Instance Two_iso_2 : Category_from_Metacategory Two ≅ _2 := {
  to   := Two_to_Two;
  from := Two_from_Two
}.
Next Obligation.
  unshelve eexists; intros.
    induction x; reflexivity.
  induction f; reflexivity.
Qed.
Next Obligation.
  unshelve eexists; intros.
    induction x using object_Two_rect;
    destruct x; simpl in H; subst.
    { isomorphism; simpl.
      - construct; [exact 0%N|..]; auto.
      - construct; [exact 0%N|..]; auto.
      - reflexivity.
      - reflexivity.
    }
    { isomorphism; simpl.
      - construct; [exact 1%N|..]; auto.
      - construct; [exact 1%N|..]; auto.
      - reflexivity.
      - reflexivity.
    }
  induction f using morphism_Two_rect;
  destruct x, y, f;
  simpl in H, H0, H1; subst;
  vm_compute; reflexivity.
Qed.
*)
