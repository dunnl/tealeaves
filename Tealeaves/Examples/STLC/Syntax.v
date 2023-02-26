(*|
############################################################
Formalizing STLC with Tealeaves
############################################################
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Kleisli presentation
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This file gives a tutorial on proving the decorated traversable monad
laws the for the syntax of the simply-typed lambda calculus (STLC).

.. contents:: Table of Contents
   :depth: 2

============================
Imports and setup
============================

Since we are using the Kleisli typeclass hierarchy, we import modules under
the namespaces ``Classes.Kleisli`` and ``Theory.Kleisli.``
|*)
From Tealeaves Require Export
  Backends.LN
  (* Locally nameless infrastructure *)
  Classes.Kleisli.DT.Monad
  (* DTM definition *)
  Data.Natural
  (* Monoid of natural numbers *)
  Functors.List
  (* List functor *)
  Classes.Kleisli.DT.Functor.
  (* foldMapd operation *)

Export DT.Functor.Notations. (* ∈d *)
Import Monoid.Notations. (* Ƶ and ● *)
Export Classes.Kleisli.DT.Monad.Derived. (* DTM sub-instances *)
Export Applicative.Notations. (* <⋆> *)
Export DT.Monad.Notations. (* ⋆dtm *)
Export List.ListNotations. (* [] :: *)
Export LN.Notations. (* operations *)
Export LN.AtomSet.Notations.
Export LN.AssocList.Notations. (* one, ~ *)
Export Product.Notations. (* × *)
Export Setlike.Functor.Notations. (* ∈ *)

#[local] Generalizable Variables G.

#[local] Set Implicit Arguments.

(** * Language definition *)
(******************************************************************************)
Parameter base_typ : Type.

Inductive typ :=
| base : base_typ -> typ
| arr : typ -> typ -> typ.

Coercion base : base_typ >-> typ.

Inductive term (v : Type) :=
| tvar : v -> term v
| lam : typ -> term v -> term v
| app : term v -> term v -> term v.

(** ** Notations and automation *)
(******************************************************************************)
Module Notations.
  Notation "'λ'" := (lam) (at level 45).
  Notation "[ t1 ]@[ t2 ]" := (app t1 t2) (at level 80).
  Notation "A ⟹ B" := (arr A B) (at level 40).
End Notations.

Import Notations.

#[export] Instance: Return term := tvar.

(*|
========================================
Definition of binddt
========================================
|*)
Fixpoint binddt_term (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f : nat * v1 -> G (term v2)) (t : term v1) : G (term v2) :=
  match t with
  | tvar v => f (0, v)
  | lam τ body => pure G (lam τ) <⋆> binddt_term (preincr 1 f) body
  | app t1 t2 => pure G (@app v2) <⋆> binddt_term f t1 <⋆> binddt_term f t2
  end.

#[export] Instance: Binddt nat term term := @binddt_term.

(*|
========================================
Some rewriting principles for binddt
========================================

These definitional equalities help prove the composition law later.

|*)

Section binddt_helpers.

  Generalizable Variable F.
  Context
    `{Applicative F}
      {v1 v2 v3 : Type}
      (f : nat * v1 -> F (term v2)).

  Notation "'P'" := pure.
  Notation "'BD'" := (binddt term).

  Lemma binddt_lam :
    forall (τ : typ), BD F f ∘ (@lam v1 τ) = (precompose (BD F (preincr 1 f)) ∘ ap F ∘ P F) (@lam v2 τ).
  Proof.
    reflexivity.
  Qed.

  Lemma binddt_app :
      compose (BD F f) ∘ @app v1 = (compose (precompose (BD F f) ∘ ap F) ∘ precompose (BD F f) ∘ ap F ∘ P F) (@app v2).
  Proof.
    reflexivity.
  Qed.

End binddt_helpers.

(*|
========================================
An overview of the DTM axioms
========================================
|*)

Section laws.

  (* Generalize over (Coq) variables used for object-level variables
   and symbols for applicative homomorphisms. *)
  Generalizable Variables v ϕ.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Composition with unit (left unit law)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The "composition with unit" law (or left unit law) establishes that
the atomic expression `ret term v`

1. consists just of variable `v`
2. inside an empty binding context

In this law, `ret (list β ×)` is the operation which lifts any `v`
into an empty binding context to get `([], v)`. A simpler way of
writing the left unit law is then

`binddt f (ret term v) = f ([], v)`

The proof of this rule ought to follow merely from the definitions of
`binddt` and `ret`.  In the course of proofs about `binddt f t` by
induction of the syntax of expression `t`, the left unit law acts as
a base case.

.. coq::
   :name: dtm1
|*)
  Ltac solve_dtm1 :=
    intros; now try ext var.

  Theorem dtm1_stlc:
    forall (A B : Type) (G : Type -> Type) (H1 : Fmap G) (H2 : Pure G) (H3 : Mult G), Applicative G ->
       forall f : nat * A -> G (term B),
         binddt term G f ∘ ret term = f ∘ ret (prod nat).
  Proof.
    reflexivity.
  Qed.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Identity law (right unit law)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The identity law (or right unit law) establishes that applying the
substitution rule

`pure F ∘ ret term ∘ extract ((list β) ×)`

to each of the variables in expression `t` acts as the pure effect on
`t`. The substitution rule is the one which at each variable

1. throws away the binding context: `list β * v -> v`
2. coerces the variable into an atomic expression: `v -> term v`
3. and lifts the result into `F` with the `pure` effect: `term v -> F (term v)`

.. coq::
   :name: dtm2
|*)

  Generalizable All Variables.

  Lemma dtm2_helper : forall `{Monoid M} (m : M) `(f : A -> B), preincr m (f ∘ extract (M ×)) = f ∘ extract (M ×).
  Proof.
    intros. unfold preincr. reassociate ->. now rewrite (extract_incr).
  Qed.

  Theorem dtm2_stlc : forall A : Type, binddt term (fun A0 : Type => A0) (ret term ∘ extract (prod nat)) = @id (term A).
  Proof.
    intros. ext t.
    induction t. (* .unfold *)
    - cbn. reflexivity.
    - cbn. rewrite dtm2_helper. now rewrite IHt.
    - cbn. now rewrite IHt1, IHt2.
  Qed.

  Ltac rewrite_with_bind_hyp :=
    match goal with
    | H : context[binddt] |- _ => rewrite H
    end.

  Ltac induction_on_term :=
    match goal with
    | t : term ?v |- _ => induction t
    end.

  Ltac solve_dtm2_case :=
    try rewrite dtm2_helper;
    now repeat rewrite_with_bind_hyp.

  Theorem dtm2_stlc_automated : forall A : Type, binddt term (fun A0 : Type => A0) (ret term ∘ extract (prod nat)) = @id (term A).
    intros. ext t.
    induction_on_term; cbn;
      solve_dtm2_case.
  Qed.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~
Composition law
~~~~~~~~~~~~~~~~~~~~~~~~

The composition law states the following:

`fmap F (binddt g) ∘ binddt f = binddt (g ⋆ f)`

The right-hand side may be written more explicitly as

`binddt (fun '(w, x) => fmap F (binddt (F := G) (g ∘ incr w)) (f (w, x))))`

This law is an analogue of the ordinary monad composition law

`bind g ∘ bind f = bind (bind g ∘ f)`.

Both are loosely of the form

`bind g ∘ bind f = bind (g ∗ f)`

A close comparison shows the rules differ in two respects:

1. The call to `g` in `bind g` is replaced with a call to `(g ∘ incr
   w)` where `w` is the context seen by the function `f`.
2. The call to `binddt (g ∘ incr w)` is wrapped in `fmap F`. This is
   required to map over the applicative effect of type `F` generated
   by the application of `f`.

.. coq::
   :name: dtm3
|*)

  Notation "'P'" := pure.
  Notation "'F'" := fmap.
  Notation "'BD'" := (binddt term).

  Ltac dtm3_lhs_step G1 :=
    repeat rewrite fmap_ap; (* Bring LHS <<fmap>> up to the constructor *)
    rewrite (app_pure_natural G1). (* Fuse <<fmap>> and the <<pure (constructor)>> *)

  Ltac dtm3_rhs_step G2 G1 :=
    (rewrite_strat innermost (terms (ap_compose2 G2 G1)));
    repeat rewrite fmap_ap;
    rewrite (app_pure_natural G1);
    rewrite <- ap_fmap;
    repeat rewrite fmap_ap;
    rewrite (app_pure_natural G1).

  Set Keyed Unification.

  Theorem dtm3_stlc :
    forall (A B C : Type) (G1 : Type -> Type) (H1 : Fmap G1) (H2 : Pure G1) (H3 : Mult G1),
      Applicative G1 ->
      forall (G2 : Type -> Type) (H5 : Fmap G2) (H6 : Pure G2) (H7 : Mult G2),
        Applicative G2 ->
        forall (g : nat * B -> G2 (term C)) (f : nat * A -> G1 (term B)),
          fmap G1 (binddt term G2 g) ∘ binddt term G1 f = binddt term (G1 ∘ G2) (g ⋆dtm f).
  Proof.
    intros. ext t.
    generalize dependent g.
    generalize dependent f.
    unfold compose at 1.
    induction t; intros f g.
    - cbn. change (preincr 0 g) with (preincr Ƶ g).
      now rewrite Decorated.Monad.preincr_zero.
    - cbn.
      rewrite <- (kcompose_dtm_preincr nat term).
      rewrite <- IHt.
      (* left side *)
      repeat rewrite fmap_ap. (* Bring LHS <<fmap>> up to the constructor *)
      rewrite (app_pure_natural G1). (* Fuse <<fmap>> and the <<pure (constructor)>> *)
      (* right side, constructor *)
      unfold_ops @Pure_compose.
      (* right side, first argument *)
      rewrite_strat innermost (terms (ap_compose2 G2 G1)).
      rewrite (app_pure_natural G1).
      rewrite <- ap_fmap.
      rewrite (app_pure_natural G1).
      reflexivity.
    - cbn.
      rewrite <- IHt1.
      rewrite <- IHt2.
      (* left side *)
      do 2 rewrite fmap_ap.
      rewrite (app_pure_natural G1).
      (* right side *)
      (* right side, constructor *)
      unfold_ops @Pure_compose.
      (* right side, first argument *)
      rewrite_strat innermost (terms (ap_compose2 G2 G1)).
      repeat rewrite fmap_ap.
      rewrite (app_pure_natural G1).
      rewrite <- ap_fmap.
      repeat rewrite fmap_ap.
      rewrite (app_pure_natural G1).
      (* right side, second argument *)
      rewrite_strat innermost (terms (ap_compose2 G2 G1)).
      repeat rewrite fmap_ap.
      rewrite (app_pure_natural G1).
      rewrite <- ap_fmap.
      repeat rewrite fmap_ap.
      rewrite (app_pure_natural G1).
      reflexivity.
  Qed.

  Theorem dtm3_stlc_automated :
    forall (A B C : Type) (G1 : Type -> Type) (H1 : Fmap G1) (H2 : Pure G1) (H3 : Mult G1),
      Applicative G1 ->
      forall (G2 : Type -> Type) (H5 : Fmap G2) (H6 : Pure G2) (H7 : Mult G2),
        Applicative G2 ->
        forall (g : nat * B -> G2 (term C)) (f : nat * A -> G1 (term B)),
          fmap G1 (binddt term G2 g) ∘ binddt term G1 f = binddt term (G1 ∘ G2) (g ⋆dtm f).
  Proof.
    intros. ext t.
    unfold compose at 1.
    generalize dependent g.
    generalize dependent f.
    induction_on_term; intros f g.
    - cbn. change (preincr 0 g) with (preincr Ƶ g).
      now rewrite Decorated.Monad.preincr_zero.
    - cbn.
      rewrite <- (kcompose_dtm_preincr nat term g f).
      rewrite <- IHt.
      dtm3_lhs_step G1.
      dtm3_rhs_step G2 G1.
      reflexivity.
    - cbn.
      dtm3_lhs_step G1.
      rewrite <- IHt1.
      rewrite <- IHt2.
      dtm3_rhs_step G2 G1.
      dtm3_rhs_step G2 G1.
      reflexivity.
  Qed.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Applicative homomorphism law
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This law states that `binddt` is parametric with respect to
applicative functors in the sense that it commutes with their
homomorphisms. It is (probably?) a free theorem, so it is not actually
a restriction on implementations of `binddt` (cite Gibbons).


.. coq::
   :name: dtm4
|*)

  Theorem dtm4_stlc :
    forall (G1 G2 : Type -> Type) (H1 : Fmap G1) (H2 : Pure G1) (H3 : Mult G1) (H4 : Fmap G2) (H5 : Pure G2) (H6 : Mult G2)
      (ϕ : forall A : Type, G1 A -> G2 A), ApplicativeMorphism G1 G2 ϕ ->
      forall (A B : Type) (f : nat * A -> G1 (term B)),
        ϕ (term B) ∘ binddt term G1 f = binddt term G2 (ϕ (term B) ∘ f).
  Proof.
    intros. ext t.
    inversion H.
    generalize dependent f.
    unfold compose at 1.
    induction t; intro f. (* .unfold *)
    - reflexivity.
    - cbn.
      repeat rewrite ap_morphism_1.
      rewrite appmor_pure.
      rewrite IHt.
      reflexivity.
    - cbn.
      repeat rewrite ap_morphism_1.
      rewrite appmor_pure.
      rewrite IHt1.
      rewrite IHt2.
      reflexivity.
  Qed.

  Theorem dtm4_automated :
    forall (G1 G2 : Type -> Type) (H1 : Fmap G1) (H2 : Pure G1) (H3 : Mult G1) (H4 : Fmap G2) (H5 : Pure G2) (H6 : Mult G2)
      (ϕ : forall A : Type, G1 A -> G2 A),
      ApplicativeMorphism G1 G2 ϕ ->
      forall (A B : Type) (f : nat * A -> G1 (term B)),
        ϕ (term B) ∘ binddt term G1 f = binddt term G2 (ϕ (term B) ∘ f).
  Proof.
    intros. ext t.
    inversion H.
    unfold compose at 1.
    generalize dependent f.
    induction t; intro f; cbn.
    - reflexivity.
    - repeat rewrite ap_morphism_1.
      rewrite appmor_pure.
      rewrite IHt.
      reflexivity.
    - repeat rewrite ap_morphism_1.
      rewrite appmor_pure.
      rewrite IHt1.
      rewrite IHt2.
      reflexivity.
  Qed.

  #[export] Instance: DT.Monad.Monad nat term :=
    {| kdtm_binddt0 := dtm1_stlc;
       kdtm_binddt1 := dtm2_stlc;
       kdtm_binddt2 := dtm3_stlc;
       kdtm_morph := dtm4_stlc;
    |}.

End laws.

Section test_notations.

  Context
    (β : Type)
    (x y z : atom)
    (b : β) (τ : typ).

  Check 1.
  Check (λ τ (tvar (Bd 1))).
  Check (λ τ (tvar (Fr x))).
  Check [λ τ (tvar (Bd 1))]@[tvar (Fr x)].
  Check [λ τ (tvar (Fr x))]@[tvar (Bd 0)].
  Check λ τ ([(tvar (Bd 1))]@[tvar (Fr x)]).
  Check λ τ ([(tvar (Fr x))]@[tvar (Bd 0)]).

End test_notations.

Definition ctx := list (atom * typ).

Reserved Notation "Γ ⊢ t : S" (at level 90, t at level 99).

Inductive Judgment : ctx -> term LN -> typ -> Prop :=
| j_var :
    forall (Γ : ctx) (x : atom) (A : typ),
      uniq Γ ->
      (x, A) ∈ Γ ->
      Γ ⊢ tvar (Fr x) : A
| j_abs :
    forall (L : AtomSet.t) Γ (τ1 τ2 : typ) (t : term LN),
      (forall x : atom, ~ AtomSet.In x L -> Γ ++ x ~ τ1 ⊢ t '(tvar (Fr x)) : τ2) ->
      Γ ⊢ λ τ1 t : τ1 ⟹ τ2
| j_app :
    forall Γ (t1 t2 : term LN) (A B : typ),
      Γ ⊢ t1 : A ⟹ B ->
      Γ ⊢ t2 : A ->
      Γ ⊢ [t1]@[t2] : B
where "Γ ⊢ t : A" := (Judgment Γ t A).


(** * Rewriting lemmas for high-level operations *)
(******************************************************************************)

From Tealeaves Require Export
  Classes.Listable.Functor
  (* <<Tolist>> operation *)
  Classes.Kleisli.Traversable.Functor.
(* <<Tolist>> instance for Traversable functors *)



(** ** Rewriting lemmas for <<tolist>>, <<toset>> *)
(******************************************************************************)
Section term_list_rewrite.

  Variable
    (A : Type).

  Lemma tolist_term_1 : forall (x : A),
    tolist term (tvar x) = [x].
  Proof.
    reflexivity.
  Qed.

  Lemma tolist_term_2 : forall (X : typ) (t : term A),
    tolist term (lam X t) = tolist term t.
  Proof.
    intros. cbn.
    rewrite dtm2_helper.
    reflexivity.
  Qed.

  Lemma tolist_term_3 : forall (t1 t2 : term A),
      tolist term (app t1 t2) = tolist term t1 ++ tolist term t2.
  Proof.
    reflexivity.
  Qed.

  Lemma in_term_1 : forall (x y : A),
      x ∈ tvar y <-> x = y.
  Proof.
    intros.
    rewrite (in_iff_in_tolist term).
    rewrite tolist_term_1.
    now simpl_list.
  Qed.

  Lemma in_term_2 : forall (y : A) (X : typ) (t : term A),
    y ∈ (lam X t) <-> y ∈ t.
  Proof.
    intros.
    do 2 rewrite (in_iff_in_tolist term).
    rewrite tolist_term_2.
    reflexivity.
  Qed.

  Lemma in_term_3 : forall (t1 t2 : term A) (y : A),
      y ∈ (app t1 t2) <-> y ∈ t1 \/ y ∈ t2.
  Proof.
    intros.
    do 3 rewrite (in_iff_in_tolist term).
    rewrite tolist_term_3.
    now simpl_list.
  Qed.

End term_list_rewrite.

(** ** Rewriting lemmas for <<free>>, <<freeset>> *)
(******************************************************************************)
Section term_free_rewrite.

  Variable (A : Type).

  Lemma term_free11 : forall (b : nat) (x : atom),
      x ∈ free term (tvar (Bd b)) <-> False.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma term_free12 : forall (y : atom) (x : atom),
      x ∈ free term (tvar (Fr y)) <-> x = y.
  Proof.
    intros. cbn. intuition.
  Qed.

  Lemma term_free2 : forall (x : atom) (t : term LN) (X : typ),
      x ∈ free term (lam X t) <-> x ∈ free term t.
  Proof.
    intros. rewrite in_free_iff. rewrite in_term_2.
    now rewrite <- in_free_iff.
  Qed.

  Lemma term_free3 : forall (x : atom) (t1 t2 : term LN),
      x ∈ free term (app t1 t2) <-> x ∈ free term t1 \/ x ∈ free term t2.
  Proof.
    intros. rewrite in_free_iff. rewrite in_term_3.
    now rewrite <- 2(in_free_iff).
  Qed.

  Lemma term_in_freeset11 : forall (b : nat) (x : atom),
      AtomSet.In x (freeset term (tvar (Bd b))) <-> False.
  Proof.
    intros. rewrite <- free_iff_freeset.
    now rewrite term_free11.
  Qed.

  Lemma term_in_freeset12 : forall (y : atom) (x : atom),
      AtomSet.In x (freeset term (tvar (Fr y))) <-> x = y.
  Proof.
    intros. rewrite <- free_iff_freeset.
    now rewrite term_free12.
  Qed.

  Lemma term_in_freeset2 : forall (x : atom) (t : term LN) (X : typ),
      AtomSet.In x (freeset term (lam X t)) <-> AtomSet.In x (freeset term t).
  Proof.
    intros. rewrite <- 2(free_iff_freeset). now rewrite term_free2.
  Qed.

  Lemma term_in_freeset3 : forall (x : atom) (t1 t2 : term LN),
      AtomSet.In x (freeset term (app t1 t2)) <-> AtomSet.In x (freeset term t1) \/ AtomSet.In x (freeset term t2).
  Proof.
    intros. rewrite <- 3(free_iff_freeset). now rewrite term_free3.
  Qed.

  Lemma term_freeset11 : forall (b : nat) (x : atom),
      freeset term (tvar (Bd b)) [=] ∅.
  Proof.
    intros. fsetdec.
  Qed.

  Lemma term_freeset12 : forall (y : atom),
      freeset term (tvar (Fr y)) [=] {{ y }}.
  Proof.
    intros. cbn. fsetdec.
  Qed.

  Lemma term_freeset2 : forall (t : term LN) (X : typ),
      freeset term (lam X t) [=] freeset term t.
  Proof.
    intros. unfold AtomSet.Equal; intro x.
    rewrite term_in_freeset2. reflexivity.
  Qed.

  Lemma term_freeset3 : forall (t1 t2 : term LN),
      freeset term (app t1 t2) [=] freeset term t1 ∪ freeset term t2.
  Proof.
    intros. unfold AtomSet.Equal; intro x.
    rewrite term_in_freeset3. fsetdec.
  Qed.

End term_free_rewrite.

(** ** Rewriting lemmas for <<foldMapd>> *)
(******************************************************************************)
Section term_foldMapd_rewrite.

  Context {A M : Type} (f : nat * A -> M) `{Monoid M}.

  Lemma term_foldMapd1 : forall (a : A),
      foldMapd term f (tvar a) = f (Ƶ, a).
  Proof.
    reflexivity.
  Qed.

  Lemma term_foldMapd2 : forall X (t : term A),
      foldMapd term f (λ X t) = foldMapd term (preincr 1 f) t.
  Proof.
    intros. cbv. change (op unit0 ?f) with (Ƶ ● f).
    now simpl_monoid.
  Qed.

  Lemma term_foldMapd3 : forall (t1 t2 : term A),
      foldMapd term f ([t1]@[t2]) = foldMapd term f t1 ● foldMapd term f t2.
  Proof.
    intros. cbv. change (op unit0 ?f) with (Ƶ ● f).
    now simpl_monoid.
  Qed.

End term_foldMapd_rewrite.

(** ** Rewriting lemmas for <<∈d>> *)
(******************************************************************************)
Section term_ind_rewrite.

  Lemma term_ind1 : forall (l1 l2 : LN) (n : nat),
      (n, l1) ∈d (tvar l2) <-> n = Ƶ /\ l1 = l2.
  Proof.
    introv. unfold_ops @Tosetd_Kleisli.
    rewrite term_foldMapd1.
    split.
    - now inversion 1.
    - inversion 1. now subst.
  Qed.

  Lemma term_ind2 : forall (t : term LN) (l : LN) (n : nat) (X : typ),
      (n, l) ∈d (λ X t) <-> (n - 1, l) ∈d t /\ n <> 0.
  Proof.
    introv. unfold_ops @Tosetd_Kleisli.
    rewrite term_foldMapd2; try typeclasses eauto.
    rewrite foldMapd_to_runBatch; try typeclasses eauto.
    rewrite foldMapd_to_runBatch; try typeclasses eauto.
    generalize dependent n.
    induction (toBatchd term False t); intro n.
    - cbn. unfold_ops @Pure_const. split.
      inversion 1. intros [H _]. inversion H.
    - cbn. unfold_ops @Monoid_op_set. unfold set_add.
      split.
      + intros [hyp|hyp].
        { rewrite IHb in hyp. split; intuition. }
        { clear IHb. unfold preincr, compose in hyp.
          destruct x. cbn in hyp. inverts hyp. split.
          - right. cbn. replace (n0 - 0) with n0 by lia.
            easy.
          - lia. }
      + intros [[hyp1|hyp1] hyp2].
        { rewrite IHb. now left. }
        { destruct x as [xn xl]. right.
          unfold preincr, compose, incr.
          inverts hyp1. unfold_ops @Monoid_op_plus.
          replace (1 + (n - 1))%nat with n by lia.
          easy. }
  Qed.

  Lemma term_ind3 : forall (t1 t2 : term LN) (n : nat) (l : LN),
      (n, l) ∈d ([t1]@[t2]) <-> (n, l) ∈d t1 \/ (n, l) ∈d t2.
  Proof.
    introv. unfold_ops @Tosetd_Kleisli.
    rewrite term_foldMapd3; try typeclasses eauto.
    reflexivity.
  Qed.

End term_ind_rewrite.

(** ** Rewriting lemmas for <<subst>> *)
(******************************************************************************)

(** ** Rewriting lemmas for <<locally_closed>> *)
(******************************************************************************)
Theorem term_lc_gap11 : forall (n : nat) (m : nat),
    locally_closed_gap term m (tvar (Bd n)) <-> n < m.
Proof.
  intros. unfold locally_closed_gap.
  split.
  - intros. specialize (H 0 (Bd n)).
    rewrite term_ind1 in H. specialize (H (ltac:(intuition))).
    apply H.
  - intros. cbn. rewrite term_ind1 in H0. destruct H0; subst.
    now simpl_monoid.
Qed.

Theorem term_lc_gap12 : forall (x : atom) (m : nat),
    locally_closed_gap term m (tvar (Fr x)) <-> True.
Proof.
  intros. unfold locally_closed, locally_closed_gap.
  setoid_rewrite term_ind1. intuition.
  now subst.
Qed.

Theorem term_lc_gap2 : forall (X : typ) (t : term LN) (m : nat),
    locally_closed_gap term m (lam X t) <-> locally_closed_gap term (S m) t.
Proof.
  intros. unfold locally_closed, locally_closed_gap.
  setoid_rewrite term_ind2. split.
  - introv premise hypothesis. destruct l; [easy|].
    cbn. specialize (premise (S w) (Bd n)).
    cbn in premise.
    replace (w - 0) with w in premise by lia.
    assert (H : S w <> 0) by lia.
    specialize (premise (conj hypothesis H)).
    unfold_lia.
  - introv premise [hypothesis neq0].
    destruct l; [easy|].
    specialize(premise (w - 1) (Bd n) hypothesis).
    cbn in *. unfold_lia.
Qed.

Theorem term_lc_gap3 : forall (t1 t2 : term LN) (m : nat),
    locally_closed_gap term m ([t1]@[t2]) <-> locally_closed_gap term m t1 /\ locally_closed_gap term m t2.
Proof.
  intros. unfold locally_closed, locally_closed_gap.
  setoid_rewrite term_ind3. intuition.
Qed.

Theorem term_lc11 : forall (n : nat),
    locally_closed term (tvar (Bd n)) <-> False.
Proof.
  intros. unfold locally_closed. now (rewrite term_lc_gap11).
Qed.

Theorem term_lc12 : forall (x : atom),
    locally_closed term (tvar (Fr x)) <-> True.
Proof.
  intros. unfold locally_closed. now (rewrite term_lc_gap12).
Qed.

Theorem term_lc2 : forall (X : typ) (t : term LN),
    locally_closed term (lam X t) <-> locally_closed_gap term 1 t.
Proof.
  intros. unfold locally_closed. now (rewrite term_lc_gap2).
Qed.

Theorem term_lc3 : forall (t1 t2 : term LN),
    locally_closed term ([t1]@[t2]) <-> locally_closed term t1 /\ locally_closed term t2.
Proof.
  intros. unfold locally_closed.
  now setoid_rewrite term_lc_gap3.
Qed.
