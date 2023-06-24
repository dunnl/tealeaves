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
  Tealeaves
  Backends.LN.

Export Tealeaves.Notations.
Export Tealeaves.Backends.LN.Notations.
Export Tealeaves.DerivedInstances.

#[local] Generalizable Variables G.
#[local] Set Implicit Arguments.

(* Halfway explicit *)
#[global] Arguments binddt {M}%type_scope T {U}%function_scope {Binddt}   G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[global] Arguments mapdt  {M}%type_scope (T)%function_scope   {Mapdt}    G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[global] Arguments bindd  {M}%type_scope T {U}%function_scope {Bindd}                               {A B}%type_scope _%function_scope _.
#[global] Arguments mapd   {M}%type_scope (T)%function_scope   {Mapd}                                {A B}%type_scope _%function_scope _.
#[global] Arguments bindt                 T {U}%function_scope {Bindt}    G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[global] Arguments traverse              (T)%function_scope   {Traverse} G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[global] Arguments bind                  (T) {U}%function_scope {Bind}                              {A B}%type_scope _%function_scope _.
#[global] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[global] Arguments ret T%function_scope {Return} A%type_scope _.
#[global] Arguments cobind W%function_scope {Cobind} {A B}%type_scope _%function_scope _.
#[global] Arguments tolist F%function_scope {Tolist} {A}%type_scope _.
#[global] Arguments foldMap T%function_scope {M}%type_scope {H H0 H1} {A}%type_scope f%function_scope _.
#[global] Arguments foldMapd {W}%type_scope T%function_scope {M}%type_scope {H H0 H1} {A}%type_scope _%function_scope _.

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
Fixpoint binddt_term (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f : nat * v1 -> G (term v2)) (t : term v1) : G (term v2) :=
  match t with
  | tvar v => f (0, v)
  | lam τ body => pure G (lam τ) <⋆> binddt_term (f ⦿ 1) body
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
  Notation "'BD' F" := (binddt (M := nat) term (U := term) F) (at level 10).

  Lemma binddt_lam :
    forall (τ : typ), BD F f ∘ (@lam v1 τ) = (precompose (BD F (f ⦿ 1)) ∘ ap F ∘ P F) (@lam v2 τ).
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

  Ltac rewrite_with_bind_hyp :=
    match goal with
    | H : context[binddt] |- _ => rewrite H
    end.

  Ltac induction_on_term :=
    match goal with
    | t : term ?v |- _ => induction t
    end.

  Ltac dtm_setup :=
    intros; ext t; unfold id; induction_on_term; cbn.

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
    forall  (G : Type -> Type) (H1 : Map G) (H2 : Pure G) (H3 : Mult G) `(! Applicative G) (A B : Type),
       forall f : nat * A -> G (term B),
         binddt term G f ∘ ret term A = f ∘ ret (prod nat) A.
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

  Theorem dtm2_stlc : forall A : Type, binddt term (fun A0 : Type => A0) (ret term A ∘ extract (prod nat) A) = @id (term A).
  Proof.
    intros. ext t. unfold id.
    induction t.
    - cbn. fequal.
    - cbn. fequal. rewrite extract_preincr2; auto.
    - cbn. fequal; auto.
  Qed.

  Ltac solve_dtm2_case :=
    fequal; repeat rewrite extract_preincr2; auto.

  Theorem dtm2_stlc_automated : forall A : Type, binddt term (fun A0 : Type => A0) (ret term _ ∘ extract (prod nat) _) = @id (term A).
    dtm_setup; solve_dtm2_case.
  Qed.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~
Composition law
~~~~~~~~~~~~~~~~~~~~~~~~

The composition law states the following:

`map F (binddt g) ∘ binddt f = binddt (g ⋆ f)`

The right-hand side may be written more explicitly as

`binddt (fun '(w, x) => map F (binddt (F := G) (g ∘ incr w)) (f (w, x))))`

This law is an analogue of the ordinary monad composition law

`bind g ∘ bind f = bind (bind g ∘ f)`.

Both are loosely of the form

`bind g ∘ bind f = bind (g ∗ f)`

A close comparison shows the rules differ in two respects:

1. The call to `g` in `bind g` is replaced with a call to `(g ∘ incr
   w)` where `w` is the context seen by the function `f`.
2. The call to `binddt (g ∘ incr w)` is wrapped in `map F`. This is
   required to map over the applicative effect of type `F` generated
   by the application of `f`.

.. coq::
   :name: dtm3
|*)

  Notation "'P'" := pure.
  Notation "'F'" := map.
  Notation "'BD'" := (binddt term).

  Ltac dtm3_lhs_step G1 :=
    repeat rewrite map_ap; (* Bring LHS <<map>> up to the constructor *)
    rewrite (app_pure_natural G1). (* Fuse <<map>> and the <<pure (constructor)>> *)

  Ltac dtm3_rhs_step G2 G1 :=
    (rewrite_strat innermost (terms (ap_compose2 G2 G1)));
    repeat rewrite map_ap;
    rewrite (app_pure_natural G1);
    rewrite <- ap_map;
    repeat rewrite map_ap;
    rewrite (app_pure_natural G1).

  Set Keyed Unification.

  Theorem dtm3_stlc :
    forall (G1 : Type -> Type) (G2 : Type -> Type) (H1 : Map G1) (H2 : Pure G1) (H3 : Mult G1),
      Applicative G1 ->
      forall (H5 : Map G2) (H6 : Pure G2) (H7 : Mult G2),
        Applicative G2 ->
        forall (A B C : Type) (g : nat * B -> G2 (term C)) (f : nat * A -> G1 (term B)),
          map G1 (binddt term G2 g) ∘ binddt term G1 f = binddt term (G1 ∘ G2) (g ⋆7 f).
  Proof.
    intros. ext t.
    generalize dependent g.
    generalize dependent f.
    unfold compose at 1.
    induction t; intros f g.
    - cbn. change (g ⦿ 0) with (preincr g Ƶ).
      now rewrite (preincr_zero nat).
    - cbn.
      rewrite <- (kc7_preincr nat term).
      rewrite <- IHt.
      (* left side *)
      repeat rewrite map_ap. (* Bring LHS <<map>> up to the constructor *)
      rewrite (app_pure_natural G1). (* Fuse <<map>> and the <<pure (constructor)>> *)
      (* right side, constructor *)
      unfold_ops @Pure_compose.
      (* right side, first argument *)
      rewrite_strat innermost (terms (ap_compose2 G2 G1)).
      rewrite (app_pure_natural G1).
      rewrite <- ap_map.
      rewrite (app_pure_natural G1).
      reflexivity.
    - cbn.
      rewrite <- IHt1.
      rewrite <- IHt2.
      (* left side *)
      do 2 rewrite map_ap.
      rewrite (app_pure_natural G1).
      (* right side *)
      (* right side, constructor *)
      unfold_ops @Pure_compose.
      (* right side, first argument *)
      rewrite_strat innermost (terms (ap_compose2 G2 G1)).
      repeat rewrite map_ap.
      rewrite (app_pure_natural G1).
      rewrite <- ap_map.
      repeat rewrite map_ap.
      rewrite (app_pure_natural G1).
      (* right side, second argument *)
      rewrite_strat innermost (terms (ap_compose2 G2 G1)).
      repeat rewrite map_ap.
      rewrite (app_pure_natural G1).
      rewrite <- ap_map.
      repeat rewrite map_ap.
      rewrite (app_pure_natural G1).
      reflexivity.
  Qed.

  Theorem dtm3_stlc_automated :
    forall (A B C : Type) (G1 : Type -> Type) (H1 : Map G1) (H2 : Pure G1) (H3 : Mult G1),
      Applicative G1 ->
      forall (G2 : Type -> Type) (H5 : Map G2) (H6 : Pure G2) (H7 : Mult G2),
        Applicative G2 ->
        forall (g : nat * B -> G2 (term C)) (f : nat * A -> G1 (term B)),
          map G1 (binddt term G2 g) ∘ binddt term G1 f = binddt term (G1 ∘ G2) (g ⋆7 f).
  Proof.
    intros. ext t.
    unfold compose at 1.
    generalize dependent g.
    generalize dependent f.
    induction_on_term; intros f g.
    - cbn. change (preincr g 0) with (preincr g Ƶ).
      now rewrite (preincr_zero nat).
    - cbn.
      rewrite <- (kc7_preincr nat term).
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
    forall (G1 G2 : Type -> Type) (H1 : Map G1) (H2 : Pure G1) (H3 : Mult G1) (H4 : Map G2) (H5 : Pure G2) (H6 : Mult G2)
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
    forall (G1 G2 : Type -> Type) (H1 : Map G1) (H2 : Pure G1) (H3 : Mult G1) (H4 : Map G2) (H5 : Pure G2) (H6 : Mult G2)
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

  #[export] Instance: DTM nat term :=
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

Import AtomSet.Notations.
Import Sets.ElNotations.

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

Ltac unfold_const :=
  unfold_ops @Pure_const;
  unfold_ops @Mult_const;
  unfold_ops @Map_const;
  repeat change ((fun t => t) ∘ ?f) with f.

Ltac unfold_toset :=
  unfold_ops @Toset_Traverse.

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
    intros.
    cbn.
    rewrite extract_preincr2.
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
    cbv.
    easy.
  Qed.

  Lemma in_term_2 : forall (y : A) (X : typ) (t : term A),
    y ∈ (lam X t) <-> y ∈ t.
  Proof.
    intros.
    cbn.
    unfold_const.
    simpl_monoid.
    repeat rewrite extract_preincr2.
    reflexivity.
  Qed.

  Lemma in_term_3 : forall (t1 t2 : term A) (y : A),
      y ∈ (app t1 t2) <-> y ∈ t1 \/ y ∈ t2.
  Proof.
    intros.
    cbn.
    unfold_const.
    simpl_monoid.
    change_left (evalAt y (el term A t1 ● el term A t2)).
    rewrite (monmor_op _).
    reflexivity.
  Qed.

End term_list_rewrite.

(** ** Rewriting lemmas for <<free>>, <<freeset>> *)
(******************************************************************************)
Section term_free_rewrite.

  Variable
    (A : Type).

  Lemma term_free11 : forall (b : nat),
      free term (tvar (Bd b)) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma term_free12 : forall (y : atom),
      free term (tvar (Fr y)) = [y].
  Proof.
    reflexivity.
  Qed.

  Lemma term_free2 : forall (t : term LN) (X : typ),
      free term (lam X t) = free term t.
  Proof.
    intros.
    cbn.
    reassociate ->.
    rewrite (extract_preincr2).
    reflexivity.
  Qed.

  Lemma term_free3 : forall (t1 t2 : term LN),
      free term (app t1 t2) = free term t1 ++ free term t2.
  Proof.
    reflexivity.
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
    intros.
    unfold freeset.
    rewrite term_free2.
    reflexivity.
  Qed.

  Lemma term_freeset3 : forall (t1 t2 : term LN),
      freeset term (app t1 t2) [=] freeset term t1 ∪ freeset term t2.
  Proof.
    intros.
    unfold freeset.
    rewrite term_free3.
    rewrite (atoms_app).
    reflexivity.
  Qed.

  Lemma in_term_free11 : forall (b : nat) (x : atom),
      x ∈ free term (tvar (Bd b)) <-> False.
  Proof.
    intros.
    rewrite term_free11.
    reflexivity.
  Qed.

  Lemma in_term_free12 : forall (y : atom) (x : atom),
      x ∈ free term (tvar (Fr y)) <-> x = y.
  Proof.
    intros.
    rewrite term_free12.
    autorewrite with tea_list.
    reflexivity.
  Qed.

  Lemma in_term_free2 : forall (x : atom) (t : term LN) (X : typ),
      x ∈ free term (lam X t) <-> x ∈ free term t.
  Proof.
    intros.
    rewrite term_free2.
    reflexivity.
  Qed.

  Lemma in_term_free3 : forall (x : atom) (t1 t2 : term LN),
      x ∈ free term (app t1 t2) <-> x ∈ free term t1 \/ x ∈ free term t2.
  Proof.
    intros.
    cbn.
    rewrite (monmor_op _).
    change (?f x) with (evalAt x f).
    rewrite (monmor_op _).
    reflexivity.
  Qed.

  Lemma in_term_freeset11 : forall (b : nat) (x : atom),
      AtomSet.In x (freeset term (tvar (Bd b))) <-> False.
  Proof.
    intros.
    rewrite <- free_iff_freeset.
    now rewrite in_term_free11.
  Qed.

  Lemma in_term_freeset12 : forall (y : atom) (x : atom),
      AtomSet.In x (freeset term (tvar (Fr y))) <-> x = y.
  Proof.
    intros.
    rewrite <- free_iff_freeset.
    now rewrite in_term_free12.
  Qed.

  Lemma in_term_freeset2 : forall (x : atom) (t : term LN) (X : typ),
      AtomSet.In x (freeset term (lam X t)) <-> AtomSet.In x (freeset term t).
  Proof.
    intros.
    rewrite <- 2(free_iff_freeset).
    now rewrite in_term_free2.
  Qed.

  Lemma in_term_freeset3 : forall (x : atom) (t1 t2 : term LN),
      AtomSet.In x (freeset term (app t1 t2)) <-> AtomSet.In x (freeset term t1) \/ AtomSet.In x (freeset term t2).
  Proof.
    intros.
    rewrite <- 3(free_iff_freeset).
    now rewrite in_term_free3.
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
      foldMapd term f (λ X t) = foldMapd term (f ⦿ 1) t.
  Proof.
    intros.
    cbn.
    unfold_const.
    simpl_monoid.
    reflexivity.
  Qed.

  Lemma term_foldMapd3 : forall (t1 t2 : term A),
      foldMapd term f ([t1]@[t2]) = foldMapd term f t1 ● foldMapd term f t2.
  Proof.
    intros.
    cbn.
    unfold_const.
    simpl_monoid.
    reflexivity.
  Qed.

End term_foldMapd_rewrite.

(** ** Rewriting lemmas for <<∈d>> *)
(******************************************************************************)
Section term_ind_rewrite.

  Lemma term_ind1 : forall (l1 l2 : LN) (n : nat),
      (n, l1) ∈d (tvar l2) <-> n = Ƶ /\ l1 = l2.
  Proof.
    intros. cbn.
    unfold_const. cbv. split.
    - now inversion 1.
    - inversion 1. now subst.
  Qed.

  Lemma term_ind2 : forall (t : term LN) (l : LN) (n : nat) (X : typ),
      (n, l) ∈d t <-> (S n, l) ∈d (λ X t).
  Proof.
    intros.
    enough (H : (n, l) ∈d t = (S n, l) ∈d (λ) X t) by (now rewrite H).
    cbn.
    unfold_const.
    simpl_monoid.
    unfold_ops @Tosetd_DTF.
    change_right (foldMapd term ((ret (fun A : Type => A -> Prop) (nat * LN)) ⦿ 1) t (S n, l)).
    change (foldMapd term ?f ?t ?a) with ((evalAt a ∘ foldMapd term f) t).
    rewrite (foldMapd_morphism _ term).
    rewrite (foldMapd_morphism _ term).
    fequal. ext [na la].
    cbv. propext; inversion 1; now subst.
  Qed.

  Lemma term_ind2' : forall (t : term LN) (l : LN) (n : nat) (X : typ),
      (n, l) ∈d (λ X t) = ((n -  1, l) ∈d t /\ n <> 0).
  Proof.
    intros.
    destruct n.
    - propext.
      + unfold_ops @Tosetd_DTF.
        change (?f ?t (0, l)) with ((evalAt (0, l) ∘ f) t).
        rewrite (foldMapd_morphism _ term).
        intros contra.
        exfalso.
        rewrite (term_foldMapd2 _) in contra.
  Admitted.

  Lemma term_ind3 : forall (t1 t2 : term LN) (n : nat) (l : LN),
      (n, l) ∈d ([t1]@[t2]) <-> (n, l) ∈d t1 \/ (n, l) ∈d t2.
  Proof.
    intros.
    cbn.
    unfold_const.
    simpl_monoid.
    change (?f (n, l)) with (evalAt (n, l) f).
    rewrite (monmor_op (evalAt (n, l))).
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
  intros.
  unfold locally_closed_gap.
  setoid_rewrite (term_ind1).
  unfold is_bound_or_free.
  split.
  - intros H. specialize (H 0 (Bd n) (ltac:(intuition))).
    simpl_monoid in *.
    assumption.
  - intros Hleq w l [H1 H2]. subst.
    simpl_monoid. assumption.
Qed.

Theorem term_lc_gap12 : forall (x : atom) (m : nat),
    locally_closed_gap term m (tvar (Fr x)) <-> True.
Proof.
  intros. unfold locally_closed, locally_closed_gap.
  setoid_rewrite term_ind1. intuition.
  now subst.
Qed.

Lemma is_bof_S : forall w m l,
    is_bound_or_free m (S w, l) <-> is_bound_or_free (S m) (w, l).
Proof.
  intros. unfold is_bound_or_free.
  unfold_ops @Monoid_op_plus.
  destruct l.
  - reflexivity.
  - lia.
Qed.

Theorem term_lc_gap2 : forall (X : typ) (t : term LN) (m : nat),
    locally_closed_gap term m (lam X t) <-> locally_closed_gap term (S m) t.
Proof.
  intros. unfold locally_closed_gap.
  setoid_rewrite term_ind2' with (X := X).
  split.
  - introv premise hypothesis.
    specialize (premise (S w) l).
    replace (S w - 1) with w in premise by lia.
    assert (neq : S w <> 0) by lia.
    specialize (premise (conj hypothesis neq)).
    rewrite (is_bof_S) in premise.
    assumption.
  - intros premise w l [hypothesis neq].
    unfold is_bound_or_free in *.
    destruct l; [easy|].
    specialize (premise (w - 1) (Bd n)).
    specialize (premise hypothesis).
    cbn in premise.
    unfold_monoid.
    lia.
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
