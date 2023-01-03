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
  (* LN.Leaf LN.Atom LN.AtomSet LN.AssocList LN.Operations LN.Theory *)
  Classes.Kleisli.DT.Monad
  Functors.List.

Import Product.Notations.
Import Applicative.Notations.
Export List.ListNotations.
Open Scope list_scope.
Export DT.Monad.Notations.
Open Scope tealeaves_scope.
(*
Export LN.AtomSet.Notations.
Open Scope set_scope.
Export LN.AssocList.Notations.
 *)

#[local] Generalizable Variables G.
Set Implicit Arguments.

(** * Language definition *)
(******************************************************************************)
Parameter base_typ : Type.

Inductive typ :=
| base : base_typ -> typ
| arr : typ -> typ -> typ.

Coercion base : base_typ >-> typ.

Inductive term (β : Type) (v : Type) :=
| var : v -> term β v
| lam : β -> typ -> term β v -> term β v
| app : term β v -> term β v -> term β v.

(** ** Notations and automation *)
(******************************************************************************)
Module Notations.
  Notation "'λ' X ⋅ body" := (lam X body) (at level 45).
  Notation "[ t1 ] [ t2 ]" := (app t1 t2) (at level 40).
  Notation "A ⟹ B" := (arr A B) (at level 40).
End Notations.

Import Notations.

#[export] Instance: forall β, Return (term β) := var.

(*|
========================================
Definition of binddt
========================================
|*)

Fixpoint binddt_term {β} (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f : list β * v1 -> G (term β v2)) (t : term β v1) : G (term β v2) :=
  match t with
  | var _ v => f (nil, v)
  | lam b τ e => pure G (lam b τ) <⋆> (binddt_term (prepromote [b] f) e)
  | app t1 t2 => pure G (@app β v2) <⋆> binddt_term f t1 <⋆> binddt_term f t2
  end.

#[export] Instance: forall β, Binddt (list β) (term β) (term β) := @binddt_term.


(*|
========================================
Some rewriting principles for binddt
========================================
|*)

Section binddt_helpers.

  Context {β : Type}.

  (* Generalize over (Coq) variables used for object-level variables
   and symbols for applicative homomorphisms. *)
  Generalizable Variables v ϕ.

  Context {v1 v2 : Type}.
  
  Notation "'P'" := pure.
  Notation "'F'" := fmap.
  Notation "'B'" := binddt.
  
  Lemma binddt_lam :
    forall `{Applicative G2}
      `(g : list β * v2 -> G2 (term β v3))
      β0 τ,
      compose (B (term β) G2 g) (lam β0 τ) = (precompose (B (term β) G2 (prepromote [β0] g)) ∘ ap G2) (P G2 (lam β0 τ)).
  Proof.
    reflexivity.
  Qed.

  Lemma binddt_app :
    forall `{Applicative G2}
      `(g : list β * v2 -> G2 (term β v3)),
      compose (compose (B (term β) G2 g)) (app (v:=v2))
      = ((compose (precompose (B (term β) G2 g) ∘ ap G2)) ∘ precompose (B (term β) G2 g) ∘ ap G2) (P G2 (app (v:=v3))).
  Proof.
    reflexivity.
  Qed.

    (*
    change (compose (B (term β) G2 g) ∘ app (v:=v2))
      with (fun t1 t2 => ap G2 ((ap G2 (P G2 (app (v:=v3)))) (B (term β) G2 g t1)) (B (term β) G2 g t2)).
    Undo.
    change (compose (B (term β) G2 g) ∘ app (v:=v2))
      with (fun t1 => precompose (B (term β) G2 g) (ap G2 ((ap G2 (P G2 (app (v:=v3)))) (B (term β) G2 g t1)))).
    Undo.
    Check (compose (precompose (B (term β) G2 g)) (ap G2)).
     *)
  
End binddt_helpers.
    
(*|
========================================
An overview of the DTM axioms
========================================
|*)

Section laws.

  Context {β : Type}.

  (* Generalize over (Coq) variables used for object-level variables
   and symbols for applicative homomorphisms. *)
  Generalizable Variables v ϕ.

  Context {v1 v2 : Type}.
  
  Notation "'P'" := pure.
  Notation "'F'" := fmap.
  Notation "'B'" := binddt.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Composition with unit (left unit law)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

  Definition dtm1 `{Applicative G1} :=
    forall  (f : list β * v1 -> G1 (term β v2)),
      binddt (term β) G1 f ∘ ret (term β) = f ∘ ret (list β ×).

(*|
The "composition with unit" law (or left unit law) establishes that
the atomic expression `ret (term β) v`

1. consists just of variable `v` and
2. has an empty binding context

In this law, `ret (list β ×)` is the operation which lifts any `v`
into an empty binding context to get `([], v)`. A simpler way of
writing the left unit law is then

`binddt f (ret (term β) v) = f ([], v)`

The proof of this rule ought to follow merely from the definitions of
`binddt` and `ret`.  In the course of proofs about `binddt f t` by
induction of the syntax of expression `t`, the left unit law acts as
a base case.

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Identity law (right unit law)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

  Definition dtm2 `{Applicative G1} := forall (t : term β v1),
    binddt (term β) G1 (pure G1 ∘ ret (term β) ∘ extract ((list β) ×)) t = pure G1 t.

(*|
The identity law (or right unit law) establishes that applying the
substitution rule

`pure F ∘ ret (term β) ∘ extract ((list β) ×)`

to each of the variables in expression `t` acts as the pure effect on
`t`. The substitution rule is the one which at each variable

1. throws away the binding context: `list β * v -> v`
2. coerces the variable into an atomic expression: `v -> term β v`
3. and lifts the result into `F` with the `pure` effect: `term β v -> F (term β v)`

~~~~~~~~~~~~~~~~~~~~~~~~
Composition law
~~~~~~~~~~~~~~~~~~~~~~~~
|*)
  Definition dtm3 `{Applicative G1} `{Applicative G2} :=
    forall 
      `(g : list β * v2 -> G2 (term β v3))
      `(f : list β * v1 -> G1 (term β v2)),
      fmap G1 (binddt (term β) G2 g) ∘ binddt (term β) G1 f =
        binddt (term β) (G1 ∘ G2) (g ⋆dtm f).

(*|
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

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Applicative homomorphism law
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

  Definition dtm4 `{Applicative G1} `{Applicative G2}
    `{! ApplicativeMorphism G1 G2 ϕ} :=
  forall (f : list β * v1 -> G1 (term β v2)),
    binddt (term β) G2 (ϕ _ ∘ f) = ϕ _ ∘ binddt (term β) G1 f.

(*|
This law states that `binddt` is parametric with respect to
applicative functors in the sense that it commutes with their
homomorphisms. It is (probably?) a free theorem, so it is not actually
a restriction on implementations of `binddt` (cite Gibbons).

================================
Proving the DTM axioms for STLC
================================

We prove the laws for STLC.

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Left unit law for STLC
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. coq::
   :name: dtm1
|*)

  Ltac solve_dtm1 :=
    intros; now try ext var.

  Theorem dtm1_stlc : forall (v1 v2 : Type) `{Applicative G} (f : list β * v1 -> G (term β v2)),
        @binddt (list β) (term β) (term β) _ G _ _ _ v1 v2 f ∘ ret (term β) = f ∘ ret (list β ×).
  Proof.
    unfold dtm1. solve_dtm1.
  Qed.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~
Identity law for STLC
~~~~~~~~~~~~~~~~~~~~~~~~

.. coq::
   :name: dtm2
|*)

  Theorem dtm2_stlc : dtm2.
  Proof.
    unfold dtm2.
    intros.
    induction t. (* .unfold *)
    - cbn. (* var case *) (* .unfold *)
      reflexivity.
    - cbn. (* lam case *) (* .unfold *)
      unfold prepromote.
      reassociate -> near (incr [β0]).
      rewrite extract_incr. (* .unfold *)
      rewrite IHt.
      reflexivity.
    - cbn. (* app case *) (* . unfold *)
      rewrite IHt1.
      rewrite IHt2.
      reflexivity.
  Qed.

  Ltac absorb_incr :=
    match goal with
    | |- context[(?f ∘ extract ?W) ∘ incr ?w] =>
        reassociate -> near (incr w);
        rewrite extract_incr;
        idtac "aborb_incr"
    end.

  Ltac rewrite_with_bind_hyp :=
    match goal with
    | H : context[binddt] |- _ =>
        rewrite H
    end.

  Ltac find_induction :=
    match goal with
    | t : term ?β ?v |- _ =>
        induction t
    end.

  Ltac solve_dtm2 :=
    intros; find_induction;
    cbn; unfold prepromote;
    repeat absorb_incr;
    repeat rewrite_with_bind_hyp;
    easy.

  Goal dtm2.
    unfold dtm2. solve_dtm2.
  Qed.

  (*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Composition law for STLC
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. coq::
   :name: dtm3
|*)

  Theorem dtm3_stlc :
    forall `{Applicative G1} `{Applicative G2}
      `(g : list β * v2 -> G2 (term β v3))
      `(f : list β * v1 -> G1 (term β v2)),
      fmap G1 (binddt (term β) G2 g) ∘ binddt (term β) G1 f = binddt (term β) (G1 ∘ G2) (g ⋆dtm f).
  Proof.
    intros. ext t.
    generalize dependent g.
    generalize dependent f.
    induction t; intros f g. (* .unfold *)
    - change_right ((binddt _ (G1 ∘ G2) (g ⋆dtm f) ∘ ret (term β)) v).
      change_left (((fmap G1 (B (term β) G2 g) ∘ B (term β) G1 f) ∘ ret (term β)) v).
      reassociate -> on left.
      rewrite (dtm1_stlc); [| typeclasses eauto].
      rewrite (dtm1_stlc); [| typeclasses eauto].
      unfold kcompose_dtm; cbn.
      now rewrite Prepromote.prepromote_zero.
    - change_left ((F G1 (B (term β) G2 g) ∘ (B (term β) G1 f ∘ (λ β0 ⋅ t))) t0).
      change_right ((B (term β) (G1 ∘ G2) (g ⋆dtm f) ∘ (λ β0 ⋅ t)) t0).
      rewrite binddt_lam.
      rewrite binddt_lam.
      admit.







      (* Working proof:
      change_left (fmap G1 (B (term β) G2 g) (P G1 (λ β0 ⋅ t) <⋆> B (term β) G1 (prepromote [β0] f) t0)).
      change_right (P (G1 ∘ G2) (λ β0 ⋅ t) <⋆> B (term β) (G1 ∘ G2) (prepromote [β0] (g ⋆dtm f)) t0).
      rewrite ap6; rewrite (app_pure_natural G1).
      rewrite scoot1'.


      
      unfold compose.
      change (precompose ?g ?f) with (compose f g).
      rewrite <- (ap2 (G := G1)).
      rewrite <- (ap2 (G := G1)).
      rewrite ap4.



      
      rewrite <- (fmap_to_ap ((B (term β) G2 (prepromote [β0] g)))).
      compose near t0 on left.
      rewrite IHt.
      unfold_ops @Pure_compose.
      rewrite (ap_compose1 G2 G1).
      rewrite (ap2 (G := G1)).
      rewrite <- (kcompose_dtm_prepromote _ (term β)).
      reflexivity.
      *)
    - unfold compose; cbn.
      rewrite ap6.
      rewrite ap6.
      rewrite (app_pure_natural G1).
      rewrite binddt_app.
      admit.
  Abort.

  Ltac merge_incr :=
    try unfold prepromote;
    change (?f ∘ incr ?w0 ∘ incr ?w1) with (f ∘ (incr w0 ∘ incr w1));
    repeat rewrite incr_incr.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Homomorphism law for STLC
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. coq::
   :name: dtm4
|*)
    
  Theorem dtm4_stlc : dtm4.
  Proof.
    unfold dtm4.
    
    
    intros. ext t.
    generalize dependent f.
    induction t; intro f. (* .unfold *)
    - reflexivity.
    - cbn. unfold prepromote.
      reassociate -> near (incr [β0]).
      rewrite IHt.
      (*
      rewrite <- (appmor_pure G1 G2).
      unfold compose.
      rewrite <- ap_morphism_1.
      reflexivity.
    - cbn.
      repeat rewrite_with_bind_hyp.
      rewrite <- (appmor_pure G1 G2).
      unfold compose.
      do 2 rewrite <- ap_morphism_1.
      reflexivity.
  Qed.
       *)
  Admitted.
  
End laws.
