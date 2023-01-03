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
  Classes.Kleisli.DT.Monad
  Data.Natural
  Theory.Kleisli.Decorated.Prepromote
  Functors.List.

Import Product.Notations.
Import Applicative.Notations.
Export List.ListNotations.
Open Scope list_scope.
Export DT.Monad.Notations.
Open Scope tealeaves_scope.

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
| tvar : v -> term β v
| lam : β -> typ -> term β v -> term β v
| app : term β v -> term β v -> term β v.

(** ** Notations and automation *)
(******************************************************************************)
Module Notations.
  Notation "'λ' ( X ::: t ) body" := (lam X t body) (at level 45).
  Notation "[ t1 ] [ t2 ]" := (app t1 t2) (at level 40).
  Notation "A ⟹ B" := (arr A B) (at level 40).
End Notations.

Import Notations.

#[export] Instance: forall β, Return (term β) := tvar.

(*|
========================================
Definition of binddt
========================================
|*)
Fixpoint binddt_term (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f : nat * v1 -> G (term unit v2)) (t : term unit v1) : G (term unit v2) :=
  match t with
  | tvar _ v => f (0, v)
  | lam b τ e => pure G (lam b τ) <⋆> (binddt_term (prepromote 1 f) e)
  | app t1 t2 => pure G (@app unit v2) <⋆> binddt_term f t1 <⋆> binddt_term f t2
  end.

#[export] Instance: Binddt nat (term unit) (term unit) := @binddt_term.

(*
Fixpoint binddt_term {β} (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f : list β * v1 -> G (term β v2)) (t : term β v1) : G (term β v2) :=
  match t with
  | tvar _ v => f (nil, v)
  | lam b τ e => pure G (lam b τ) <⋆> (binddt_term (prepromote [b] f) e)
  | app t1 t2 => pure G (@app β v2) <⋆> binddt_term f t1 <⋆> binddt_term f t2
  end.

#[export] Instance: forall β, Binddt (list β) (term β) (term β) := @binddt_term.
*)

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
  
(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Composition with unit (left unit law)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

  Check kdtm_binddt0 (list β) (term β) :
     forall (A B : Type) (G : Type -> Type) (H1 : Fmap G) (H2 : Pure G) (H3 : Mult G), Applicative G ->
       forall f : list β * A -> G (term β B),
         binddt (term β) G f ∘ ret (term β) = f ∘ ret (prod (list β)).

(*|
The "composition with unit" law (or left unit law) establishes that
the atomic expression `ret (term β) v`

1. consists just of variable `v`
2. inside an empty binding context

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

  Check kdtm_binddt1 (list β) (term β) :
    forall A : Type, binddt (term β) (fun A0 : Type => A0) (ret (term β) ∘ extract (prod (list β))) = @id (term β A).

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
  Check kdtm_binddt2 (list β) (term β) :
     forall (A B C : Type) (G1 : Type -> Type) (H1 : Fmap G1) (H2 : Pure G1) (H3 : Mult G1),
       Applicative G1 ->
       forall (G2 : Type -> Type) (H5 : Fmap G2) (H6 : Pure G2) (H7 : Mult G2),
       Applicative G2 ->
       forall (g : list β * B -> G2 (term β C)) (f : list β * A -> G1 (term β B)),
       fmap G1 (binddt (term β) G2 g) ∘ binddt (term β) G1 f = binddt (term β) (G1 ∘ G2) (g ⋆dtm f).

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

  Check kdtm_morph (list β) (term β) :
    forall (G1 G2 : Type -> Type) (H1 : Fmap G1) (H2 : Pure G1) (H3 : Mult G1) (H4 : Fmap G2) (H5 : Pure G2) (H6 : Mult G2)
         (ϕ : forall A : Type, G1 A -> G2 A),
       ApplicativeMorphism G1 G2 ϕ ->
       forall (A B : Type) (f : list β * A -> G1 (term β B)),
         ϕ (term β B) ∘ binddt (term β) G1 f = binddt (term β) G2 (ϕ (term β B) ∘ f).

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

  Theorem dtm1_stlc:
    forall (A B : Type) (G : Type -> Type) (H1 : Fmap G) (H2 : Pure G) (H3 : Mult G), Applicative G ->
       forall f : list β * A -> G (term β B),
         binddt (term β) G f ∘ ret (term β) = f ∘ ret (prod (list β)).
  Proof.
    reflexivity.
  Qed.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~
Identity law for STLC
~~~~~~~~~~~~~~~~~~~~~~~~

.. coq::
   :name: dtm2
|*)

  Theorem dtm2_stlc : forall A : Type, binddt (term β) (fun A0 : Type => A0) (ret (term β) ∘ extract (prod (list β))) = @id (term β A).
  Proof.
    intros. ext t.
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
        rewrite extract_incr
    end.
  
  Ltac merge_incr :=
    try unfold prepromote;
    change (?f ∘ incr ?w0 ∘ incr ?w1) with (f ∘ (incr w0 ∘ incr w1));
    repeat rewrite incr_incr.

  Ltac rewrite_with_bind_hyp :=
    match goal with
    | H : context[binddt] |- _ =>
        rewrite H
    end.

  Ltac induction_on_term :=
    match goal with
    | t : term ?β ?v |- _ =>
        induction t
    end.

  Ltac solve_dtm2 :=
    intros; ext t; induction_on_term;
    cbn; unfold prepromote;
    repeat absorb_incr;
    repeat rewrite_with_bind_hyp;
    easy.

  Goal forall A : Type, binddt (term β) (fun A0 : Type => A0) (ret (term β) ∘ extract (prod (list β))) = @id (term β A).
    solve_dtm2.
  Qed.

  (*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Composition law for STLC
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. coq::
   :name: dtm3
|*)

  Notation "'P'" := pure.
  Notation "'F'" := fmap.
  Notation "'BD'" := binddt.
  
Section ap_compose.

  Theorem ap_compose1new `{Applicative G1}
    `{Applicative G2} {A B} : forall (f : G2 (G1 (A -> B))),
      ap (G2 ∘ G1) f =
        ap G2 (fmap G2 (ap G1) f).
  Proof.
    intros. ext a.
    rewrite (ap_compose1 G1 G2).
    now rewrite fmap_to_ap.
  Qed.

  Theorem ap_compose2new `{Applicative G1}
    `{Applicative G2} {A B} :
      ap (G2 ∘ G1) (A := A) (B := B) =
        ap G2 ∘ fmap G2 (ap G1).
  Proof.
    intros. ext f.
    now rewrite (ap_compose1new).
  Qed.
  
  Theorem ap6_new : forall {G : Type -> Type} {H : Fmap G} {H0 : Pure G} {H1 : Mult G},
      Applicative G -> forall (A B C : Type) (f : B -> C), compose (F G f) ∘ ap G (A := A) = ap G ∘ F G (compose f).
  Proof.
    intros. ext x. ext y. unfold compose.
    rewrite ap6.
    reflexivity.
  Qed.

  Theorem commute_hom_action1 :
    forall (A B C D : Type) (f1 : A -> B) (f2 : B -> C) (f3 : C -> D),
      compose f3 (precompose f1 f2) = precompose f1 (compose f3 f2).
  Proof.
    reflexivity.
  Qed.
  
  Theorem commute_hom_action2 :
    forall (A B C D : Type) (f1 : A -> B) (f3 : C -> D),
      compose f3 ∘ precompose f1 = precompose f1 ∘ compose f3.
  Proof.
    reflexivity.
  Qed.

End ap_compose.

  Theorem dtm3_stlc :
    forall (A B C : Type) (G1 : Type -> Type) (H1 : Fmap G1) (H2 : Pure G1) (H3 : Mult G1),
      Applicative G1 ->
       forall (G2 : Type -> Type) (H5 : Fmap G2) (H6 : Pure G2) (H7 : Mult G2),
       Applicative G2 ->
       forall (g : list β * B -> G2 (term β C)) (f : list β * A -> G1 (term β B)),
       fmap G1 (binddt (term β) G2 g) ∘ binddt (term β) G1 f = binddt (term β) (G1 ∘ G2) (g ⋆dtm f).
  Proof.
    intros. ext t.
    generalize dependent g.
    generalize dependent f.
    induction t; intros f g. (* .unfold *)
    - change_right ((binddt _ (G1 ∘ G2) (g ⋆dtm f) ∘ ret (term β)) v).
      change_left (((fmap G1 (BD (term β) G2 g) ∘ BD (term β) G1 f) ∘ ret (term β)) v).
      reassociate -> on left.
      rewrite (dtm1_stlc); [| typeclasses eauto].
      rewrite (dtm1_stlc); [| typeclasses eauto].
      unfold kcompose_dtm; cbn.
      now rewrite prepromote_zero.
    - change_left (fmap G1 (BD (term β) G2 g) (P G1 (lam β0 t) <⋆> BD (term β) G1 (prepromote [β0] f) t0)).
      change_right (P (G1 ∘ G2) (lam β0 t) <⋆> BD (term β) (G1 ∘ G2) (prepromote [β0] (g ⋆dtm f)) t0).
      rewrite ap6. rewrite (app_pure_natural G1).
      rewrite binddt_lam.
      change ((precompose ?pre ∘ ?post) ?arg) with (post arg ∘ pre).
      

      rewrite (ap_compose1 G2 G1).
      rewrite <- (kcompose_dtm_prepromote _ (term β)).
      rewrite <- IHt.

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
      admit.
    - unfold compose; cbn.
      rewrite ap6.
      rewrite ap6.
      rewrite (app_pure_natural G1).
      rewrite binddt_app.
      admit.
  Admitted.
  
(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Homomorphism law for STLC
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. coq::
   :name: dtm4
|*)
  
  Theorem dtm4_stlc :
    forall (G1 G2 : Type -> Type) (H1 : Fmap G1) (H2 : Pure G1) (H3 : Mult G1) (H4 : Fmap G2) (H5 : Pure G2) (H6 : Mult G2)
      (ϕ : forall A : Type, G1 A -> G2 A), ApplicativeMorphism G1 G2 ϕ ->
      forall (A B : Type) (f : list β * A -> G1 (term β B)),
        ϕ (term β B) ∘ binddt (term β) G1 f = binddt (term β) G2 (ϕ (term β B) ∘ f).
  Proof.
    intros. ext t.
    inversion H.
    generalize dependent f.
    induction t; intro f. (* .unfold *)
    - reflexivity.
    - unfold compose at 1.
      change (ϕ (term β B) (BD (term β) G1 f ((lam β0 t) t0)))
        with (ϕ (term β B) (ap G1 (P G1 (lam β0 t)) (BD (term β) G1 (prepromote [β0] f) t0))).
      rewrite ap_morphism_1.
      compose near t0 on left.
      rewrite IHt.
      rewrite appmor_pure.
      reflexivity.
    - change ((ϕ (term β B) ∘ BD (term β) G1 f) ([t1][t2]))
        with (ϕ (term β B) (pure G1 (app (v:=B)) <⋆> BD (term β) G1 f t1 <⋆> (BD (term β) G1 f t2))).
      rewrite ap_morphism_1.
      rewrite ap_morphism_1.
      rewrite appmor_pure.
      compose near t1.
      rewrite IHt1.
      compose near t2.
      rewrite IHt2.
      reflexivity.
  Qed.

End laws.

From Tealeaves Require Export
  LN.Leaf LN.Atom LN.AtomSet LN.AssocList LN.Operations LN.Theory.

Export LN.AtomSet.Notations.
Open Scope set_scope.
Export LN.AssocList.Notations.

Arguments tvar [β]%type_scope [v]%type_scope _.

Section test_notations.

  Context
    (β : Type)
    (x y z : atom)
    (b : β) (τ : typ).

  Check 1.
  Check (λ (b ::: τ) (tvar (Bd 1))).
  Check (λ (b ::: τ) (tvar (Fr x))).
  Check [λ (b ::: τ) (tvar (Bd 1))][tvar (Fr x)].
  Check [λ (b ::: τ) (tvar (Fr x))][tvar (Bd 0)].
  Check λ (b ::: τ) [(tvar (Bd 1))][tvar (Fr x)].
  Check λ (b ::: τ) [(tvar (Fr x))][tvar (Bd 0)].

End test_notations.

Definition ctx := list (atom * typ).

Import Tealeaves.Classes.Algebraic.Setlike.Functor.Notations.

Import LN.Operations.Notations.

Reserved Notation "Γ ⊢ t : S" (at level 90, t at level 99).

Inductive Judgment : ctx -> term unit leaf -> typ -> Prop :=
| j_var :
    forall Γ (x : atom) (A : typ),
      uniq Γ ->
      (x, A) ∈ Γ ->
      Γ ⊢ tvar (Fr x) : A
| j_abs :
    forall (L : AtomSet.t) Γ (u : unit) (τ1 τ2 : typ) (t : term unit leaf),
      (forall x : atom, ~ AtomSet.In x L -> Γ ++ x ~ τ1 ⊢ t '(tvar (Fr x)) : τ2) ->
      Γ ⊢ λ (tt ::: τ1) t : τ1 ⟹ τ2
| j_app :
    forall Γ (t1 t2 : term unit leaf) (A B : typ),
      Γ ⊢ t1 : A ⟹ B ->
      Γ ⊢ t2 : A ->
      Γ ⊢ [t1][t2] : B
where "Γ ⊢ t : A" := (Judgment Γ t A).
