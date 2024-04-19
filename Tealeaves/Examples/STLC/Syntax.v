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
  Examples.Simplification.

Export LN.Notations.

#[local] Set Implicit Arguments.

(*|
========================================
Using Tealeaves with STLC
========================================
|*)
Parameter base_typ : Type.

Inductive typ :=
| base : base_typ -> typ
| arr : typ -> typ -> typ.

Coercion base : base_typ >-> typ.

Inductive term (v : Type) :=
| tvar : v -> term v
| lam : typ -> term v -> term v
| app : term v -> term v -> term v.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

Module Notations.
  Notation "'λ'" := (lam) (at level 45).
  Notation "⟨ t ⟩ ( u )" := (app t u) (at level 80, t at level 40, u at level 40).
  Notation "A ⟹ B" := (arr A B) (at level 40).
End Notations.

Export Notations.

Definition lnvar := @tvar LN.
Definition bvar := @tvar LN ○ Bd.
Definition fvar := @tvar LN ○ Fr.
Coercion lnvar: LN >-> term.
Coercion bvar: nat >-> term.
Coercion fvar: atom >-> term.
Coercion Bd: nat >-> LN.
Coercion Fr: atom >-> LN.

Section test_notations.

  Context
    (β : Type)
    (x y z : atom)
    (b : β) (τ : typ).

  Check 1.
  Check (1: LN).
  Check (1: term LN).
  Check λ τ (tvar (Bd 1)).
  Check λ τ (Bd 1).
  Check λ τ 1.
  Check λ τ (tvar (Fr x)).
  Check λ τ (Fr x).
  Check λ τ x.
  Check ⟨λ τ (tvar (Bd 1))⟩ (tvar (Fr x)).
  Check ⟨λ τ (Bd 1)⟩ (Fr x).
  Check ⟨λ τ (Bd 1)⟩ (x).
  Check ⟨λ τ (tvar (Fr x))⟩ (tvar (Bd 0)).
  Check ⟨λ τ (Fr x)⟩ (Bd 0).
  Check ⟨λ τ x⟩ (0).

End test_notations.

(*|
========================================
Definition of binddt
========================================
|*)
Fixpoint binddt_term (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f : nat * v1 -> G (term v2)) (t : term v1) : G (term v2) :=
  match t with
  | tvar v => f (0, v)
  | lam τ body => pure (lam τ) <⋆> binddt_term (f ⦿ 1) body
  | app t1 t2 => pure (@app v2) <⋆> binddt_term f t1 <⋆> binddt_term f t2
  end.

#[export] Instance Return_STLC: Return term := tvar.
#[export] Instance Binddt_STLC: Binddt nat term term := @binddt_term.
#[export] Instance DTM_STLC: DecoratedTraversableMonad nat term := ltac:(derive_dtm).

(*|
========================================
Instantiation of derived functions
========================================
|*)
#[export] Instance Map_STLC: Map term
  := Map_Binddt nat term term.
#[export] Instance Mapd_STLC: Mapd nat term
  := Mapd_Binddt nat term term.
#[export] Instance Traverse_STLC: Traverse term
  := Traverse_Binddt nat term term.
#[export] Instance Mapdt_STLC: Mapdt nat term
  := Mapdt_Binddt nat term term.
#[export] Instance Bind_STLC: Bind term term
  := Bind_Binddt nat term term.
#[export] Instance Bindd_STLC: Bindd nat term term
  := Bindd_Binddt nat term term.
#[export] Instance Bindt_STLC: Bindt term term
  := Bindt_Binddt nat term term.
#[export] Instance ToSubset_STLC: ToSubset term
  := ToSubset_Traverse.
#[export] Instance ToBatch_STLC: ToBatch term
  := ToBatch_Traverse.

#[export] Instance DTMFull_STLC:
  DecoratedTraversableMonadFull nat term
  := DecoratedTraversableMonadFull_DecoratedTraversableMonad nat term.


Module NotationsLN.
  Notation "t '{ x ~> u }" := (subst x (u: term LN) (t: term LN)) (at level 35).
  Notation "t ' ( u )" := (open (u: term LN) (t : term LN)) (at level 35, format "t  ' ( u )" ).
  Notation "' [ x ] t" := (close x (t: term LN)) (at level 35, format "' [ x ]  t" ).
End NotationsLN.

Export NotationsLN.

Section test_operations.

  Context
    (β : Type)
    (x y z : atom)
    (b : β) (τ : typ).


  Compute (λ τ (tvar (Bd 0))) '(Bd 0: term LN).
  Compute (λ τ (tvar (Bd 0))) '(Bd 1).
  Compute (λ τ (tvar (Bd 1))) '(0).
  Compute (λ τ (Bd 1)) '(0).
  Compute (λ τ 1) '(0).
  Compute (λ τ 1) '(0).
  Compute (λ τ x) '{x ~> y}.
  Compute (λ τ y) '{x ~> y}.
  Compute (λ τ x) '{x ~> 0}.
  Compute (λ τ 0) '{x ~> y}.

  Check 1.
  Check (1: LN).
  Check (1: term LN).
  Compute (λ τ (tvar (Bd 0))) '(x: term LN).
  (*
  Set Typeclasses Debug.
  Fail Timeout 1 Compute (λ τ (tvar (Bd 0))) '(x: LN).
  *)
  Compute (λ τ (tvar (Bd 1))) '(tvar (Fr x)).
  Compute (λ τ (tvar (Bd 0))) '(Bd 0: term LN).
  Compute (λ τ (tvar (Bd 0))) '(Bd 1: term LN).
  Compute (λ τ (tvar (Bd 1))) '(Bd 0: term LN).
  Compute (λ τ (tvar (Bd 1))) '(Bd 1: term LN).
  Compute (λ τ x) '{x ~> (y: term LN)}.
  Compute (λ τ y) '{x ~> (y: term LN)}.

End test_operations.

Definition ctx := list (atom * typ).

Reserved Notation "Γ ⊢ t : τ" (at level 90, t at level 99).

Implicit Types (t: term LN) (Γ: ctx) (x: atom) (τ: typ)
  (L: AtomSet.t).

Inductive Judgment: ctx -> term LN -> typ -> Prop :=
| j_var:
    forall Γ x τ
      (Huniq: uniq Γ)
      (Hin: (x, τ) ∈ Γ),
      Γ ⊢ x: τ
| j_abs:
    forall L Γ τ1 τ2 t,
      (forall x,
          x `notin` L ->
          Γ ++ x ~ τ1 ⊢ t '(x): τ2) ->
      Γ ⊢ λ τ1 t: τ1 ⟹ τ2
| j_app:
    forall Γ (t1 t2: term LN) (τ1 τ2: typ),
      Γ ⊢ t1: τ1 ⟹ τ2 ->
      Γ ⊢ t2: τ1 ->
      Γ ⊢ ⟨t1⟩ (t2): τ2
where "Γ ⊢ t : τ" := (Judgment Γ t τ).

Ltac typing_induction_on J :=
  let  x := fresh "x" in
  let τ := fresh "τ" in
  let τ1 := fresh "τ1" in
  let τ2 := fresh "τ2" in
  let body := fresh "body" in
  induction J as
    [ Γ x τ Huniq Hin
    | L Γ τ1 τ2 body Jbody IHbody
    | Γ t1 t2 τ1 τ2 J1 IHJ1 J2 IHJ2 ].

Ltac typing_induction :=
  match goal with
  | J: context[Judgment ?Γ ?t ?τ] |- _ =>
      typing_induction_on J
  end.
