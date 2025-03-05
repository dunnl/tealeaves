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
  Backends.LN.

Export LN.Simplification.
Export LN.Notations.
Export DecoratedTraversableMonad.UsefulInstances.

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

Inductive Lam (V : Type) :=
| tvar : V -> Lam V
| lam  : typ -> Lam V -> Lam V
| app  : Lam V -> Lam V -> Lam V.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

Module TermNotations.
  Notation "'term'" := (Lam LN).
  Notation "'λ'" := (lam) (at level 45).
  Notation "⟨ t ⟩ ( u )" := (app t u) (at level 80, t at level 40, u at level 40).
  Notation "A ⟹ B" := (arr A B) (at level 40).
End TermNotations.

Import TermNotations.

Definition lnvar := @tvar LN.
Definition bvar := @tvar LN ○ Bd.
Definition fvar := @tvar LN ○ Fr.
Coercion lnvar: LN >-> Lam.
Coercion bvar: nat >-> Lam.
Coercion fvar: atom >-> Lam.
Coercion Bd: nat >-> LN.
Coercion Fr: atom >-> LN.

(* Help the simplification tactics unfold coercions to expose a
   <<tvar>> constructor, which is needed to find a match for
   <<bindd f (ret x)>> *)
#[global] Hint Unfold fvar bvar: tea_ret_coercions.

Section test_notations.

  Context
    (β : Type)
    (x y z : atom)
    (b : β) (τ : typ).

  Check 1.
  Check (1: LN).
  Check (1: Lam LN).
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
Fixpoint binddt_Lam (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f : nat * v1 -> G (Lam v2)) (t : Lam v1) : G (Lam v2) :=
  match t with
  | tvar v => f (0, v)
  | lam τ body => pure (lam τ) <⋆> binddt_Lam (f ⦿ 1) body
  | app t1 t2 => pure (@app v2) <⋆> binddt_Lam f t1 <⋆> binddt_Lam f t2
  end.

#[export] Instance Return_STLC: Return Lam := tvar.
#[export] Instance Binddt_STLC: Binddt nat Lam Lam := @binddt_Lam.
#[export] Instance DTM_STLC: DecoratedTraversableMonad nat Lam.
Proof.
  (* We duplicate the goal just for the purpose of debugging the tactics *)
  dup. {
    constructor.
    typeclasses eauto.
    - derive_dtm1.
    - constructor.
      + derive_dtm2.
      + derive_dtm3.
      + derive_dtm4. }
  derive_dtm.
Qed.

(*|
========================================
Instantiation of derived functions
========================================
|*)
#[export] Instance Map_STLC: Map Lam
  := DerivedOperations.Map_Binddt nat Lam Lam.
#[export] Instance Mapd_STLC: Mapd nat Lam
  := DerivedOperations.Mapd_Binddt nat Lam Lam.
#[export] Instance Traverse_STLC: Traverse Lam
  := DerivedOperations.Traverse_Binddt nat Lam Lam.
#[export] Instance Mapdt_STLC: Mapdt nat Lam
  := DerivedOperations.Mapdt_Binddt nat Lam Lam.
#[export] Instance Bind_STLC: Bind Lam Lam
  := DerivedOperations.Bind_Binddt nat Lam Lam.
#[export] Instance Bindd_STLC: Bindd nat Lam Lam
  := DerivedOperations.Bindd_Binddt nat Lam Lam.
#[export] Instance Bindt_STLC: Bindt Lam Lam
  := DerivedOperations.Bindt_Binddt nat Lam Lam.
#[export] Instance ToSubset_STLC: ToSubset Lam
  := ToSubset_Traverse.
#[export] Instance ToBatch_STLC: ToBatch Lam
  := DerivedOperations.ToBatch_Traverse.

Module LNNotations.
  Notation "t '{ x ~> u }" :=
    (subst x (u: Lam LN) (t: Lam LN)) (at level 35).
  Notation "t ' ( u )" :=
    (open (u: Lam LN) (t : Lam LN)) (at level 35, format "t  ' ( u )" ).
  Notation "' [ x ] t" :=
    (close x (t: Lam LN)) (at level 35, format "' [ x ]  t" ).
End LNNotations.

Export LNNotations.

Section test_operations.

  Context
    (β : Type)
      (b : β) (τ : typ).

  Definition x: atom := 0.
  Definition y: atom := 1.
  Definition z: atom := 2.

  Compute (λ τ (tvar (Bd 0))) '(Bd 0: Lam LN).
  Compute (λ τ (tvar (Bd 0))) '(Bd 1).
  Compute (λ τ (tvar (Bd 1))) '(0).
  Compute (λ τ (Bd 1)) '(0).
  Compute (λ τ 1) '(0).
  Compute (λ τ 1) '(0).
  Compute (λ τ x) '{x ~> y}.
  Compute (λ τ y) '{x ~> y}.
  Compute (λ τ x) '{x ~> 0}.
  Compute (λ τ 0) '{x ~> y}.

  (* test something *)
  Eval cbn in LC (λ τ 0).
  Context (body: Lam LN).
  Eval cbn in FV (λ τ body).
  Eval cbn in LCn 3 (λ τ body).
  Goal LC (λ τ body).
    simplify.
  Abort.
  Goal FV (λ τ body) = FV (λ τ body).
    simplify.
  Abort.
  Goal  (λ τ body) '{x ~> y} = (λ τ body).
    cbn.
  Abort.
  Goal (λ τ (body '{x ~> y}) = λ τ body).
    simplify.
  Abort.

  Check (1: LN).
  Check (1: Lam LN).
  Compute (λ τ (tvar (Bd 0))) '(x: Lam LN).

  Compute (λ τ (tvar (Bd 0))) '(x: LN).
  Compute (λ τ (tvar (Bd 1))) '(tvar (Fr x)).
  Compute (λ τ (tvar (Bd 0))) '(Bd 0: Lam LN).
  Compute (λ τ (tvar (Bd 0))) '(Bd 1: Lam LN).
  Compute (λ τ (tvar (Bd 1))) '(Bd 0: Lam LN).
  Compute (λ τ (tvar (Bd 1))) '(Bd 1: Lam LN).
  Compute (λ τ x) '{x ~> (y: Lam LN)}.
  Compute (λ τ y) '{x ~> (y: Lam LN)}.

End test_operations.

Definition ctx := list (atom * typ).

Reserved Notation "Γ ⊢ t : τ" (at level 90, t at level 99).

Implicit Types (t: term) (Γ: ctx) (x: atom) (τ: typ)
  (L: AtomSet.t).

Inductive Judgment: ctx -> term -> typ -> Prop :=
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
    forall Γ (t1 t2: Lam LN) (τ1 τ2: typ),
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
