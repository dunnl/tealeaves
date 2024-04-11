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
  Misc.NaturalNumbers
  Functors.List
  Theory.DecoratedTraversableMonad
  Tactics.Debug
  Examples.Simplification_Support.

Export Monoid.Notations. (* Ƶ and ● *)
Export Kleisli.DecoratedTraversableMonad.Notations. (* ∈d *)
Export Misc.Subset.Notations. (* ∪ *)
Export Applicative.Notations. (* <⋆> *)
Export List.ListNotations. (* [] :: *)
Export LN.Notations. (* operations *)
Export LN.AtomSet.Notations.
Export LN.AssocList.Notations. (* one, ~ *)
Export Product.Notations. (* × *)
Export ContainerFunctor.Notations. (* ∈ *)
Export DecoratedContainerFunctor.Notations. (* ∈d *)

#[local] Generalizable Variables G A B C.
#[local] Set Implicit Arguments.

Open Scope set_scope.

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
  Notation "[ t1 ]@[ t2 ]" := (app t1 t2) (at level 80).
  Notation "A ⟹ B" := (arr A B) (at level 40).
End Notations.

Import Notations.

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

(*|
========================================
Simplification automation
========================================
|*)

#[local] Notation "'P'" := pure.
#[local] Notation "'BD'" := binddt.

(*|
========================================
Simplification support
========================================
|*)


(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Helper lemmas for proving the DTM laws
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

These definitional equalities help prove the composition law later.
|*)

Section rw.

  Context
    {G : Type -> Type} `{Map G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f: nat * v1 -> G (term v2)).

  Definition binddt_term_rw1: forall x,
      BD f (tvar x) = f (0, x) := ltac:(reflexivity).

  Definition binddt_term_rw2: forall τ body,
      binddt f (@lam _ τ body) =
        (P (λ τ) <⋆> BD (f ⦿ 1) body)
    := ltac:(reflexivity).

  Definition binddt_term_rw3: forall t1 t2,
      binddt f (@app _ t1 t2) =
        (P (@app v2) <⋆> BD f t1 <⋆> BD f t2)
    := ltac:(reflexivity).

  Lemma binddt_pointfree_lam: forall τ,
    BD f ∘ (@lam v1 τ) =
      (precompose (BD (f ⦿ 1)) ∘ ap G ∘ P) (@lam v2 τ).
  Proof.
    reflexivity.
  Qed.

  Lemma binddt_pointfree_app :
    compose (BD f) ∘ @app v1 =
      (compose (precompose (BD f) ∘ ap G) ∘ precompose (BD f) ∘ ap G ∘ P) (@app v2).
  Proof.
    reflexivity.
  Qed.

End rw.

(*
change does not work as well as rewrite because it the right-hand side
seems to do its own typeclass resolution rather than taking the information from the match (which seems not completely unreasonable in general *)
(*
Ltac binddt_term_1 :=
  change ((BD ?f) (tvar ?x)) with (f (0, x)).

Ltac binddt_term_2 :=
  change ((BD ?f) ((λ) ?τ ?body)) with
    (P ((λ) τ) <⋆> BD (f ⦿ 1) body).

Ltac binddt_term_3 :=
  change ((BD ?f) (app ?t1 ?t2)) with
    (P (@app _) <⋆> BD f t1 <⋆> BD f t2).
 *)

Ltac simplify_binddt_term :=
  match goal with
  | |- context[BD ?f (tvar ?y)] =>
      debug "step_BD_tvar";
      rewrite binddt_term_rw1
  | |- context[((BD ?f) ((λ) ?τ ?body))] =>
      debug "step_BD_lam";
      rewrite binddt_term_rw2
  | |- context[((BD ?f) (app ?t1 ?t2))] =>
      debug "step_BD_app";
      rewrite binddt_term_rw3
  end.

Ltac simplify_binddt_term_lazy unit :=
  simplify_binddt_term.

Ltac derive_dtm_law :=
  derive_dtm_law_with_simplify_binddt simplify_binddt_term_lazy.

(*|
========================================
An overview of the DTM axioms
========================================
|*)

Section laws.

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
    forall `{Applicative G} (A B : Type),
       forall f : nat * A -> G (term B),
         binddt f ∘ ret  = f ∘ ret (T := (nat ×)).
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

  Theorem dtm2_stlc: forall A: Type,
      binddt (T := term) (U := term)
        (G := fun A => A) (ret (T := term) ∘ extract (W := (nat ×))) = @id (term A).
  Proof.
    derive_dtm_law.
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


  Ltac dtm3_lhs_step :=
  repeat rewrite map_ap;
  (* Distribute outer <<map>> into the constructor *)
  rewrite app_pure_natural.
  (* Fuse <<map f>> and the <<pure C>> into <<pure (f ∘ C)>> *)

  Ltac dtm3_rhs_kc7_preincr :=
    try match goal with
    | |- context[@preincr _ _ _ ((?G1 ∘ ?G2) ?x)] =>
        (* this step deals with composition blocking
           rewrite kc7_preincr *)
        change ((G1 ∘ G2) x) with (G1 (G2 x))
        end;
    repeat rewrite <- kc7_preincr.

  Ltac dtm3_rhs_invoke_IH :=
    repeat match goal with
      | IH: context[BD (_ ⋆7 _) ?t] |- _ =>
          dtm3_rhs_kc7_preincr;
          rewrite <- IH
      end.

  Ltac dtm3_rhs_applicative_compose :=
      match goal with
      | |- context[ap (?G1 ∘ ?G2)] =>
          (rewrite_strat innermost
             (terms (ap_compose2 G2 G1)));
          (repeat rewrite map_ap);
          (repeat rewrite app_pure_natural)
      end.

  Ltac dtm3_rhs_applicative_map :=
      rewrite <- ap_map;
      repeat rewrite map_ap;
      repeat rewrite app_pure_natural.

  Ltac dtm3_rhs_step :=
      dtm3_rhs_invoke_IH;
      unfold_ops @Pure_compose;
      repeat (dtm3_rhs_applicative_compose;
              dtm3_rhs_applicative_map).

  Theorem dtm3_stlc :
    forall `{Applicative G1} `{Applicative G2},
        forall `(g : nat * B -> G2 (term C)) `(f : nat * A -> G1 (term B)),
          map (binddt g) ∘ binddt f = binddt (G := G1 ∘ G2) (g ⋆7 f).
  Proof.
    intros. ext t.
    unfold compose at 1.
    generalize dependent g.
    generalize dependent f.
    induction t; intros f g.
    - repeat simplify_binddt_term.
      dtm_law_pass.
      simplify_pass2.
      reflexivity.
    - repeat simplify_binddt_term.
      dtm3_lhs_step.
      dtm3_rhs_step.
      reflexivity.
    - repeat simplify_binddt_term.
      dtm3_lhs_step.
      dtm3_rhs_step.
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
    forall (G1 G2 : Type -> Type) (H1 : Map G1) (H2 : Mult G1) (H3 : Pure G1) (H4 : Map G2) (H5 : Mult G2) (H6 : Pure G2)
      (ϕ : forall A : Type, G1 A -> G2 A), ApplicativeMorphism G1 G2 ϕ ->
      forall (A B : Type) (f : nat * A -> G1 (term B)),
        ϕ (term B) ∘ binddt f = binddt (ϕ (term B) ∘ f).
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

  #[export] Instance DTMPre_STLC:
    DecoratedTraversableRightPreModule nat term term :=
    {| kdtm_binddt1 := dtm2_stlc;
      kdtm_binddt2 := @dtm3_stlc;
      kdtm_morph := @dtm4_stlc;
    |}.

  #[export] Instance DTM_STLC:
    DecoratedTraversableMonad nat term :=
    {| kdtm_binddt0 := @dtm1_stlc;
    |}.

  #[export] Instance DTMFull_STLC:
    DecoratedTraversableMonadFull nat term
    := DecoratedTraversableMonadFull_DecoratedTraversableMonad nat term.

End laws.

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
