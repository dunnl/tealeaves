(*|
############################################################
Formalizing STLC with Tealeaves
############################################################
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Algebraic presentation
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This file gives a tutorial on proving the decorated traversable monad
laws the for the syntax of the simply-typed lambda calculus (STLC).

.. contents:: Table of Contents
   :depth: 2

============================
Imports and setup
============================

Since we are using the algebraic typeclass hierarchy, we import modules under
the namespaces ``Classes.Algebraic`` and ``Theory.Algebraic.``
|*)

From Tealeaves Require Export
  Classes.DT.Monad
  Classes.Monoid
  Classes.Listable.Functor
  Data.Natural.

Import Traversable.Functor.Notations.
Import List.ListNotations.
Import Strength.Notations.
Import Monoid.Notations.

#[local] Generalizable All Variables.
#[local] Set Implicit Arguments.

(*|
=====================
Language Definition
=====================

The first step with Tealeaves is to define the syntax of the
language. We take a type ``base_typ`` of types we consider primitive
(a/k/a atomic). The set of simple types is built up by forming arrows
between types, starting with base types. The syntax of STLC is defined
with three constructors as usual.
|*)

Parameter base_typ : Type.

Inductive typ :=
| base : base_typ -> typ
| arr : typ -> typ -> typ.

Coercion base : base_typ >-> typ.

(* we give more informative names to [Lam]'s arguments
 than Coq would infer otherwise *)
Inductive term (A : Type) :=
| Var : A -> term A
| Lam : forall (X : typ) (t : term A), term A
| Ap : term A -> term A -> term A.

Module Notations.
  Notation "'λ' X ⋅ body" :=
    (Lam X body) (at level 45) : tealeaves_scope.
  Notation "[ t1 ] [ t2 ]" :=
    (Ap t1 t2) (at level 40) : tealeaves_scope.
  Notation "A ⟹ B" :=
    (arr A B) (at level 40) : tealeaves_scope.
End Notations.

Import Notations.

(*|
For convenience, we define an extremely rudimentary Ltac tactic that
will solve the most trivial inductive steps automatically. Namely,
they will attempt to solve a goal in one step by rewriting with the
hypotheses in context (up to two times), then calling ``reflexivity``.
|*)

Ltac basic t :=
  induction t;
  [ reflexivity |
    simpl; match goal with H : _ |- _ => rewrite H end; reflexivity |
    simpl; do 2 match goal with H : _ |- _ => rewrite H end; reflexivity ].

(*|
=====================
Functor instances
=====================

Plain Functor instance
========================

Note that our datatype ``term`` is parameterized by a single type
variable. The first thing we must show is that ``term`` is actually
*functor* in this type argument.
|*)

Fixpoint fmap_term {A B : Type} (f : A -> B) (t : term A) : term B :=
  match t with
  | Var a => Var (f a)
  | Lam X t => Lam X (fmap_term f t)
  | Ap t1 t2 => Ap (fmap_term f t1) (fmap_term f t2)
  end.

#[export] Instance Fmap_term : Fmap term := @fmap_term.

Theorem fmap_id : forall A, fmap term id = @id (term A).
Proof.
  intros. ext t. unfold transparent tcs. basic t.
Qed.

Theorem fmap_fmap : forall A B C (f : A -> B) (g : B -> C),
    fmap term g ∘ fmap term f = fmap term (g ∘ f).
Proof.
  intros. ext t. unfold transparent tcs.
  unfold compose. basic t.
Qed.

#[export] Instance Functor_term : Functor term :=
  {| fun_fmap_id := @fmap_id;
     fun_fmap_fmap := @fmap_fmap;
  |}.

(*|
Rewriting rules for ``fmap``
-----------------------------
|*)

Section fmap_term_rewrite.

  Context
    `{f : A -> B}.

  Lemma fmap_term_ap : forall (t1 t2 : term A),
      fmap term f (@Ap A t1 t2) = @Ap B (fmap term f t1) (fmap term f t2).
  Proof.
    reflexivity.
  Qed.

End fmap_term_rewrite.

(*|
Decorated Functor instance
===========================
|*)

Fixpoint dec_term {A} (t : term A) : term (nat * A) :=
  match t with
  | Var a => Var (Ƶ, a)
  | Lam τ t => Lam τ (shift term (1, dec_term t))
  | Ap t1 t2 => Ap (dec_term t1) (dec_term t2)
  end.

#[export] Instance Decorate_term : Decorate nat term := @dec_term.

Theorem dec_natural : forall A B (f : A -> B),
    fmap term (fmap (prod nat) f) ∘ dec term = dec term ∘ fmap term f.
Proof.
  intros. unfold compose. ext t. induction t.
  - now cbn.
  - cbn -[shift]. fequal. now rewrite dec_helper_1.
  - cbn. now fequal.
Qed.

#[export] Instance: Natural (@dec nat term _).
Proof.
  constructor.
  - typeclasses eauto.
  - apply Functor_compose.
  - apply dec_natural.
Qed.

Theorem dec_extract : forall A,
    fmap term (extract (prod nat)) ∘ dec term = @id (term A).
Proof.
  intros. unfold compose. ext t. induction t.
  - reflexivity.
  - cbn -[shift]. now rewrite dec_helper_2.
  - unfold id. cbn. now fequal.
Qed.

Theorem dec_dec : forall A,
    dec term ∘ dec term = fmap term (cojoin (prod nat)) ∘ dec term (A := A).
Proof.
  intros. unfold compose. ext t. induction t.
  - reflexivity.
  - cbn -[shift]. fequal. now rewrite dec_helper_3.
  - cbn. fequal; auto.
Qed.

#[export] Instance DecoratedFunctor_term : DecoratedFunctor nat term.
Proof.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - apply dec_dec.
  - apply dec_extract.
Qed.

(*|
Rewriting rules for ``dec``
-----------------------------
|*)

Section dec_term_rewrite.

  Context
    `{f : A -> B}.

  Lemma dec_term1 : forall (x : A),
      dec term (Var x) = Var (0, x).
  Proof.
    reflexivity.
  Qed.

  Lemma dec_term21 : forall (X : typ) (t : term A),
      dec term (Lam X t) = shift term (1, Lam X (dec term t)).
  Proof.
    reflexivity.
  Qed.

  Lemma dec_term22 : forall (X : typ) (t : term A),
      dec term (Lam X t) = Lam X (shift term (1, dec term t)).
  Proof.
    reflexivity.
  Qed.

  Lemma dec_term3 : forall (t1 t2 : term A),
      dec term (Ap t1 t2) = Ap (dec term t1) (dec term t2).
  Proof.
    reflexivity.
  Qed.

End dec_term_rewrite.

(*|
Traversable Functor instance
==============================
|*)

Import Applicative.Notations.

Fixpoint dist_term `{Fmap F} `{Pure F} `{Mult F} {A : Type}
         (t : term (F A)) : F (term A) :=
  match t with
  | Var a => fmap F (@Var A) a
  | Lam X t => fmap F (Lam X) (dist_term t)
  | Ap t1 t2 => (pure F (@Ap A))
                 <⋆> dist_term t1
                 <⋆> dist_term t2
  end.

#[export] Instance: Dist term := @dist_term.

(*|
Rewriting rules for ``dist``
-----------------------------
|*)

Section term_dist_rewrite.

  Context
    `{Applicative G}.

  Variable (A : Type).

  Lemma dist_term_var_1 : forall (x : G A),
    dist term G (@Var (G A) x) = pure G (@Var A) <⋆> x.
  Proof.
    intros. cbn. now rewrite fmap_to_ap.
  Qed.

  Lemma dist_term_var_2 : forall (x : G A),
    dist term G (@Var (G A) x) = fmap G (@Var A) x.
  Proof.
    reflexivity.
  Qed.

  Lemma dist_term_lam_1 : forall (X : typ) (t : term (G A)),
      dist term G (Lam X t) = pure G (Lam X) <⋆> (dist term G t).
  Proof.
    intros. cbn. now rewrite fmap_to_ap.
  Qed.

  Lemma dist_term_lam_2 : forall (X : typ) (t : term (G A)),
      dist term G (Lam X t) = fmap G (Lam X) (dist term G t).
  Proof.
    reflexivity.
  Qed.

  Lemma dist_term_ap_1 : forall (t1 t2 : term (G A)),
      dist term G (Ap t1 t2) =
      (pure G (@Ap A))
        <⋆> dist term G t1
        <⋆> dist term G t2.
  Proof.
    reflexivity.
  Qed.

  Lemma dist_term_ap_2 : forall (t1 t2 : term (G A)),
      dist term G (Ap t1 t2) =
      (fmap G (@Ap A) (dist term G t1)
            <⋆> dist term G t2).
  Proof.
    intros. rewrite dist_term_ap_1.
    now rewrite fmap_to_ap.
  Qed.

End term_dist_rewrite.

Section dist_term_properties.

  Context
    `{Applicative G}.

(*|
Naturality of ``dist``
-----------------------------
|*)

  Lemma dist_natural_term : forall `(f : A -> B),
      fmap (G ∘ term) f ∘ dist term G =
      dist term G ∘ fmap (term ∘ G) f.
  Proof.
    intros; cbn. ext t.
    unfold_ops @Fmap_compose. unfold compose. induction t.
    + cbn. compose near a. now rewrite 2(fun_fmap_fmap G).
    + cbn. rewrite <- IHt.
      compose near (dist term G t).
      now rewrite 2(fun_fmap_fmap G).
    + rewrite (dist_term_ap_2).
      rewrite (fmap_term_ap).
      rewrite (dist_term_ap_2).
      rewrite <- IHt1, <- IHt2.
      rewrite <- ap_fmap.
      rewrite fmap_ap. fequal.
      compose near (dist term G t1).
      rewrite (fun_fmap_fmap G).
      rewrite (fun_fmap_fmap G).
      compose near (dist term G t1) on right.
      rewrite (fun_fmap_fmap G).
      reflexivity.
  Qed.

  #[export] Instance dist_Natural_term :
      Natural (@dist term _ _ _ _ _).
  Proof.
    intros. constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. apply dist_natural_term.
  Qed.

(*|
Traversal laws
-----------------------------
|*)

  Lemma dist_unit_term : forall (A : Type),
      dist term (fun A => A) = @id (term A).
  Proof.
    intros. ext t. induction t.
    - reflexivity.
    - cbn. rewrite IHt. reflexivity.
    - cbn. rewrite IHt1, IHt2.
      reflexivity.
  Qed.

  #[local] Set Keyed Unification.
  Lemma dist_linear_term : forall `{Applicative G1} `{Applicative G2} (A : Type),
      dist term (G1 ∘ G2) =
      fmap G1 (dist term G2) ∘ dist term G1 (A := G2 A).
  Proof.
    intros. unfold compose. ext t. induction t.
    - cbn. compose near a on right. now rewrite (fun_fmap_fmap G1).
    - cbn. rewrite IHt. compose near (dist term G1 t).
      change (fmap (G1 ○ G2) (Lam X)) with (fmap G1 (fmap G2 (@Lam A X))).
      rewrite (fun_fmap_fmap G1).
      now rewrite (fun_fmap_fmap G1).
    - rewrite dist_term_ap_2.
      rewrite (dist_term_ap_2 (G := G1 ○ G2)).
      rewrite fmap_ap.
      compose near ((dist term G1 t1)).
      rewrite (fun_fmap_fmap G1).
      rewrite (ap_compose2 G2 G1).
      rewrite IHt1, IHt2.
      rewrite <- ap_fmap. fequal.
      repeat (compose near (dist term G1 t1) on left;
              rewrite (fun_fmap_fmap G1)).
      fequal. ext s1 s2. unfold compose; cbn.
      unfold precompose. now rewrite (fmap_to_ap).
  Qed.
  #[local] Unset Keyed Unification.

  Lemma dist_morph_term : forall `{ApplicativeMorphism G1 G2 ϕ} A,
      dist term G2 ∘ fmap term (ϕ A) = ϕ (term A) ∘ dist term G1.
  Proof.
    intros. ext t. unfold compose. induction t.
    - cbn. now rewrite <- (appmor_natural G1 G2).
    - cbn. rewrite IHt.
      now rewrite (appmor_natural G1 G2).
    - rewrite fmap_term_ap. inversion H9.
      rewrite dist_term_ap_2.
      rewrite IHt1. rewrite IHt2.
      rewrite dist_term_ap_2. rewrite (ap_morphism_1).
      fequal. now rewrite <- (appmor_natural).
  Qed.

End dist_term_properties.

#[export] Instance TraversableFunctor_term : TraversableFunctor term :=
  {| dist_natural := @dist_Natural_term;
     dist_morph := @dist_morph_term;
     dist_linear := @dist_linear_term;
     dist_unit := @dist_unit_term;
  |}.

(*|
Decorated-Traversable Functor instance
=======================================
|*)

Lemma dtfun_compat_term1 : forall `{Applicative G} (X : typ) {A},
    fmap G (dec term ∘ Lam X) ∘ δ term G (A := A) =
    fmap G (curry (shift term) 1 ∘ Lam X) ∘ fmap G (dec term) ∘ δ term G.
Proof.
  intros. rewrite (fun_fmap_fmap G). reflexivity.
Qed.

Theorem dtfun_compat_term :
        `(forall `{Applicative G} {A : Type},
             dist term G ∘ fmap term (strength G) ∘ dec term (A := G A) =
             fmap G (dec term) ∘ dist term G).
Proof.
  intros. ext t. unfold compose. induction t.
  - cbn. compose near a. now rewrite 2(fun_fmap_fmap G).
  - cbn. do 2 (compose near (dec term t) on left;
               rewrite (fun_fmap_fmap term)).
    reassociate <-. rewrite (strength_shift1 nat G).
    rewrite <- (fun_fmap_fmap term); unfold compose.
    change (fmap term (fmap G ?f)) with (fmap (term ∘ G) f).
    compose near ((fmap term (σ G) (dec term t))).
    unfold_compose_in_compose.
    rewrite <- (natural (ϕ := @dist term _ G _ _ _)).
    unfold compose.
    rewrite IHt. compose near (δ term G t).
    rewrite (fun_fmap_fmap G).
    compose near (δ term G t) on left.
    unfold_ops @Fmap_compose; rewrite 2(fun_fmap_fmap G).
    fequal. ext t'; unfold compose; cbn.
    compose near (dec term t') on right; now rewrite (fun_fmap_fmap term).
  - cbn. rewrite IHt1, IHt2. rewrite fmap_ap. rewrite fmap_ap.
    rewrite pure_ap_fmap. rewrite <- ap_fmap.
    rewrite (app_pure_natural G). rewrite <- (fmap_to_ap).
    compose near (δ term G t1) on left. rewrite (fun_fmap_fmap G).
    reflexivity.
Qed.

#[export] Instance : DecoratedTraversableFunctor nat term :=
  {| dtfun_compat := @dtfun_compat_term |}.


(*|
=====================
Monad instances
=====================

Plain Monad instance
=====================
|*)

Fixpoint join_term {A : Type} (t : term (term A)) : term A :=
  match t with
  | Var t' => t'
  | Lam X t => Lam X (join_term t)
  | Ap t1 t2 => Ap (join_term t1) (join_term t2)
  end.

#[export] Instance Ret_term : Return term := @Var.

#[export] Instance Join_term : Join term := @join_term.

Theorem ret_natural : forall A B (f : A -> B),
    fmap term f ∘ ret term = ret term ∘ f.
Proof.
  reflexivity.
Qed.

Theorem join_natural : forall A B (f : A -> B),
    fmap term f ∘ join term = join term ∘ fmap term (fmap term f).
Proof.
  intros. ext t. unfold transparent tcs.
  unfold compose. basic t.
Qed.

#[export] Instance: Natural (@ret term _).
Proof.
  constructor; try typeclasses eauto.
  apply ret_natural.
Qed.

#[export] Instance: Natural (@join term _).
Proof.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - apply join_natural.
Qed.

Theorem join_ret : forall A,
    join term ∘ ret term = @id (term A).
Proof.
  reflexivity.
Qed.

Theorem join_fmap_ret : forall A,
    join term ∘ fmap term (ret term) = @id (term A).
Proof.
  intros. unfold compose. unfold transparent tcs.
  ext t. basic t.
Qed.

Theorem join_join : forall A,
    join term ∘ join term = join term (A := A) ∘ fmap term (join term).
Proof.
  intros. unfold compose. unfold transparent tcs.
  ext t. basic t.
Qed.

#[export] Instance Monad_term : Monad term :=
  {| mon_join_ret := join_ret;
     mon_join_fmap_ret := join_fmap_ret;
     mon_join_join := join_join |}.

(*|
Decorated Monad instance
===========================
|*)

Theorem dec_ret : forall A,
    dec term ∘ ret term (A := A) = ret term ∘ pair Ƶ.
Proof.
  reflexivity.
Qed.

Theorem dec_join : forall A,
    dec term ∘ join term (A := A) =
    join term ∘ fmap term (shift term) ∘ dec term ∘ fmap term (dec term).
Proof.
  intros. unfold compose. ext t. induction t.
  - cbn -[shift]. now rewrite (shift_zero term).
  - cbn -[shift]. fequal. now rewrite (dec_helper_4).
  - cbn. fequal; auto.
Qed.

#[export] Instance DecoratedMonad_term : DecoratedMonad nat term.
Proof.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - typeclasses eauto.
  - apply dec_ret.
  - apply dec_join.
Qed.

(*|
Traversable Monad instance
==============================
|*)

Theorem trvmon_ret_term `{Applicative G} :
  `(dist term G ∘ ret term (A := G A) = fmap G (ret term)).
Proof.
  intros. ext x. reflexivity.
Qed.

#[local] Set Keyed Unification.
Theorem trvmon_join_term `{Applicative G} :
  `(dist term G ∘ join term = fmap G (join term) ∘ dist (term ∘ term) G (A := A)).
Proof.
  intros. ext t. unfold compose. induction t.
  - cbn. compose near (dist term G a).
    rewrite (fun_fmap_fmap G).
    replace (join term ∘ Var (A := term A)) with (@id (term A)).
    now rewrite (fun_fmap_id G).
    apply (join_ret).
  - cbn. rewrite IHt.
    unfold_ops @Dist_compose. unfold compose.
    compose near (dist term G (fmap term (dist term G) t)).
    rewrite (fun_fmap_fmap G).
    rewrite (fun_fmap_fmap G).
    reflexivity.
  - cbn. rewrite IHt1, IHt2.
    unfold_ops @Dist_compose. unfold compose.
    rewrite <- fmap_to_ap.
    rewrite <- fmap_to_ap.
    rewrite <- ap_fmap. rewrite fmap_ap.
    fequal. compose near ((dist term G (fmap term (dist term G) t1))).
    repeat rewrite (fun_fmap_fmap G).
    compose near ((dist term G (fmap term (dist term G) t1))) on left.
    rewrite (fun_fmap_fmap G).
    fequal.
Qed.
#[local] Set Keyed Unification.

#[export] Instance TraversableMonad_term : TraversableMonad term :=
  {| trvmon_ret := @trvmon_ret_term;
     trvmon_join := @trvmon_join_term;
  |}.

(*|
Decorated-Traversable Monad instance
=======================================

Our hard work has paid off---a DTM is defined as the combination of the typeclass instances we have
given so far, so we can let Coq infer the DTM instance for us.
|*)

#[export] Instance : DecoratedTraversableMonad nat term := {}.
