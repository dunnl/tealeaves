From Tealeaves Require Import
  Adapters.CategoricalToKleisli.TraversableFunctor
  Adapters.CategoricalToKleisli.DecoratedFunctor
  Adapters.CategoricalToKleisli.DecoratedTraversableFunctor
  Adapters.KleisliToCoalgebraic.TraversableFunctor
  Adapters.KleisliToCoalgebraic.DecoratedTraversableFunctor
  Classes.Categorical.DecoratedFunctor
  Classes.Coalgebraic.TraversableFunctor
  Classes.Coalgebraic.DecoratedTraversableFunctor.

From Tealeaves Require Export
  Functors.Batch
  Functors.Environment
  Theory.TraversableFunctor
  Theory.DecoratedTraversableFunctor
  Theory.LiftRel.TraversableFunctor
  Kleisli.Theory.DecoratedTraversableFunctor.

Import Product.Notations.
Import Monoid.Notations.
Import Batch.Notations.
Import List.ListNotations.
Import Subset.Notations.
Import ContainerFunctor.Notations.
Import DecoratedContainerFunctor.Notations.
Import VectorRefinement.Notations.

#[local] Generalizable Variables F M E T G A B C ϕ.

(** * Lifting context-sensitive relations over Decorated-Traversable functors *)
(******************************************************************************)
Section lifting_relations.

  Context
    `{Categorical.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}.

  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.
  Import CategoricalToKleisli.DecoratedFunctor.DerivedOperations.
  Import CategoricalToKleisli.TraversableFunctor.DerivedOperations.

  Context `{ToSubset T} `{! Compat_Map_Traverse T}.

  (*
  Lemma shape_decorate1
    (A: Type) (t: T A):
    shape (F := T) (dec T t) = shape t.
  Proof.
    unfold dec.
    unfold_ops @Decorate_Mapdt.
    unfold shape.
    compose near t on left.
  Abort.

  Lemma Hshape_decorate
    (A B: Type) (t: T A) (u: T B)
    (Hshape: shape t = shape u):
    shape (dec T t) = shape (dec T u).
  Proof.
    unfold dec.
    unfold Decorate_Mapdt.
    unfold shape.
    compose near t.
    unfold_ops @Map_compose.
  Abort.

  Definition zip_decorate
    (A B: Type) (t: T A) (u: T B)
    (Hshape: shape t = shape u):
    False.
  Proof.
    (*
    Check map (cojoin (W := (E ×))) (dec T (same_shape_zip t u Hshape)).
    Check same_shape_zip (A := E * A) (B := E * B) (dec T t) (dec T u) _.
     *)
  Abort.
  *)

  Import Theory.TraversableFunctor.
  Print Instances ToSubset.

  Definition lift_relation_ctx {A B:Type}
    (R: E * A -> E * B -> Prop): T A -> T B -> Prop :=
    precompose (dec T) ∘ mapdt (T := T) (G := subset) R.

  Lemma lift_relation_ctx_rw
    {A B:Type}  {t1: T A} {t2: T B}
    (R: E * A -> E * B -> Prop):
    lift_relation_ctx R t1 t2 = (mapdt (T := T) (G := subset) R) t1 (dec T t2).
  Proof.
    reflexivity.
  Qed.

  Lemma lift_relation_ctx_spec {A B: Type}
    (R: E * A -> E * B -> Prop): forall t u,
      lift_relation_ctx R t u <-> lift_relation R (dec T t) (dec T u).
  Proof.
    reflexivity.
  Qed.

  Lemma lift_relation_ctx_diagonal:
    forall (A: Type) (R: E * A -> E * A -> Prop) (t: T A),
      lift_relation_ctx R t t <-> Forall_ctx (fun '(e, a) => R (e, a) (e, a)) t.
  Proof.
    intros.
    rewrite lift_relation_ctx_spec.
    rewrite relation_diagonal_iff.
    replace (fun a => R a a) with (fun '(e, a) => R (e, a) (e, a)).
    - reflexivity.
    - now ext [e a].
  Qed.

End lifting_relations.


