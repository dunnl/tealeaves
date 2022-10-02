From Tealeaves Require Import
  Classes.Kleisli.DT.Functor
  Classes.Monoid
  Functors.Constant
  Functors.Batch
  Theory.Kleisli.DT.Functor.DerivedInstances.

Import Batch.Notations.
Import Applicative.Notations.

#[local] Generalizable Variables M W G A B.

(** * Batch *)
(******************************************************************************)
Section with_functor.

  Context
    (T : Type -> Type)
    `{DT.Functor.DecoratedTraversableFunctor W T}.

  Definition batch {A : Type} (B : Type) : A -> @Batch A B B :=
    fun a => (Go (@id B)) ⧆ a.

  Definition iterate {A : Type} (B : Type) : T A -> @Batch (W * A) B (T B) :=
    fmapdt T (Batch (W * A) B) (batch B).

  Lemma runBatch_batch : forall  `{Applicative G} (A B : Type) (f : W * A -> G B),
      runBatch f ∘ batch B = f.
  Proof.
    intros. ext [w a]. cbn.
    now rewrite ap1.
  Qed.

  Theorem fmapdt_to_runBatch :
    forall `{Applicative G} (A B : Type) (f : W * A -> G B) (t : T A),
      fmapdt T G f t = runBatch f (iterate B t).
  Proof.
    intros. unfold iterate.
    compose near t on right. rewrite <- (kdtfun_morph W T).
    now rewrite runBatch_batch.
  Qed.

End with_functor.
