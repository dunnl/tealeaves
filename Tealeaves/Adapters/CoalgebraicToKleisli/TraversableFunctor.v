From Tealeaves Require Import
  Functors.Early.Batch
  Classes.Coalgebraic.TraversableFunctor
  Classes.Kleisli.TraversableFunctor.

Import Batch.Notations.
Import Applicative.Notations.
Import Kleisli.TraversableFunctor.Notations.

#[local] Generalizable Variables ϕ T G A B C.


(** * Categorical Traversable Monads from Kleisli Traversable Monads *)
(******************************************************************************)

(** ** Derived Operations *)
(******************************************************************************)
Module DerivedOperations.

  #[export] Instance Traverse_ToBatch
    (T : Type -> Type) `{ToBatch T} : Traverse T :=
  fun G _ _ _ A B f =>
    runBatch G f (T B) ∘ toBatch.

End DerivedOperations.

(** ** Derived Instances *)
(******************************************************************************)
Module DerivedInstances.

  Import DerivedOperations.

  Context
    `{Coalgebraic.TraversableFunctor.TraversableFunctor T}.

  Lemma kc2_spec :
    forall `{Applicative G1}
      `{Applicative G2}
      `(g : B -> G2 C) `(f : A -> G1 B),
      g ⋆2 f = runBatch G1 f (G2 C) ∘
                 map (F := Batch A B) (runBatch G2 g C) ∘
                 double_batch.
  Proof.
    intros.
    ext a.
    unfold compose.
    rewrite double_batch_rw.
    rewrite map_Batch_rw2.
    rewrite map_Batch_rw1.
    rewrite (runBatch_batch G2).
    rewrite runBatch_rw2.
    rewrite runBatch_rw1.
    rewrite <- map_to_ap.
    reflexivity.
  Qed.

  Lemma traverse_id : forall (A : Type),
      traverse (G := fun A => A) id = @id (T A).
  Proof.
    intros.
    unfold_ops @Traverse_ToBatch.
    rewrite <- extract_Batch_to_runBatch.
    rewrite trf_extract.
    reflexivity.
  Qed.

  Lemma traverse_traverse :
    forall `{Applicative G1} `{Applicative G2},
      forall (A B C : Type)
          (g : B -> G2 C) (f : A -> G1 B),
          map (F := G1) (traverse (T := T) (G := G2) g) ∘ traverse (G := G1) f =
            traverse (G := G1 ∘ G2) (kc2 (G1 := G1) (G2 := G2) g f).
  Proof.
    intros.
    unfold_ops @Traverse_ToBatch.
    rewrite <- (fun_map_map (F := G1)).
    reassociate -> on left.
    reassociate <- near (map (toBatch (A := B) (A' := C))).
    rewrite (natural (ϕ := runBatch G1 f)).
    reassociate -> on left.
    rewrite <- trf_duplicate.
    rewrite cojoin_Batch_to_runBatch.
    reassociate <- on left.
    reassociate <- on left.
    rewrite (natural (ϕ := runBatch G1 f)).
    rewrite (runBatch_morphism'
               (homomorphism := ApplicativeMorphism_parallel (Batch A B) (Batch B C) G1 G2)).
    rewrite kc2_spec.
    reflexivity.
  Qed.

  Lemma traverse_morphism :
    forall `{morphism : ApplicativeMorphism G1 G2 ϕ} (A B : Type) (f : A -> G1 B),
      ϕ (T B) ∘ traverse f = traverse (T := T) (ϕ B ∘ f).
  Proof.
    intros.
    unfold_ops @Traverse_ToBatch.
    reassociate <- on left.
    rewrite (runBatch_morphism').
    reflexivity.
  Qed.

  #[export] Instance TraversableFunctor_Kleisli_From_Coalgebraic :
    Kleisli.TraversableFunctor.TraversableFunctor T :=
    {| trf_traverse_id := traverse_id;
      trf_traverse_traverse := @traverse_traverse;
      trf_traverse_morphism := @traverse_morphism;
    |}.

End DerivedInstances.
