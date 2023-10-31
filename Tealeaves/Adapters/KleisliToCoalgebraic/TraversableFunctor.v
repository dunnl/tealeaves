From Tealeaves Require Export
  Misc.Prop
  Functors.Subset
  Functors.List
  Functors.Batch
  Classes.Kleisli.TraversableFunctor.

From Tealeaves Require Import
  Classes.Coalgebraic.TraversableFunctor (ToBatch, toBatch).

Import TraversableFunctor.Notations.
Import Batch.Notations.

#[local] Generalizable Variable M.

#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.
#[local] Arguments traverse (T)%function_scope {Traverse} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.

Import Kleisli.TraversableFunctor.DerivedInstances.

(** * Traversals as <<Batch>> coalgebras *)
(******************************************************************************)
#[export] Instance ToBatch_Traverse
 (T : Type -> Type) `{Traverse T}
    : Coalgebraic.TraversableFunctor.ToBatch T :=
  (fun A B => traverse T (Batch A B) A B (batch B A) : T A -> Batch A B (T B)).

(** ** Factoring operations through <<toBatch>> *)
(******************************************************************************)
Section runBatch.

  Context
    (T : Type -> Type)
    `{Kleisli.TraversableFunctor.TraversableFunctor T}.

  Lemma traverse_to_runBatch (G : Type -> Type)
    `{Applicative G} {A B : Type} (f : A -> G B) :
    traverse T G A B f = runBatch G f (T B) ∘ toBatch T A B.
  Proof.
    unfold_ops @ToBatch_Traverse.
    rewrite (trf_traverse_morphism (ϕ := runBatch G f)).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Corollary map_to_runBatch {A B : Type} (f : A -> B) :
    map T A B f = runBatch (fun A => A) f (T B) ∘ toBatch T A B.
  Proof.
    rewrite (map_to_traverse).
    rewrite (traverse_to_runBatch (fun A => A)).
    reflexivity.
  Qed.

  Corollary id_to_runBatch : forall (A : Type),
      id (A := T A) = runBatch (fun A => A) id (T A) ∘ toBatch T A A.
  Proof.
    intros. rewrite <- (trf_traverse_id (T := T)).
    rewrite (traverse_to_runBatch (fun A => A)).
    reflexivity.
  Qed.

End runBatch.

(** ** Naturality of <<toBatch>> *)
(******************************************************************************)
Lemma toBatch_mapfst (T : Type -> Type)
  `{Kleisli.TraversableFunctor.TraversableFunctor T}
  {A B : Type} (f : A -> B) {C : Type} :
  toBatch T B C ∘ map T A B f = mapfst_Batch A B f ∘ toBatch T A C.
Proof.
  unfold_ops @ToBatch_Traverse.
  rewrite (traverse_map T (Batch B C)).
  rewrite (traverse_to_runBatch T (Batch B C)).
  rewrite (traverse_to_runBatch T (Batch A C)).
  ext t.
  unfold compose.
  induction (toBatch T A C t).
  - cbv. reflexivity.
  - do 2 rewrite runBatch_rw2. rewrite IHb.
    now rewrite mapfst_Batch2.
Qed.

(** ** Coalgebra laws *)
(******************************************************************************)
Section traversals_coalgebras.

  Context
    (T : Type -> Type)
    `{Kleisli.TraversableFunctor.TraversableFunctor T}.

  #[local] Arguments extract_Batch {A} (B)%type_scope b.

  Lemma toBatch_extract_Kleisli : forall (A : Type),
      extract_Batch (T A) ∘ toBatch T A A = @id (T A).
  Proof.
    intros.
    unfold_ops @ToBatch_Traverse.
    rewrite (trf_traverse_morphism (ϕ := extract_Batch)).
    rewrite (trf_traverse_id).
    reflexivity.
  Qed.

  Lemma toBatch_duplicate_Kleisli : forall (A B C : Type),
      cojoin_Batch ∘ toBatch T A C =
        map (Batch A B) _ _ (toBatch T B C) ∘ toBatch T A B.
  Proof.
    intros.
    unfold_ops @ToBatch_Traverse.
    rewrite (trf_traverse_morphism (T := T) (ϕ := @cojoin_Batch A B C)).
    rewrite (cojoin_Batch_batch).
    rewrite (trf_traverse_traverse (T := T) (Batch A B) (Batch B C)).
    reflexivity.
  Qed.

  Import Coalgebraic.TraversableFunctor.

  #[export] Instance Coalgebraic_Traversable_of_Kleisli :
    Coalgebraic.TraversableFunctor.TraversableFunctor T :=
    {| trf_extract := toBatch_extract_Kleisli;
      trf_duplicate := toBatch_duplicate_Kleisli;
    |}.

End traversals_coalgebras.
