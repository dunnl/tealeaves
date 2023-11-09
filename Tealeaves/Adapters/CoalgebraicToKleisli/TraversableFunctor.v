From Tealeaves Require Export
  Functors.Batch
  Classes.Coalgebraic.TraversableFunctor.

Import Batch.Notations.
Import Applicative.Notations.
Import TraversableFunctor.Notations.

Definition traverse_ToBatch
  (T : Type -> Type)
  `{ToBatch T} (A B : Type) F
  `{Mult F} `{Map F} `{Pure F} (f : A -> F B) :
  T A -> F (T B) :=
  runBatch F f (T B) ∘ toBatch T A B.

#[export] Instance Traverse_Coalgebra
  (T : Type -> Type) `{ToBatch T} : Traverse T :=
  fun F _ _ _ A B f => traverse_ToBatch T A B F f.

Section with_algebra.

  Context
    (T : Type -> Type)
      `{TraversableFunctor T}.

  Lemma traverse_id : forall (A : Type),
      traverse T (fun A => A) id = @id (T A).
  Proof.
    intros.
    unfold_ops @Traverse_Coalgebra.
    unfold traverse_ToBatch.
    rewrite <- (extract_Batch_to_runBatch).
    rewrite trf_extract.
    reflexivity.
  Qed.

  Lemma k2_spec :
    forall (G1 G2 : Type -> Type)
      (H0 : Map G1) (H2 : Pure G1)
      (H3 : Mult G1),
      Applicative G1 ->
      forall (H5 : Map G2)
        (H6 : Pure G2) (H7 : Mult G2),
        Applicative G2 ->
        forall (A B C : Type)
          (g : B -> G2 C) (f : A -> G1 B),
          runBatch _ f (G2 C) ∘ map (Batch A B) (runBatch _ g C) ∘ double_batch =
            kc2 G1 G2 g f.
  Proof.
    intros.
    ext a.
    unfold compose.
    cbn.
    reassociate <-.
    rewrite (runBatch_batch G2).
    change (g ∘ id) with g.
    rewrite <- map_to_ap.
    reflexivity.
  Qed.

  Lemma traverse_traverse :
    forall (G1 G2 : Type -> Type)
      (H0 : Map G1) (H2 : Pure G1)
      (H3 : Mult G1),
      Applicative G1 ->
      forall (H5 : Map G2)
        (H6 : Pure G2) (H7 : Mult G2),
        Applicative G2 ->
        forall (A B C : Type)
          (g : B -> G2 C) (f : A -> G1 B),
          map G1 (traverse T G2 g) ∘ traverse T G1 f =
            traverse T (G1 ∘ G2) (kc2 G1 G2 g f).
  Proof.
    intros.
    unfold_ops @Traverse_Coalgebra.
    unfold traverse_ToBatch.
    rewrite <- (fun_map_map (F := G1)).
    reassociate ->.
    reassociate <- near (map G1 (toBatch T B C)).
    rewrite natural.
    reassociate ->.
    rewrite <- trf_duplicate.
    repeat reassociate <-.
    rewrite cojoin_Batch_to_runBatch.
    rewrite (natural (G := G1) (F := Batch A B)).
    rewrite (runBatch_morphism'
               (H9 := ApplicativeMorphism_parallel (Batch A B) (Batch B C) G1 G2)).
    unfold_compose_in_compose.
    rewrite (k2_spec G1 G2 _ _ _ _ _ _ _ _).
    reflexivity.
  Qed.

End with_algebra.
