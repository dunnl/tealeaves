From Tealeaves Require Import
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Coalgebraic.DecoratedTraversableFunctor
  Functors.Early.Batch.

Import Monoid.Notations.
Import Applicative.Notations.
Import Product.Notations.
Import DecoratedTraversableFunctor.Notations.

#[local] Generalizable Variables E T G ϕ.

(** * Coalgebraic DTFs to Kleisli DTFs *)
(**********************************************************************)

(** ** Derived Operations *)
(**********************************************************************)
Module DerivedOperations.

  #[export] Instance Mapdt_ToBatch3
    (E: Type) (T: Type -> Type)
    `{ToBatch3 E T}: Mapdt E T :=
  fun G _ _ _ A B f =>
    (runBatch f ∘ toBatch3: T A -> G (T B)).

End DerivedOperations.

(** ** Derived Laws *)
(**********************************************************************)
Module DerivedInstances.

  Import DerivedOperations.

  Section with_algebra.

    Context
      `{Coalgebraic.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}.

    Lemma kc3_spec:
      forall `{Applicative G1}
             `{Applicative G2},
      forall (A B C: Type)
             (g: E * B -> G2 C) (f: E * A -> G1 B),
        g ⋆3 f =
          runBatch (G := G1) f (C := G2 C) ∘
            map (F := Batch (E * A) B) (runBatch (G := G2) g (C := C)) ∘
            double_batch3 C.
    Proof.
      intros. ext [e a].
      unfold compose.
      rewrite (double_batch3_rw (e, a)).
      rewrite map_Batch_rw2.
      rewrite map_Batch_rw1.
      rewrite runBatch_rw2.
      rewrite runBatch_rw1.
      rewrite <- (map_to_ap).
      reassociate <- on right.
      rewrite (runBatch_batch G2).
      rewrite kc3_spec.
      reflexivity.
    Qed.

    Lemma kdtf_mapdt1_T: forall (A: Type),
        mapdt (G := fun A: Type => A) (extract (W := (E ×))) = @id (T A).
    Proof.
      intros.
      unfold_ops @Mapdt_ToBatch3.
      rewrite (runBatch_via_traverse (F := fun A => A)).
      rewrite <- TraversableFunctor.map_to_traverse.
      rewrite <- dtf_extract.
      reflexivity.
    Qed.

    Lemma kdtf_mapdt2_T:
      forall `{Applicative G1}
        `{Applicative G2},
      forall (A B C: Type) (g: E * B -> G2 C) (f: E * A -> G1 B),
        map (F := G1) (mapdt g) ∘ mapdt f =
          mapdt (G := G1 ∘ G2) (g ⋆3 f).
    Proof.
      intros.
      unfold_ops @Mapdt_ToBatch3.
      reassociate <- on left.
      rewrite <- (fun_map_map (F := G1)).
      reassociate -> near (runBatch f).
      rewrite natural.
      reassociate <- on left.
      reassociate -> near toBatch3.
      rewrite <- dtf_duplicate.
      rewrite cojoin_Batch3_to_runBatch.
      reassociate <- on left.
      rewrite natural.
      rewrite (runBatch_morphism'
                 (homomorphism := ApplicativeMorphism_parallel
                                    (Batch (E * A) B) (Batch (E * B) C) G1 G2)).
      rewrite kc3_spec.
      reflexivity.
    Qed.

    Lemma kdtf_morph_T:
      forall (G1 G2: Type -> Type) `{morph: ApplicativeMorphism G1 G2 ϕ},
      forall (A B: Type) (f: E * A -> G1 B),
        ϕ (T B) ∘ mapdt f = mapdt (ϕ B ∘ f).
    Proof.
      intros. ext t.
      unfold_ops @Mapdt_ToBatch3.
      reassociate <- on left.
      rewrite runBatch_morphism'.
      reflexivity.
    Qed.

    (** ** Typeclass Instances *)
    (******************************************************************)
    #[export] Instance TraversableFunctor_Kleisli_Coalgebra:
      Classes.Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T :=
      {|
        kdtf_mapdt1 := kdtf_mapdt1_T;
        kdtf_mapdt2 := @kdtf_mapdt2_T;
        kdtf_morph := kdtf_morph_T;
      |}.

  End with_algebra.

End DerivedInstances.
