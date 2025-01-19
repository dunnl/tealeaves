From Tealeaves Require Import
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Coalgebraic.DecoratedTraversableFunctor.

Import Product.Notations.
Import Kleisli.DecoratedTraversableFunctor.Notations.
Import Batch.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables E G T M A B.

#[local] Arguments runBatch {A B}%type_scope {F}%function_scope
  {H H0 H1} ϕ%function_scope {C}%type_scope b.
#[local] Arguments batch {A} (B)%type_scope _.


(** * Coalgebraic DTFs from Kleisli DTFs *)
(******************************************************************************)

(** ** Derived Operations *)
(******************************************************************************)
Module DerivedOperations.

  #[export] Instance ToBatch3_Mapdt `{Mapdt E T}
 : Coalgebraic.DecoratedTraversableFunctor.ToBatch3 E T :=
  (fun A B => mapdt (G := Batch (E * A) B) (batch B):
     T A -> Batch (E * A) B (T B)).

End DerivedOperations.

(** ** Coalgebra laws *)
(******************************************************************************)
Module DerivedInstances.

  Import DerivedOperations.

  Section to_coalgebraic.

    Context
      `{Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}.

    Lemma double_Batch3_spec: forall A B C,
        double_batch3 (E := E) (A := A) (B := B) C = batch C ⋆3 batch B.
    Proof.
      intros. unfold double_batch3. now ext [e a].
    Qed.

    Lemma toBatch3_extract_Kleisli: forall (A: Type),
        extract_Batch ∘ mapfst_Batch _ _ (extract (W := (E ×))) ∘ toBatch3 = @id (T A).
    Proof.
      intros.
      reassociate -> on left.
      unfold toBatch3.
      unfold ToBatch3_Mapdt.
      rewrite (kdtf_morph (T := T)
                 (morphism := ApplicativeMorphism_mapfst_Batch
                                (extract (W := prod E) (A := A)))
                 (batch A)).
      Check mapdt (mapfst_Batch (E * A) A extract ∘ batch A).
      rewrite (kdtf_morph
                 (G1 := Batch A A)
                 (G2 := fun A => A)
                 (morphism := ApplicativeMorphism_extract_Batch _)).
      reassociate <- on left.
      assert (cut: extract_Batch ∘ mapfst_Batch (E * A) A extract ∘ batch A
              = extract).
      { ext [e a]. reflexivity. }
      rewrite cut.
      rewrite kdtf_mapdt1.
      reflexivity.
    Qed.

    Lemma toBatch3_duplicate_Kleisli: forall (A B C: Type),
        cojoin_Batch3 ∘ toBatch3 (A := A) (B := C) =
          map (F := Batch (E * A) B) (toBatch3) ∘ toBatch3.
      intros.
      unfold_ops @ToBatch3_Mapdt.
      rewrite (kdtf_morph (T := T) (E := E) (B := C)
                 (G1 := Batch (E * A) C)
                 (G2 := Batch (E * A) B ∘ Batch (E * B) C)
                 (morphism := ApplicativeMorphism_cojoin_Batch3 _ _ _)
                 (ϕ := @cojoin_Batch3 E _ _ A C B)).
      rewrite (kdtf_mapdt2 _ _).
      rewrite <- double_Batch3_spec.
      rewrite <- (cojoin_Batch3_batch (E := E) (T := T)).
      reflexivity.
    Qed.

    #[export] Instance Coalgebraic_DecoratedTraversableFunctor_of_Kleisli :
      Coalgebraic.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T :=
      {| dtf_extract := toBatch3_extract_Kleisli;
         dtf_duplicate := toBatch3_duplicate_Kleisli;
      |}.

  End to_coalgebraic.

End DerivedInstances.
