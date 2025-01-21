From Tealeaves Require Import
  Classes.Kleisli.TraversableMonad
  Classes.Coalgebraic.TraversableMonad
  Functors.Early.Batch.

Import Batch.Notations.
Import Applicative.Notations.
Import TraversableMonad.Notations.

#[local] Generalizable Variables T G ϕ.

(** * Kleisli Traversable Monad from Kleisli Traversable Monad *)
(******************************************************************************)

(** ** Derived Operation <<toBatch6>> *)
(******************************************************************************)
Module DerivedOperations.

  #[export] Instance Bindt_ToBatch6
    (T U : Type -> Type) `{ToBatch6 T U} : Bindt T U :=
  fun G _ _ _ A B f => runBatch (G := G) f (C := U B) ∘ toBatch6.

End DerivedOperations.

(** ** Derived Operation <<toBatch6>> *)
(******************************************************************************)
Module DerivedInstances.

  Import DerivedOperations.

  Section with_algebra.

    Context
      `{Coalgebraic.TraversableMonad.TraversableMonad T}.

    Lemma kc6_spec
      {A B C : Type}
      (G1 G2 : Type -> Type)
      `{Map G1} `{Pure G1} `{Mult G1} `{! Applicative G1}
      `{Map G2} `{Pure G2} `{Mult G2} `{! Applicative G2}
      (g : B -> G2 (T C))
      (f : A -> G1 (T B)) :
      kc6 (G1 := G1) (G2 := G2) g f =
        runBatch f (C := G2 (T C)) ∘ map (F := Batch A (T B)) (runBatch g)
          ∘ double_batch6.
    Proof.
      ext a.
      unfold compose.
      rewrite double_batch6_rw.
      rewrite map_Batch_rw2.
      rewrite map_Batch_rw1.
      rewrite runBatch_rw2.
      rewrite runBatch_rw1.
      rewrite <- map_to_ap.
      reflexivity.
    Qed.

    Lemma ktm_bindt0_T :
      forall `{Applicative G} (A B : Type) (f : A -> G (T B)),
        bindt (T := T) (G := G) f ∘ ret = f.
    Proof.
      intros.
      unfold_ops Bindt_ToBatch6.
      reassociate -> on left.
      rewrite trfm_ret.
      rewrite (runBatch_batch G).
      reflexivity.
    Qed.

    Lemma ktm_bindt1_T : forall (A : Type),
        bindt (G := fun A : Type => A) (ret (T := T)) = (@id (T A)).
    Proof.
      intros.
      unfold_ops Bindt_ToBatch6.
      assert (cut: runBatch (G := fun A => A) (ret (T := T) (A := A)) (C := T A) =
                     extract_Batch ∘ mapfst_Batch _ _ ret).
      { unfold compose. ext b. induction b.
        - reflexivity.
        - cbn. rewrite IHb.
          reflexivity. }
      rewrite cut.
      rewrite trfm_extract.
      reflexivity.
    Qed.

    Lemma ktm_bindt2_T :
      forall `{Applicative G1} `{Applicative G2},
      forall (A B C : Type) (g : B -> G2 (T C)) (f : A -> G1 (T B)),
        map (F := G1) (bindt (G := G2) g) ∘ bindt (G := G1) f =
          bindt (G := G1 ∘ G2) (kc6 (G1 := G1) (G2 := G2) g f).
    Proof.
      intros.
      unfold_ops Bindt_ToBatch6.
      reassociate <- on left.
      rewrite <- (fun_map_map (F := G1)).
      reassociate -> near (runBatch f).
      rewrite natural.
      reassociate <- on left.
      reassociate -> near toBatch6.
      rewrite <- trfm_duplicate.
      rewrite cojoin_Batch6_to_runBatch.
      reassociate <- on left.
      rewrite natural.
      rewrite (runBatch_morphism'
                 (homomorphism := ApplicativeMorphism_parallel
                                    (Batch A (T B)) (Batch B (T C)) G1 G2)).
      rewrite (kc6_spec G1 G2).
      reflexivity.
    Qed.

    Lemma ktm_morph_T :
      forall `{ApplicativeMorphism G1 G2 ϕ},
      forall (A B : Type) (f : A -> G1 (T B)),
        ϕ (T B) ∘ bindt (G := G1) f = bindt (G := G2) (ϕ (T B) ∘ f).
    Proof.
      intros.
      unfold_ops Bindt_ToBatch6.
      reassociate <- on left.
      now rewrite runBatch_morphism'.
    Qed.

    #[export] Instance:
      Kleisli.TraversableMonad.TraversableRightPreModule T T :=
      {| ktm_bindt1 := ktm_bindt1_T;
        ktm_bindt2 := @ktm_bindt2_T;
        ktm_morph := @ktm_morph_T;
      |}.

    #[export] Instance TraversableMonad_Kleisli_Coalgebraic :
      Kleisli.TraversableMonad.TraversableMonad T :=
      {| ktm_bindt0 := @ktm_bindt0_T;
      |}.

  End with_algebra.

End DerivedInstances.
