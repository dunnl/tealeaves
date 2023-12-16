From Tealeaves Require Import
  Classes.Kleisli.TraversableMonad
  Classes.Coalgebraic.TraversableMonad
  Functors.Batch.

Import Applicative.Notations.

#[local] Generalizable Variables T G ϕ.

(** * Coalgebraic to traversable monad *)
(******************************************************************************)
Definition bindt_ToBatchM
  (T : Type -> Type)
  `{ToBatchM T} (A B : Type) F
  `{Mult F} `{Map F} `{Pure F} (f : A -> F (T B)) :
  T A -> F (T B) :=
  runBatch F f (T B) ∘ toBatchM T A B.

#[export] Instance Bindt_ToBatchM
  (T : Type -> Type) `{ToBatchM T} : Bindt T T :=
  fun F _ _ _ A B f => bindt_ToBatchM T A B F f.

Section with_algebra.

  Context
    `{Coalgebraic.TraversableMonad.TraversableMonad T}.

  Lemma ktm_bindt0_T :
    forall `{Applicative G} (A B : Type) (f : A -> G (T B)),
      bindt (T := T) (G := G) f ∘ ret = f.
  Proof.
    intros.
    unfold_ops Bindt_ToBatchM; unfold bindt_ToBatchM.
    reassociate -> on left.
    rewrite (trfm_ret).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Lemma ktm_bindt1_T : forall (A : Type),
      bindt (G := fun A : Type => A) (ret (T := T)) = (@id (T A)).
  Proof.
    intros.
    unfold id. ext t.
    unfold_ops Bindt_ToBatchM; unfold bindt_ToBatchM.
    assert (lemma : @runBatch A (T A) (fun X => X) _ _ _ (@ret T _ A) (T A) =
              extract_Batch ∘ mapfst_Batch A (T A) (@ret T _ A)).
    { rewrite (runBatch_spec (fun A => A)).
      rewrite <- (TraversableFunctor.map_to_traverse).
      rewrite <- map_compat_traverse_Batch1.
      reflexivity. }
    setoid_rewrite lemma.
    rewrite trfm_extract.
    reflexivity.
  Qed.

  Lemma kc3_spec
    {A B C : Type}
    (G1 G2 : Type -> Type)
    `{Map G1} `{Pure G1} `{Mult G1} `{! Applicative G1}
    `{Map G2} `{Pure G2} `{Mult G2} `{! Applicative G2}
    (g : B -> G2 (T C))
    (f : A -> G1 (T B)) :
    kc3 (G1 := G1) (G2 := G2) g f =
      runBatch G1 f (G2 (T C)) ∘ map (F := Batch A (T B)) (runBatch G2 g (T C))
        ∘ double_BatchM T A B C.
  Proof.
    ext a.
    unfold kc3.
    cbn. unfold id, compose.
    rewrite (map_to_ap).
    reflexivity.
  Qed.

  Lemma ktm_bindt2_T :
    forall `{Applicative G1} `{Applicative G2},
        forall (A B C : Type) (g : B -> G2 (T C)) (f : A -> G1 (T B)),
          map (F := G1) (bindt (G := G2) g) ∘ bindt (G := G1) f =
            bindt (G := G1 ∘ G2) (kc3 (G1 := G1) (G2 := G2) g f).
  Proof.
    intros.
    unfold_ops Bindt_ToBatchM; unfold bindt_ToBatchM.
    reassociate <- on left.
    rewrite <- (fun_map_map (F := G1)).
    reassociate -> near (runBatch G1 f (T B)).
    rewrite natural.
    reassociate <- on left.
    reassociate -> near (toBatchM T A B).
    rewrite <- (trfm_duplicate).
    rewrite cojoin_BatchM_spec.
    reassociate <- on left.
    rewrite (natural).
    rewrite (runBatch_morphism'
               (homomorphism := ApplicativeMorphism_parallel
                        (Batch A (T B)) (Batch B (T C)) G1 G2)).
    rewrite (kc3_spec G1 G2).
    reflexivity.
  Qed.

  Lemma ktm_morph_T :
    forall `{ApplicativeMorphism G1 G2 ϕ},
      forall (A B : Type) (f : A -> G1 (T B)),
        ϕ (T B) ∘ bindt (G := G1) f = bindt (G := G2) (ϕ (T B) ∘ f).
  Proof.
    intros.
    unfold_ops Bindt_ToBatchM; unfold bindt_ToBatchM.
    reassociate <- on left.
    now rewrite (runBatch_morphism').
  Qed.

  #[export] Instance TraversableMonad_Kleisli_Coalgebraic :
    Kleisli.TraversableMonad.TraversableMonad T :=
    {| ktm_bindt0 := @ktm_bindt0_T;
      ktm_bindt1 := ktm_bindt1_T;
      ktm_bindt2 := @ktm_bindt2_T;
      ktm_morph := @ktm_morph_T;
    |}.

End with_algebra.
