From Tealeaves Require Import
  Classes.Kleisli.TraversableMonad
  Classes.Coalgebraic.TraversableMonad
  Functors.Batch.

Import Applicative.Notations.

#[local] Generalizable Variables G.

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
    (T : Type -> Type)
    `{Coalgebraic.TraversableMonad.TraversableMonad T}.

  Lemma ktm_bindt0_T :
    forall `{Applicative G} (A B : Type) (f : A -> G (T B)),
      bindt G A B f ∘ ret T A = f.
  Proof.
    intros.
    unfold_ops Bindt_ToBatchM; unfold bindt_ToBatchM.
    reassociate -> on left.
    rewrite (trfm_ret).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.


  Lemma ktm_bindt1_T : forall (A : Type),
      bindt (fun A : Type => A) A A (ret T A) = (@id (T A)).
  Proof.
    intros.
    unfold id. ext t.
    unfold_ops Bindt_ToBatchM; unfold bindt_ToBatchM.
    assert (lemma : @runBatch A (T A) (fun X => X) _ _ _ (ret T A) (T A) =
              extract_Batch ∘ mapfst_Batch A (T A) (ret T A)).
    { rewrite (runBatch_spec (fun A => A)).
      rewrite <- (TraversableFunctor.map_to_traverse).
      rewrite <- map_compat_traverse_Batch1.
      reflexivity. }
    rewrite lemma.
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
    kc3 T G1 G2 g f =
      runBatch G1 f (G2 (T C)) ∘ map (Batch A (T B)) (runBatch G2 g (T C))
        ∘ double_BatchM T A B C.
  Proof.
    ext a.
    unfold kc3.
    cbn. unfold id, compose.
    rewrite (map_to_ap).
    reflexivity.
  Qed.

  Lemma ktm_bindt2_T :
    forall (G1 G2 : Type -> Type) (H1 : Map G1)
      (H2 : Pure G1) (H4 : Mult G1),
      Applicative G1 ->
      forall (H6 : Map G2) (H7 : Pure G2) (H8 : Mult G2),
        Applicative G2 ->
        forall (A B C : Type) (g : B -> G2 (T C)) (f : A -> G1 (T B)),
          map G1 (bindt G2 B C g) ∘ bindt G1 A B f =
            bindt (G1 ∘ G2) A C (kc3 T G1 G2 g f).
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
               (H9 := ApplicativeMorphism_parallel
                        (Batch A (T B)) (Batch B (T C)) G1 G2)).
    rewrite (kc3_spec G1 G2).
    reflexivity.
  Qed.

  Lemma ktm_morph_T :
    forall (G1 G2 : Type -> Type) (H1 : Map G1)
      (H2 : Pure G1) (H4 : Mult G1) (H5 : Map G2)
      (H6 : Pure G2) (H7 : Mult G2)
      (ϕ : forall A : Type, G1 A -> G2 A),
      ApplicativeMorphism G1 G2 ϕ ->
      forall (A B : Type) (f : A -> G1 (T B)),
        ϕ (T B) ∘ bindt G1 A B f = bindt G2 A B (ϕ (T B) ∘ f).
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
      ktm_bindt2 := ktm_bindt2_T;
      ktm_morph := ktm_morph_T;
    |}.

End with_algebra.
