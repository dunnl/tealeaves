From Tealeaves Require Import
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Coalgebraic.DecoratedTraversableFunctor
  Functors.Batch.

Import Monoid.Notations.
Import Applicative.Notations.
Import Product.Notations.
Import DecoratedTraversableFunctor.Notations.

#[local] Generalizable Variables E T G ϕ.

#[local] Arguments runBatch {A B}%type_scope {F}%function_scope {H H0 H1} ϕ%function_scope {C}%type_scope b.
#[local] Arguments batch {A} (B)%type_scope _.
#[local] Arguments mapfst_Batch {B C}%type_scope {A1 A2}%type_scope f%function_scope b.
#[local] Arguments mapsnd_Batch {A}%type_scope {B1 B2}%type_scope {C}%type_scope f%function_scope b.

(** * Coalgebraic DTMs to Kleisli DTM *)
(******************************************************************************)
#[export] Instance Mapdt_ToBatch6
  (E : Type) (T : Type -> Type) `{ToBatch6 E T} : Mapdt E T :=
  fun F _ _ _ A B f => (runBatch f ∘ toBatch6 : T A -> F (T B)).

Section with_algebra.

  Context
    `{Coalgebraic.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}.

  Lemma kc6_spec :
    forall `{Applicative G1}
      `{Applicative G2},
    forall (A B C : Type)
      (g : E * B -> G2 C) (f : E * A -> G1 B),
      g ⋆6 f =
        runBatch (F := G1) f (C := G2 C) ∘
          map (F := Batch (E * A) B) (runBatch (F := G2) g (C := C)) ∘
          double_batch6 C.
  Proof.
    intros. ext [e a].
    unfold compose.
    rewrite (double_batch6_rw (e, a)).
    rewrite map_Batch_rw2.
    rewrite map_Batch_rw1.
    rewrite runBatch_rw2.
    rewrite runBatch_rw1.
    rewrite <- (map_to_ap).
    reassociate <- on right.
    rewrite (runBatch_batch G2).
    rewrite kc6_spec.
    reflexivity.
  Qed.

  Lemma kdtf_mapdt1_T : forall (A : Type),
      mapdt (G := fun A : Type => A) (extract (W := (E ×))) = @id (T A).
  Proof.
    intros.
    unfold_ops @Mapdt_ToBatch6.
    rewrite (runBatch_spec (F := fun A => A)).
    rewrite <- map_to_traverse.
    rewrite <- dtf_extract.
    reflexivity.
  Qed.

  Lemma kdtf_mapdt2_T :
    forall `{Applicative G1}
      `{Applicative G2},
        forall (A B C : Type) (g : E * B -> G2 C) (f : E * A -> G1 B),
          map (F := G1) (mapdt g) ∘ mapdt f =
            mapdt (G := G1 ∘ G2) (g ⋆6 f).
  Proof.
    intros.
    unfold_ops @Mapdt_ToBatch6.
    reassociate <- on left.
    rewrite <- (fun_map_map (F := G1)).
    reassociate -> near (runBatch f).
    rewrite natural.
    reassociate <- on left.
    reassociate -> near toBatch6.
    rewrite <- dtf_duplicate.
    rewrite cojoin_Batch6_to_runBatch.
    reassociate <- on left.
    rewrite natural.
    rewrite (runBatch_morphism'
               (homomorphism := ApplicativeMorphism_parallel
                        (Batch (E * A) B) (Batch (E * B) C) G1 G2)).
    rewrite kc6_spec.
    reflexivity.
  Qed.

  Lemma kdtf_morph_T :
    forall (G1 G2 : Type -> Type) `{morph : ApplicativeMorphism G1 G2 ϕ},
      forall (A B : Type) (f : E * A -> G1 B),
        mapdt (ϕ B ∘ f) = ϕ (T B) ∘ mapdt f.
  Proof.
    intros. ext t.
    unfold_ops @Mapdt_ToBatch6.
    reassociate <- on right.
    rewrite runBatch_morphism'.
    reflexivity.
  Qed.

#[export] Instance TraversableFunctor_Kleisli_Coalgebra :
  Classes.Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T :=
  {|
    kdtfun_mapdt1 := kdtf_mapdt1_T;
    kdtfun_mapdt2 := @kdtf_mapdt2_T;
    kdtfun_morph := kdtf_morph_T;
  |}.

End with_algebra.
