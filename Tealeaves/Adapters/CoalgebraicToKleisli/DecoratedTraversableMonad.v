From Tealeaves Require Import
  Classes.Kleisli.DecoratedTraversableMonad
  Classes.Coalgebraic.DecoratedTraversableMonad
  Functors.Batch.

Import Batch.Notations.
Import Monoid.Notations.
Import Applicative.Notations.
Import Product.Notations.
Import DecoratedTraversableMonad.Notations.

#[local] Generalizable Variables W T G ϕ.

#[local] Arguments runBatch {A B}%type_scope {F}%function_scope {H H0 H1} ϕ%function_scope {C}%type_scope b.
#[local] Arguments batch {A} (B)%type_scope _.
#[local] Arguments mapfst_Batch {B C}%type_scope {A1 A2}%type_scope f%function_scope b.
#[local] Arguments mapsnd_Batch {A}%type_scope {B1 B2}%type_scope {C}%type_scope f%function_scope b.

(** * Coalgebraic DTMs to Kleisli DTM *)
(******************************************************************************)
#[export] Instance Binddt_ToBatch7
  (W : Type) (T : Type -> Type) `{ToBatch7 W T} : Binddt W T T :=
  fun F _ _ _ A B f => runBatch f (C := T B) ∘ toBatch7.

Section with_algebra.

  Context
    `{Coalgebraic.DecoratedTraversableMonad.DecoratedTraversableMonad W T}.

  Lemma kc7_spec :
    forall (G1 G2 : Type -> Type)
      `{Applicative G1}
      `{Applicative G2},
    forall (A B C : Type)
      (g : W * B -> G2 (T C)) (f : W * A -> G1 (T B)),
      g ⋆7 f =
        runBatch (F := G1) f (C := G2 (T C)) ∘
          map (F := Batch (W * A) (T B)) (runBatch (F := G2) g (C := T C)) ∘
          double_batch7.
  Proof.
    intros. ext [w a].
    unfold compose.
    rewrite (double_batch7_rw (w, a)).
    rewrite map_Batch_rw2.
    rewrite map_Batch_rw1.
    rewrite runBatch_rw2.
    rewrite runBatch_rw1.
    rewrite <- (map_to_ap).
    reassociate <- on right.
    rewrite <- runBatch_mapfst'.
    reflexivity.
  Qed.

  Lemma kdtm_binddt0_T :
    forall (F : Type -> Type) `{Applicative F}
      (A B : Type)
      (f : W * A -> F (T B)),
      binddt f ∘ ret = f ∘ pair Ƶ.
  Proof.
    intros.
    unfold_ops @Binddt_ToBatch7.
    reassociate -> on left.
    rewrite (dtm_ret (W := W) (T := T)).
    unfold compose; ext a.
    rewrite runBatch_rw2.
    rewrite runBatch_rw1.
    rewrite ap1.
    reflexivity.
  Qed.

  Lemma kdtm_binddt1_T : forall (A : Type),
      binddt (G := fun A : Type => A) (ret (T := T) ∘ extract (W := (W ×))) = @id (T A).
  Proof.
    intros.
    unfold_ops @Binddt_ToBatch7.
    rewrite (runBatch_spec (F := fun A => A)).
    rewrite <- map_to_traverse.
    apply dtm_extract.
  Qed.

  Lemma kdtm_binddt2_T :
    forall (G1 G2 : Type -> Type) (H1 : Map G1) (H2 : Pure G1) (H5 : Mult G1),
      Applicative G1 ->
      forall (H7 : Map G2) (H8 : Pure G2) (H9 : Mult G2),
        Applicative G2 ->
        forall (A B C : Type) (g : W * B -> G2 (T C)) (f : W * A -> G1 (T B)),
          map (F := G1) (binddt g) ∘ binddt f =
            binddt (G := G1 ∘ G2) (g ⋆7 f).
  Proof.
    intros.
    unfold_ops @Binddt_ToBatch7.
    reassociate <- on left.
    rewrite <- (fun_map_map (F := G1)).
    reassociate -> near (runBatch f).
    rewrite natural.
    reassociate <- on left.
    reassociate -> near toBatch7.
    rewrite <- dtm_duplicate.
    rewrite cojoin_Batch7_to_runBatch.
    reassociate <- on left.
    rewrite natural.
    rewrite (runBatch_morphism'
               (homomorphism := ApplicativeMorphism_parallel
                        (Batch (W * A) (T B)) (Batch (W * B) (T C)) G1 G2)).
    rewrite (kc7_spec G1 G2).
    reflexivity.
  Qed.

  Lemma kdtm_morph_T :
    forall (G1 G2 : Type -> Type) `{morph : ApplicativeMorphism G1 G2 ϕ},
      forall (A B : Type) (f : W * A -> G1 (T B)),
        ϕ (T B) ∘ binddt f = binddt (ϕ (T B) ∘ f).
  Proof.
    intros. ext t.
    unfold_ops @Binddt_ToBatch7.
    reassociate <- on left.
    rewrite runBatch_morphism'.
    reflexivity.
  Qed.

(* TODO

  #[export] Instance DecoratedTraversableRightPreModule_Kleisli_Coalgebra :
    Classes.Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T :=
    {|
      kdtm_binddt1 := kdtm_binddt1_T;
      kdtm_binddt2 := kdtm_binddt2_T;
      kdtm_morph := kdtm_morph_T;
    |}.

  #[export] Instance DecoratedTraversableMonad_Kleisli_Coalgebra :
    Classes.Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T :=
    {|
      kdtm_binddt0 := kdtm_binddt0_T;
    |}.
    *)

End with_algebra.
