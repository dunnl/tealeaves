From Tealeaves Require Import
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Coalgebraic.DecoratedTraversableFunctor
  Functors.Batch.

Import Monoid.Notations.
Import Applicative.Notations.
Import Product.Notations.
Import DecoratedTraversableFunctor.Notations.

#[local] Generalizable Variables E T G ϕ.

#[local] Arguments map {F}%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments traverse {T}%function_scope {Traverse} {G}%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments runBatch {A B}%type_scope {F}%function_scope {H H0 H1} ϕ%function_scope {C}%type_scope b.
#[local] Arguments batch {A} (B)%type_scope _.
#[local] Arguments toBatch6 {E}%type_scope {T}%function_scope {ToBatch6} {A B}%type_scope _.
#[local] Arguments traverse {T}%function_scope {Traverse} {G}%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
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


  Lemma kdtm_binddt1_T : forall (A : Type),
      mapdt (G := fun A : Type => A) (extract (W := (E ×))) = @id (T A).
  Proof.
    intros. unfold id. ext t.
    unfold_ops @Mapdt_ToBatch6.
    rewrite (runBatch_spec (fun A => A)).
    unfold_ops @Map_I.
    rewrite <- (TraversableFunctor.map_to_traverse).
    pose (dtf_extract).
    specialize (e A).
    (* TODO Need to deal with mapfst_Batch *)
  Admitted.

  Lemma kc7_spec :
    forall (G1 G2 : Type -> Type)
      `{Applicative G1}
      `{Applicative G2},
        forall (A B C : Type)
          (g : E * B -> G2 (T C)) (f : E * A -> G1 (T B)),
          runBatch (F := G1) f (C := G2 (T C)) ∘
            map (F := Batch (E * A) (T B)) (runBatch (F := G2) g (C := T C)) ∘
            double_batch6 C =
            g ⋆7 f.
  Proof.
    intros. ext [w a].
    unfold compose. cbn.
    rewrite <- (map_to_ap).
    change (?f ∘ id) with f.
    reassociate <- on left.
    fequal.
    unfold_ops @Binddt_Coalgebra.
    unfold binddt_ToBatchDM.
    fequal.
    unfold compose; ext x; rewrite <- (runBatch_mapfst).
    reflexivity.
  Qed.

  Lemma factor :
    forall (G1 G2 : Type -> Type) (H1 : Map G1) (H2 : Pure G1) (H5 : Mult G1),
      Applicative G1 ->
      forall (H7 : Map G2) (H8 : Pure G2) (H9 : Mult G2),
        Applicative G2 ->
        forall (A B C : Type) (g : E * B -> G2 (T C)) (f : E * A -> G1 (T B)),
          map (runBatch (C := T C) g) ∘ runBatch f ∘ runBatch (double_batch6 C) =
            runBatch (F := G1 ∘ G2) (g ⋆7 f).
  Proof.
    intros.
    rewrite <- (kc7_spec G1 G2).
  Admitted.

  Lemma kdtm_binddt2_T :
    forall (G1 G2 : Type -> Type) (H1 : Map G1) (H2 : Pure G1) (H5 : Mult G1),
      Applicative G1 ->
      forall (H7 : Map G2) (H8 : Pure G2) (H9 : Mult G2),
        Applicative G2 ->
        forall (A B C : Type) (g : E * B -> G2 (T C)) (f : E * A -> G1 (T B)),
          map (F := G1) (binddt g) ∘ binddt f =
            binddt (G := G1 ∘ G2) (g ⋆7 f).
  Proof.
    intros.
    unfold_ops @Binddt_Coalgebra; unfold binddt_ToBatchDM.
    rewrite <- (fun_map_map (F := G1)).
    reassociate -> on left.
    reassociate <- near (map (F := G1) (toBatch6 (A := B) (B := C))).
    rewrite (natural (ϕ := @runBatch _ _ _ _ _ _ f)).
    do 2 reassociate <- on left.
    reassociate -> on left.
    rewrite <- (dtm_duplicate).
    rewrite cojoin_BatchDM_spec.
    repeat reassociate <-.
    now rewrite factor.
  Qed.

  Lemma kdtm_morph_T :
    forall (G1 G2 : Type -> Type) `{morph : ApplicativeMorphism G1 G2 ϕ},
      forall (A B : Type) (f : E * A -> G1 (T B)),
        ϕ (T B) ∘ binddt f = binddt (ϕ (T B) ∘ f).
  Proof.
    intros. ext t.
    unfold_ops @Binddt_Coalgebra.
    unfold binddt_ToBatchDM.
    reassociate <- on left.
    rewrite (runBatch_morphism').
    reflexivity.
  Qed.

#[export] Instance TraversableFunctor_Kleisli_Coalgebra :
  Classes.Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T :=
  {|
    kdtm_binddt0 := kdtm_binddt0_T;
    kdtm_binddt1 := kdtm_binddt1_T;
    kdtm_binddt2 := kdtm_binddt2_T;
    kdtm_morph := kdtm_morph_T;
  |}.

End with_algebra.
