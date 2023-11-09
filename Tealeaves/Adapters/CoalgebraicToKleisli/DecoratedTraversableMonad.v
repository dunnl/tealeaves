
(** * Coalgebraic DTMs to Kleisli DTM *)
(******************************************************************************)
Definition binddt_ToBatchDM
  (W : Type)
  (T : Type -> Type)
  `{ToBatchDM W T} (A B : Type) F
  `{Mult F} `{Map F} `{Pure F} (f : W * A -> F (T B)) :
  T A -> F (T B) :=
  runBatch F f (T B) ∘ toBatchDM W T A B.

#[export] Instance Binddt_Coalgebra
  (W : Type) (T : Type -> Type) `{ToBatchDM W T} : Binddt W T T :=
  fun F _ _ _ A B f => binddt_ToBatchDM W T A B F f.

Section with_algebra.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DecoratedTraversableMonad W T}.

  Lemma kdtm_binddt0_T :
    forall (F : Type -> Type) `{Applicative F}
      (A B : Type)
      (f : W * A -> F (T B)),
      binddt T F f ∘ ret T A = f ∘ pair Ƶ.
  Proof.
    intros.
    unfold_ops @Binddt_Coalgebra.
    unfold binddt_ToBatchDM.
    reassociate -> on left.
    rewrite (dtm_ret (W := W) (T := T)).
    unfold compose; ext a.
    cbn.
    now rewrite (ap1).
  Qed.

  Lemma kdtm_binddt1_T : forall (A : Type),
      binddt T (fun A : Type => A) (ret T A ∘ extract (W ×) A) = (@id (T A)).
  Proof.
    intros.
    unfold id. ext t.
    unfold_ops @Binddt_Coalgebra.
    unfold binddt_ToBatchDM.
    rewrite (runBatch_spec (fun A => A)).
    rewrite <- (TraversableFunctor.DerivedInstances.map_to_traverse).
    rewrite (map_BATCH1_spec).
    unfold_ops @Map_I.
    rewrite dtm_extract.
    reflexivity.
  Qed.

  Lemma kc7_spec :
    forall (G1 G2 : Type -> Type)
      `{Applicative G1}
      `{Applicative G2},
        forall (A B C : Type)
          (g : W * B -> G2 (T C)) (f : W * A -> G1 (T B)),
          runBatch G1 f (G2 (T C)) ∘ map (Batch (W * A) (T B)) (runBatch G2 g (T C)) ∘ new_double_batch W T A B C =
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

  Lemma kdtm_binddt2_T :
    forall (G1 G2 : Type -> Type) (H1 : Map G1) (H2 : Pure G1) (H5 : Mult G1),
      Applicative G1 ->
      forall (H7 : Map G2) (H8 : Pure G2) (H9 : Mult G2),
        Applicative G2 ->
        forall (A B C : Type) (g : W * B -> G2 (T C)) (f : W * A -> G1 (T B)),
          map G1 (binddt T G2 g) ∘ binddt T G1 f = binddt T (G1 ∘ G2) (g ⋆7 f).
  Proof.
    intros.
    unfold id. ext t.
    unfold_ops @Binddt_Coalgebra.
    unfold binddt_ToBatchDM.
    rewrite <- (fun_map_map (F := G1)).
    reassociate -> on left.
    reassociate <- near (map G1 (toBatchDM W T B C)).
    rewrite (natural (ϕ := runBatch G1 f)).
    reassociate -> on left.
    rewrite <- (dtm_duplicate).
    repeat reassociate <-.
    rewrite (natural (ϕ := runBatch G1 f)).
    rewrite (cojoin_Batch_rw0).
    rewrite (runBatch_morphism'
               (H9 := ApplicativeMorphism_parallel (Batch (W * A) (T B))
                        (Batch (W * B) (T C)) G1 G2)).
    unfold_compose_in_compose.
    rewrite (kc7_spec G1 G2).
    reflexivity.
  Qed.

  Lemma kdtm_morph_T :
    forall (G1 G2 : Type -> Type) `{Map G1} `{Pure G1} `{Mult G1}
      `{Map G2} `{Pure G2} `{Mult G2}
      (ϕ : forall A : Type, G1 A -> G2 A),
      `{ApplicativeMorphism G1 G2 ϕ} ->
      forall (A B : Type) (f : W * A -> G1 (T B)), ϕ (T B) ∘ binddt T G1 f = binddt T G2 (ϕ (T B) ∘ f).
  Proof.
    intros.
    unfold id. ext t.
    unfold_ops @Binddt_Coalgebra.
    unfold binddt_ToBatchDM.
    reassociate <- on left.
    rewrite (runBatch_morphism').
    reflexivity.
  Qed.

#[export] Instance TraversableMonad_Kleisli_Coalgebra :
  Classes.Kleisli.DecTravMonad.DecTravMonad W T :=
  {|
    kdtm_binddt0 := kdtm_binddt0_T;
    kdtm_binddt1 := kdtm_binddt1_T;
    kdtm_binddt2 := kdtm_binddt2_T;
    kdtm_morph := kdtm_morph_T;
  |}.

End with_algebra.
