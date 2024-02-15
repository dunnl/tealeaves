From Tealeaves Require Import
  Classes.Categorical.DecoratedTraversableMonad
  Classes.Kleisli.DecoratedTraversableMonad
  CategoricalToKleisli.DecoratedMonad
  CategoricalToKleisli.DecoratedFunctor (cobind_dec).

Import Product.Notations.
Import Kleisli.Monad.Notations.
Import Kleisli.DecoratedTraversableMonad.Notations.
Import Categorical.Monad.Notations.
Import Categorical.TraversableFunctor.Notations.
Import Strength.Notations.

#[local] Generalizable Variables W T G ϕ A B C.

(** * Kleisli presentation of D-T monads *)
(******************************************************************************)
Module ToKleisli.

  #[export] Instance Binddt_categorical
    (W : Type)
    (T : Type -> Type)
    `{Map T}
    `{Decorate W T}
    `{ApplicativeDist T}
    `{Join T} : Binddt W T T :=
  fun (G : Type -> Type) `{Map G} `{Pure G} `{Mult G} (A B : Type)
    (f : W * A -> G (T B)) =>
    map (F := G) join ∘ dist T G ∘ map f ∘ dec T.

  #[local] Tactic Notation "bring" constr(x) "and" constr(y) "together" :=
    change (?f ∘ x ∘ y ∘ ?g) with (f ∘ (x ∘ y) ∘ g).

  Section adapter.

    Context
      `{Classes.Categorical.DecoratedTraversableMonad.DecoratedTraversableMonad W T}.

    Context
      (G1 : Type -> Type) `{Map G1} `{Pure G1} `{Mult G1} `{! Applicative G1}
      (G2 : Type -> Type) `{Map G2} `{Pure G2} `{Mult G2} `{! Applicative G2}.

    Definition kcompose_dtm_alt {A B C} :=
      fun `(g : W * B -> G2 (T C))
        `(f : W * A -> G1 (T B))
      => (map (F := G1) ((map (F := G2) (μ))
                    ∘ δ T G2
                    ∘ map (F := T) (g ∘ μ (T := (W ×)))
                    ∘ σ
                    ∘ map (F := (W ×)) (dec T)))
          ∘ σ
          ∘ cobind (W := (W ×)) f.

    Lemma equiv' {A B C} :
      forall  `(g : W * B -> G2 (T C))
         `(f : W * A -> G1 (T B)),
        g ⋆7 f =
          kcompose_dtm_alt g f.
    Proof.
      intros. unfold kc7.
      unfold_ops @Binddt_categorical.
      ext [w a].
      unfold kcompose_dtm_alt.
      unfold compose at 6. cbn.
      unfold compose at 6.
      cbn. compose near (f (w, a)) on right.
      rewrite (fun_map_map (F := G1)).
      repeat fequal.
      ext t.
      unfold compose. cbn.
      compose near (dec T t).
      unfold compose. cbn.
      compose near (dec T t) on right.
      rewrite (fun_map_map (F := T)).
      unfold compose.
      repeat fequal.
      now ext [w' b].
    Qed.

  End adapter.

  Section with_monad.

    Context
      `{Categorical.DecoratedTraversableMonad.DecoratedTraversableMonad W T}.

    Theorem kdtm_binddt1_T {A} :
      binddt (G := fun A => A) (η (T := T) ∘ extract) = @id (T A).
    Proof.
      unfold_ops @Binddt_categorical.
      change (map (F := fun A => A) ?f) with f.
      rewrite (dist_unit (F := T)).
      change (?mu ∘ id) with mu.
      rewrite <- fun_map_map.
      do 2 reassociate -> on left.
      rewrite dfun_dec_extract.
      reassociate <- on left.
      rewrite (mon_join_map_ret (T := T)).
      reflexivity.
    Qed.

    Theorem kdtm_binddt0_T : forall
        (G : Type -> Type) `{Map G} `{Pure G} `{Mult G} `{! Applicative G}
        (A B : Type)
        (f : W * A -> G (T B)),
        binddt f ∘ η (T := T) = f ∘ η (T := (W ×)).
    Proof.
      intros.
      unfold_ops @Binddt_categorical.
      reassociate -> on left.
      rewrite (dmon_ret (W := W) (T := T)).
      reassociate <- on left.
      reassociate -> near (η (A := W * A)).
      rewrite (natural (ϕ := @ret T _)).
      unfold_ops @Map_I.
      reassociate <- on left.
      reassociate -> near (η (A := G (T B))).
      rewrite (trvmon_ret (T := T)).
      rewrite (fun_map_map (F := G)).
      rewrite (mon_join_ret (T := T)).
      rewrite (fun_map_id (F := G)).
      reflexivity.
    Qed.

    Section binddt_binddt.

      Context
        (G1 : Type -> Type)
          `{Map G1} `{Pure G1} `{Mult G1} `{! Applicative G1}
          (G2 : Type -> Type)
          `{Map G2} `{Pure G2} `{Mult G2} `{! Applicative G2}
          `(g : W * B -> G2 (T C)) `(f : W * A -> G1 (T B)).

      #[local] Arguments map (F)%function_scope {Map} {A B}%type_scope f%function_scope _.
      #[local] Arguments dist F%function_scope {ApplicativeDist} G%function_scope {H H0 H1} (A)%type_scope _.
      #[local] Arguments dec {E}%type_scope F%function_scope {Decorate} (A)%type_scope _.
      #[local] Arguments join {T}%function_scope {Join} (A)%type_scope _.

      Theorem kdtm_binddt2_T :
        map G1 (binddt (G := G2) g) ∘ binddt (G := G1) f = binddt (G := G1 ∘ G2) (g ⋆7 f).
      Proof.
        unfold binddt at 1 2; unfold Binddt_categorical.
        rewrite <- (fun_map_map (F := G1)).
        do 3 reassociate <-.
        reassociate -> near (map G1 (μ B)).
        rewrite (fun_map_map (F := G1)).
        rewrite dmon_join.
        (* Rearrange right of <<shift>> *)
        reassociate -> near (map T (dec T B)).
        rewrite <- (natural (ϕ := @dec W T _)).
        reassociate <- on left.
        rewrite <- (fun_map_map
                     (F := G1) (map_instance := H5)
                     _ _ _
                     (dec T (T B))
                     (μ (W * B) ∘ map T (shift T) ∘ map (T ○ prod W) (dec T B))).
        reassociate <- on left.
        reassociate -> near (δ T G1 (T B)).
        rewrite <- (dtfun_compat (F := T) (G := G1)).
        reassociate <- on left.
        reassociate -> near (map T f).
        rewrite <- (natural (ϕ := @dec W T _)).
        reassociate <- on left.
        reassociate -> near (dec T A).
        rewrite dfun_dec_dec.
        reassociate <- on left.
        reassociate -> near (map T cojoin).
        change (map (T ○ prod W) f) with (map T (map (prod W) f)).
        rewrite (fun_map_map (F := T)).
        reassociate <- on left.
        reassociate -> near (map T (map (prod W) f ∘ cojoin)).
        rewrite (fun_map_map (F := T)).
        (* Rearrange left of <<shift>> *)
        change (map (T ○ prod W) (dec T B)) with (map T (map (prod W) (dec T B))).
        rewrite (fun_map_map (F := G1)).
        do 2 reassociate <- on left.
        bring (map T g) and (μ (W * B)) together.
        rewrite (natural (ϕ := @join T _)).
        reassociate <- on left.
        bring (δ T G2 (T C)) and (μ (G2 (T C))) together.
        rewrite trvmon_join.
        do 2 reassociate <- on left.
        rewrite (fun_map_map (F := G2)).
        rewrite (mon_join_join (T := T)).
        rewrite <- (fun_map_map (F := G2)).
        reassociate -> near (δ T G2 (T (T C))).
        change (map G2 (map T ?f)) with (map (G2 ∘ T) f).
        unfold_compose_in_compose.
        rewrite (natural (ϕ := @dist T _ G2 _ _ _)).
        change (map (T ○ G2) ?f) with (map T (map G2 f)).
        change (map (T ∘ T) ?g) with (map T (map T g)).
        do 7 reassociate -> on left.
        do 4 rewrite (fun_map_map (F := T)).
        repeat reassociate <- on left.
        rewrite <- (fun_map_map (F := G1)).
        change (map G1 (map T ?f)) with (map (G1 ○ T) f).
        reassociate -> near (δ T G1 (W * T B)).
        rewrite (natural (ϕ := @dist T _ G1 _ _ _)).

        rewrite <- (fun_map_map (F := G1)).
        change (map G1 (map G2 ?f)) with (map (G1 ∘ G2) f).
        reassociate <- on left.
        change (map (T ○ G1) ?f) with (map T (map G1 f)).
        reassociate -> near (map T (σ ∘ map (prod W) f ∘ cojoin)).
        rewrite (fun_map_map (F := T)).
        unfold strength.



        unfold binddt.
        unfold_compose_in_compose.
        rewrite (dist_linear( F:= T) (G1 := G1) (G2 := G2) (T C)).
        unfold kc7.
        unfold binddt.
        repeat fequal.
        ext [w a].
        do 2 (unfold compose; cbn).
        compose near (f (w, a)) on left.
        rewrite (fun_map_map (F := G1)).
        fequal.
        unfold compose; cbn.

      Admitted.

    End binddt_binddt.

    Lemma kdtm_morph_T :
      forall `{ApplicativeMorphism G1 G2 ϕ},
      forall (A B : Type) (f : W * A -> G1 (T B)),
        ϕ (T B) ∘ binddt (G := G1) f = binddt (G := G2) (ϕ (T B) ∘ f).
    Proof.
      introv morph. intros.
      unfold_ops @Binddt_categorical.
      do 3 reassociate <- on left.
      fequal.
      unfold compose. ext t.
      rewrite appmor_natural.
      fequal.
      compose near (map f t).
      rewrite <- (dist_morph (F := T)).
      unfold compose. compose near t on left.
      now rewrite (fun_map_map (F := T)).
    Qed.

    #[export] Instance: Kleisli.DecoratedTraversableMonad.DecoratedTraversableRightPreModule W T T :=
      {|
        kdtm_binddt1 := @kdtm_binddt1_T;
        kdtm_binddt2 := @kdtm_binddt2_T;
        kdtm_morph := @kdtm_morph_T;
      |}.

    #[export] Instance: Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T :=
      {| kdtm_binddt0 := @kdtm_binddt0_T;
      |}.

  End with_monad.

End ToKleisli.
