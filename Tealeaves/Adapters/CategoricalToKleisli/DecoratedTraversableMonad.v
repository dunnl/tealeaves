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
      rewrite (fun_map_map (F := G1) (Functor := app_functor)).
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
      rewrite (fun_map_map (F := G) (Functor := app_functor)).
      rewrite (mon_join_ret (T := T)).
      rewrite (fun_map_id (F := G) (Functor := app_functor)).
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
        rewrite (equiv' _ _ g f).
        unfold kcompose_dtm_alt.
        (* ********** *)
        unfold binddt at 1 2; unfold Binddt_categorical.
        assert (Functor G1) by now inversion Applicative0.
        assert (Functor G2) by now inversion Applicative1.
        (* Normalize associativity *)
        do 3 reassociate <-.
        (* Bring together <<map G1 (dec T B)>> and <<map G1 (μ B)>> *)
        rewrite <- (fun_map_map (F := G1) (Functor := app_functor)).
        bring (map G1 (dec T B)) and (map G1 (μ B)) together.
        rewrite (fun_map_map (F := G1) (Functor := app_functor)).
        rewrite dmon_join.
        (* Move <<dec T (T (W * B))>> towards <<dec T A>> *)
        reassociate -> near (map T (dec T B)).
        rewrite <- (natural (ϕ := @dec W T _)).
        reassociate <- on left.
        rewrite <- (fun_map_map
                     (F := G1)
                     _ _ _
                     (dec T (T B))).
        reassociate <- on left.
        bring (map G1 (dec T (T B))) and (δ T G1 (T B)) together.
        rewrite <- (dtfun_compat (F := T) (G := G1)).
        do 2 reassociate <- on left.
        bring (dec T (G1 (T B))) and (map T f) together.
        rewrite <- (natural (ϕ := @dec W T _)).
        change (map (T ○ prod W) f) with (map (T ∘ prod W) f).
        reassociate <- on left.
        reassociate -> near (dec T A).
        (* Change decorate-then-decorate into decorate-then-duplicate *)
        rewrite dfun_dec_dec.
        reassociate <- on left.
        (* Now move <<μ B>> towards <<μ C>> *)
        unfold shift; rewrite incr_spec.
        change (μ (W * B) ∘ map T (map T (μ B) ∘ σ) ∘ map (T ○ prod W) (dec T B)) with
          (μ (W * B) ∘ (map T (map T (μ B) ∘ σ) ∘ map (T ○ prod W) (dec T B))).
        rewrite <- (fun_map_map (F := G1) (Functor := app_functor) _ _ _ _ (μ (W * B))).
        reassociate <- on left.
        rewrite (fun_map_map (F := G1) _ _ _ (μ (W * B))).
        reassociate -> near (μ (W * B)).
        rewrite (natural (ϕ := join)).
        reassociate <- on left.
        bring (δ T G2 (T C)) and (μ (G2 (T C))) together.
        rewrite trvmon_join.
        do 2 reassociate <- on left.
        rewrite (fun_map_map (F := G2)).
        (* Change map-join-then-join into join-then-join *)
        rewrite (mon_join_join (T := T)).
        (* Now rearrange to match RHS *)
        rewrite <- (fun_map_map (F := G2)).
        change (map G2 (μ C) ∘ map G2 (map T (μ C)) ∘ δ T G2 (T (T C)) ∘ map T (δ T G2 (T C)) ∘ map (T ∘ T) g)
          with (map G2 (μ C) ∘ (map G2 (map T (μ C)) ∘ δ T G2 (T (T C)) ∘ map T (δ T G2 (T C)) ∘ map (T ∘ T) g)).
        rewrite <- (fun_map_map (F := G1)).
        change (map G1 (map G2 ?f)) with (map (G1 ∘ G2) f).
        change (map G2 (map T ?mu)) with (map (G2 ∘ T) mu).
        rewrite (natural (ϕ := dist T G2)).
        change (map (T ○ G2) ?f) with (map T (map G2 f)).
        reassociate -> near (map T (δ T G2 (T C))).
        rewrite (fun_map_map (F := T)).
        change (map (T ○ prod W) ?f) with (map T (map (W ×) f)).
        rewrite (fun_map_map (F := T)).
        reassociate -> near (δ T G1 (W * T B)).
        change (map G1 (map T ?f)) with (map (G1 ○ T) f).
        rewrite (natural (ϕ := dist T G1) (A := (W * T B)) (B := (T (W * B)))).
        reassociate <- on left.
        change (map (T ∘ T) ?g) with (map T (map T g)).
        reassociate -> near (map T (map T g)).
        rewrite (fun_map_map (F := T)).
        rewrite <- (fun_map_map (F := G1)).
        reassociate <- on left.
        change (map G1 (map T ?f)) with (map (G1 ○ T) f).
        reassociate -> near (δ T G1 (T (W * B))).
        rewrite (natural (ϕ := δ T G1)).
        reassociate <- on left.
        reassociate -> near (map (T ○ G1) (map T (μ B) ∘ σ ∘ map (prod W) (dec T B))).
        rewrite (fun_map_map (F := T ○ G1)).
        change (map (T ∘ prod W) f) with (map T (map (prod W) f)).
        change (map (T ○ G1) ?f) with (map T (map G1 f)).
        reassociate -> near (map T cojoin).
        rewrite (fun_map_map (F := T)).
        reassociate -> near (map T (map (prod W) f ∘ cojoin)).
        rewrite (fun_map_map (F := T)).
        reassociate -> near (map T (σ ∘ (map (prod W) f ∘ cojoin))).
        rewrite (fun_map_map (F := T)).
        (* ********** *)
        unfold binddt, kc7, binddt.
        rewrite dist_linear.
        do 4 reassociate <- on left.
        reassociate -> near (map T (μ B)).
        rewrite (fun_map_map (F := T)).
        replace (cobind f) with (map (prod W) f ∘ cojoin).
        reflexivity.
        ext [w a].
        reflexivity.
      Qed.

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
