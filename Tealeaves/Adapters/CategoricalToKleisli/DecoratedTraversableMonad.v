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

#[local] Generalizable Variables G ϕ.

(** * Kleisli presentation of D-T monads *)
(******************************************************************************)
Module ToKleisli.

    (* Define <<Binddt>> from dist/dec/join *)
    #[export] Instance Binddt_ddj
      (W : Type) (T : Type -> Type) `{Map T}
      `{Decorate W T} `{ApplicativeDist T} `{Join T} : Binddt W T T :=
      fun G `{Map G} `{Pure G} `{Mult G} A B
        (f : W * A -> G (T B)) =>
        map (F := G) join ∘ dist T G ∘ map f ∘ dec T.

  #[local] Tactic Notation "bring" constr(x) "and" constr(y) "together" :=
    change (?f ∘ x ∘ y ∘ ?g) with (f ∘ (x ∘ y) ∘ g).

  Section adapter.

    Context
      (W : Type)
      (T : Type -> Type)
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
      unfold_ops @Binddt_ddj.
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
      (W : Type)
      (T : Type -> Type)
      `{Categorical.DecoratedTraversableMonad.DecoratedTraversableMonad W T}.

    (* for [kdtm_binddt1_T] *)
    Import CategoricalToKleisli.DecoratedMonad.ToKleisli.

    Theorem kdtm_binddt1_T {A} : binddt T (fun A => A) (η (T := T) ∘ extract) = @id (T A).
    Proof.
      introv. unfold_ops @Binddt_ddj.
      change (map (fun A => A) ?f) with f.
      rewrite (dist_unit (F := T)).
      change_left (bindd (B := A) (η ∘ extract)).
      ext t. now rewrite (kmond_bindd1 (T := T)).
    Qed.

    Theorem kdtm_binddt0_T : forall
        (G : Type -> Type) `{Map G} `{Pure G} `{Mult G} `{! Applicative G}
        (A B : Type)
        (f : W * A -> G (T B)),
        binddt T G f ∘ η (T := T) = f ∘ η (T := (W ×)).
    Proof.
      intros.
      unfold_ops @Binddt_ddj.
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
        (G1 G2 : Type -> Type) `{Map G1} `{Pure G1} `{Mult G1} `{! Applicative G1}
          `{Map G2} `{Pure G2} `{Mult G2} `{! Applicative G2}
        {A B C : Type}
        (g : W * B -> G2 (T C)) (f : W * A -> G1 (T B)).

      Existing Instance dtmon_decorated.
      Existing Instance dmon_functor.
      Existing Instance dfun_dec_natural | 1.

      Lemma binddt_binddt1 :
        (map (F := G1) (dec T ∘ μ (T := T)) ∘ δ T G1 : T (G1 (T B)) -> G1 (T (W * B)))
        = map (F := G1) (map (F := T) (μ (T := prod W)) ∘ μ (T := T) ∘ map (F := T) (σ (F := T) ∘ map (F := prod W) (dec T)))
            ∘ δ T G1 ∘ map (F := T) (σ (F := G1)) ∘ dec T.
      Proof.
        (* LHS *)
        rewrite (dmon_join (W := W) (T := T)).
        unfold shift.
        (* RHS *)
        change (?f ∘ δ T G1 ∘ map σ ∘ dec T)
          with (f ∘ (δ T G1 ∘ map σ ∘ dec T)).
        rewrite (dtfun_compat (E := W) (F := T) (G := G1)).
        reassociate <- on right.
        (* RHS *)
        rewrite (fun_map_map (F := G1)).
        rewrite (natural (ϕ := @join T _)).
        rewrite <- (fun_map_map (F := T) _ _ _ _ σ).
        reassociate <- on right.
        change (map (F := T) (map (F := (W ×)) (dec T) (A := ?A)))
          with (map (F := T ∘ (W ×)) (dec T) (A := A)).
        reassociate -> near (dec T (A := T B)).
        #[local] Set Keyed Unification.
        (* TODO Hacky due to redundant Map_prod vs Map_Env *)
        change (Map_reader) with (Map_prod) in *.
        rewrite (natural (F := T) (G := T ∘ prod W) (ϕ := @dec W T _)).
        do 2 reassociate <-.
        reassociate -> near (map (F := T) (σ (F := T))).
        rewrite (fun_map_map (F := T)).
        now rewrite incr_spec.
        #[local] Unset Keyed Unification.
      Qed.

      (* Note that we *cannot* immediately cancel out the right-most two <<dec T>> sub-expressions *)
      Lemma binddt_binddt2 :
        map (F := G1) (map (F := T) g ∘ dec T ∘ μ (T := T)) ∘ δ T G1 ∘ map (F := T) f ∘ dec T =
          map (F := G1) (μ (T := T) ∘
                           map (F := T) (map (F := T) (g ∘ μ (T := prod W)) ∘
                                           σ (F := T) ∘ map (F := (W ×)) (dec T))) ∘ δ T G1
            ∘ map (F := T) (σ (F := G1) ∘ cobind f) ∘ dec T.
      Proof.
        rewrite <- (fun_map_map (F := T) _ _ _ (cobind f)).
        do 4 reassociate -> on right.
        rewrite (cobind_dec T f).
        do 5 reassociate <- on right. fequal. fequal.
        reassociate -> near (map (dec T)).
        rewrite <- (fun_map_map (F := T)).
        change (map (map (g ∘ μ))) with (map (F := T ∘ T) (g ∘ μ)).
        reassociate <- on right.
        rewrite <- (natural (ϕ := @join T _) (g ∘ μ)).
        change (map g ∘ dec T ∘ μ) with (map g ∘ (dec T ∘ μ)).
        rewrite <- (fun_map_map (F := G1)).
        rewrite <- (fun_map_map (F := T)).
        change ((map (F := T) g ∘ map (F := T) (μ (T := prod W)) ∘ μ (T := T)
                   ∘ map (F := T) (σ (F := T) ∘ map (F := prod W) (dec T))))
          with ((map (F := T) g ∘ (map (F := T) (μ (T := prod W)) ∘ μ (T := T)
                               ∘ map (F := T) (σ (F := T) ∘ map (F := prod W) (dec T))))).
        rewrite <- (fun_map_map (F := G1) _ _ _ _ (map g)).
        reassociate -> on left.
        do 4 reassociate -> on right.
        fequal. do 3 reassociate <- on right.
        apply binddt_binddt1.
      Qed.

      Theorem kdtm_binddt2_T :
        map (F := G1) (binddt T G2 g) ∘ binddt T G1 f = binddt T (G1 ∘ G2) (g ⋆7 f).
      Proof.
        unfold binddt at 1 2 3; unfold Binddt_ddj at 1 2 3.
        repeat reassociate <-.
        rewrite (dist_linear (F := T)). reassociate <- on right.
        #[local] Set Keyed Unification.
        rewrite 2(fun_map_map (F := G1)).
        #[local] Unset Keyed Unification.
        rewrite (equiv' W T G1 G2 g f).
        unfold kcompose_dtm_alt.
        reassociate -> near (cobind (W := (W ×)) f).
        rewrite <- (fun_map_map (F := T)).
        change (map (map ?f)) with (map (F := T ∘ G1) f).
        reassociate <- on right.
        change (map (F := G1) (map (F := G2) (μ (T := T)) ∘ δ T G2) ∘ ?dist ∘ ?op)
          with (map (F := G1) (map (F := G2) (μ (T := T)) ∘ δ T G2) ∘ (dist ∘ op)).
        unfold_compose_in_compose.
        rewrite <- (natural (ϕ := @dist T _ G1 _ _ _)).
        change (map (F := G1 ○ T) ?f) with (map (F := G1) (map (F := T) f)).
        reassociate <-.
        #[local] Set Keyed Unification.
        rewrite (fun_map_map (F := G1)).
        change (map (F := T) (map (F := G2) (μ (T := T)) ∘ δ T G2 ∘ map (F := T) (g ∘ μ (prod W)) ∘ σ (F := T) ∘ map (prod W) (dec T)))
          with (map (F := T) (map (F := G2) (μ (T := T)) ∘ (δ T G2 ∘ map (F := T) (g ∘ μ (prod W)) ∘ σ (F := T) ∘ map (prod W) (dec T)))).
        rewrite <- (fun_map_map (F := T)).
        reassociate <- on right.
        #[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
      Admitted.
      (*
        reassociate -> near (map (F := T ∘ G2) (μ (T := (prod W)))).
        unfold_compose_in_compose.
        rewrite <- (natural (ϕ := @dist T _ G2 _ _ _)).
        reassociate <- on right.
        #[local] Set Keyed Unification.
        rewrite (fun_map_map (F := G2)).
        rewrite <- (mon_join_join (T := T)).
        #[local] Unset Keyed Unification.
        rewrite <- (fun_map_map (F := G2)).
        reassociate -> near (δ T G2).
        change (δ T G2 ∘ map (F := T) (g ∘ μ (prod W)) ∘ σ T ∘ map (prod W) (dec T))
          with (δ T G2 ∘ (map (F := T) (g ∘ μ (prod W)) ∘ σ T ∘ map (prod W) (dec T))).
        rewrite <- (fun_map_map (F := T)).
        do 2 reassociate <- on right.
        change (map (F := G2) (μ T) ∘ map (F := G2) (μ T) ∘ δ T G2 ∘ map (F := T) (δ T G2) (A := ?A))
          with (map (F := G2) (μ T) ∘ (map (F := G2) (μ T) ∘ δ T G2 ∘ map (F := T) (δ T G2) (A := A))).
        (*
        change (map G2 (μ T) ∘ δ T G2 ∘ map T (δ T G2) (A := T (G2 ?A)))
          with (map G2 (μ T) ∘ δ (T ∘ T) G2 (A := A)).
         *)
        rewrite <- (trvmon_join (T := T)).
        reassociate <- on right.
        change_left (map G1 (map G2 (μ T) ∘ δ T G2 ∘ (map T g ∘ dec T ∘ μ T)) ∘ δ T G1 ∘ map T f ∘ dec T).
        change_right (map G1 (map G2 (μ T) ∘ δ T G2 ∘
                                 (μ T ∘ map T (map T (g ∘ μ (prod W)) ∘ σ T ∘ map (prod W) (dec T))))
                        ∘ δ T G1
                        ∘ map T (σ G1 ∘ cobind (prod W) f) ∘ dec T).
        (* cancel out the common sub-expressions and apply a lemma to the remaining. *)
        rewrite <- (fun_map_map (F := G1)).
        rewrite <- (fun_map_map (F := G1) _ _ _ _ (map G2 (μ T) ∘ δ T G2)).
        do 3 reassociate -> on left.
        do 3 reassociate -> on right.
        fequal. repeat reassociate <-.
        apply binddt_binddt2.
      Qed.
       *)

    End binddt_binddt.

    Lemma kdtm_morph_T :
      forall `{ApplicativeMorphism G1 G2 ϕ},
        forall (A B : Type) (f : W * A -> G1 (T B)),
          ϕ (T B) ∘ binddt T G1 f = binddt T G2 (ϕ (T B) ∘ f).
    Proof.
      introv morph. intros.
      unfold_ops @Binddt_ddj.
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

    #[export] Instance: Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T :=
      {| kdtm_binddt0 := @kdtm_binddt0_T;
        kdtm_binddt1 := @kdtm_binddt1_T;
        kdtm_binddt2 := @kdtm_binddt2_T;
        kdtm_morph := @kdtm_morph_T;
      |}.

  End with_monad.

End ToKleisli.
