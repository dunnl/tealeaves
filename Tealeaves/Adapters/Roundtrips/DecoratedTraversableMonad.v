From Tealeaves Require Export
  Adapters.CategoricalToKleisli.DecoratedTraversableMonad
  Adapters.KleisliToCategorical.DecoratedTraversableMonad.

Import Product.Notations.
Import Kleisli.Monad.Notations.

#[local] Generalizable Variable T W.

(** * Categorical ~> Kleisli ~> Categorical *)
(******************************************************************************)
Module Roundtrip1.

  Context
    `{Monoid W}
    `{mapT: Map T}
    `{distT: ApplicativeDist T}
    `{joinT: Join T}
    `{decorateT: Decorate W T}
    `{Return T}
    `{! Categorical.DecoratedTraversableMonad.DecoratedTraversableMonad W T}.

  #[local] Instance binddt': Binddt W T T :=
    DerivedOperations.Binddt_Categorical W T.

  Definition map': Map T := DerivedOperations.Map_Binddt W T T.
  Definition join': Join T := DerivedOperations.Join_Binddt W T.
  Definition decorate': Decorate W T := DerivedOperations.Decorate_Binddt W T.
  Definition dist': ApplicativeDist T := DerivedOperations.Dist_Binddt W T.

  Goal mapT = map'.
  Proof.
    unfold map'. unfold_ops @DerivedOperations.Map_Binddt.
    unfold binddt, binddt'.
    unfold_ops @DerivedOperations.Binddt_Categorical.
    ext A B f.
    unfold_ops @Map_I.
    rewrite (dist_unit (F := T)).
    change (?f ∘ id) with f.
    do 2 rewrite <- (fun_map_map (F := T)).
    do 2 reassociate <- on right.
    rewrite (mon_join_map_ret (T := T)).
    change (id ∘ ?f) with f.
    reassociate -> on right.
    rewrite (dfun_dec_extract (E := W) (F := T)).
    reflexivity.
  Qed.

  Goal forall G `{Applicative G}, @distT G _ _ _ = @dist' G _ _ _.
  Proof.
    intros.
    unfold dist'. unfold_ops @DerivedOperations.Dist_Binddt.
    unfold binddt, binddt'.
    unfold_ops @DerivedOperations.Binddt_Categorical.
    ext A.
    rewrite <- (fun_map_map (F := T)).
    unfold_compose_in_compose.
    reassociate <- on right.
    reassociate -> near (map (map (ret))).
    change (map (map (ret)))
      with ((map (F := T ○ G) (ret (A := A)))).
    rewrite <- (natural (ϕ := @dist T _ G _ _ _)).
    unfold_ops @Map_compose.
    reassociate <- on right.
    inversion H2.
    rewrite (fun_map_map (F := G)).
    rewrite (mon_join_map_ret (T := T)).
    rewrite (fun_map_id (F := G)).
    reassociate -> on right.
    rewrite (dfun_dec_extract (E := W) (F := T)).
    reflexivity.
  Qed.

  Goal joinT = join'.
  Proof.
    unfold join'. unfold_ops @DerivedOperations.Join_Binddt.
    unfold binddt, binddt'.
    unfold_ops @DerivedOperations.Binddt_Categorical.
    ext A.
    rewrite (dist_unit (F := T)).
    reassociate -> on right.
    rewrite (dfun_dec_extract (E := W) (F := T)).
    reflexivity.
  Qed.

  Goal decorateT = decorate'.
  Proof.
    unfold decorate'. unfold_ops @DerivedOperations.Decorate_Binddt.
    unfold binddt, binddt'.
    unfold_ops @DerivedOperations.Binddt_Categorical @Map_I.
    ext A.
    rewrite (dist_unit (F := T)).
    change (?f ∘ id) with f.
    rewrite (mon_join_map_ret (T := T)).
    reflexivity.
  Qed.

End Roundtrip1.

(** * Kleisli ~> Categorical ~> Kleisli *)
(******************************************************************************)
Module Roundtrip2.

  Section section.

    Context
      `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T}.

    Definition map': Map T :=
      DerivedOperations.Map_Binddt W T T.
    Definition dist': ApplicativeDist T :=
      DerivedOperations.Dist_Binddt W T.
    Definition join': Join T :=
      DerivedOperations.Join_Binddt W T.
    Definition decorate': Decorate W T :=
      DerivedOperations.Decorate_Binddt W T.

    Definition binddt2: Binddt W T T :=
      DerivedOperations.Binddt_Categorical W T
        (H := map') (H0 := decorate') (H2 := join') (H1 := dist').

    #[local] Tactic Notation "binddt_to_bindd" :=
      rewrite <- bindd_to_binddt.
    #[local] Tactic Notation "binddt_to_bindt" :=
      rewrite <- bindt_to_binddt.
    #[local] Tactic Notation "bindd_to_map" :=
      rewrite <- map_to_bindd.

    Import Kleisli.DecoratedTraversableMonad.DerivedOperations.
    Import Kleisli.DecoratedTraversableMonad.DerivedInstances.

    Goal forall G `{Applicative G},
        @binddt W T T _ G _ _ _ = @binddt2 G _ _ _ .
    Proof.
      intros.
      ext A B f.
      unfold binddt2.
      unfold DerivedOperations.Binddt_Categorical.
      unfold map at 2, map', DerivedOperations.Map_Binddt.
      unfold dist, dist', DerivedOperations.Dist_Binddt.
      unfold dec, decorate', DerivedOperations.Decorate_Binddt.
      rewrite <- bindd_to_binddt.
      binddt_to_bindd.
      binddt_to_bindt.
      bindd_to_map.
      reassociate -> on right.
      unfold map'.
      rewrite map_bindd.
      reassociate -> on right.
      unfold_compose_in_compose.
      rewrite (bindt_bindd).
      reassociate <- on right.
      rewrite (bindt_map).
      rewrite (ktm_bindt0).
      unfold join, join'; unfold_ops @DerivedOperations.Join_Binddt.
      unfold compose at 2.
      rewrite (kdtm_binddt2 (G1 := G) (G2 := fun A => A)).
      rewrite (binddt_app_id_r).
      rewrite (kc7_73).
      change (extract (W := (W ×)) (A := T B))
        with (id ∘ extract (W := (W ×)) (A := T B)).
      rewrite (kc3_03).
      rewrite (fun_map_id (F := G)).
      reflexivity.
    Qed.

  End section.
End Roundtrip2.
