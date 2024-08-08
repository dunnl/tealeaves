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
    `{mapT : Map T}
    `{distT : ApplicativeDist T}
    `{joinT : Join T}
    `{decorateT : Decorate W T}
    `{Return T}
    `{! Categorical.DecoratedTraversableMonad.DecoratedTraversableMonad W T}.

  #[local] Instance binddt' : Binddt W T T := ToKleisli.Binddt_categorical W T.

  Definition map' : Map T := Map_Binddt W T T.
  Definition join' : Join T := ToCategorical.Join_Binddt W T.
  Definition decorate' : Decorate W T := ToCategorical.Decorate_Binddt W T.
  Definition dist' : ApplicativeDist T := ToCategorical.Dist_Binddt W T.

  Goal mapT = map'.
  Proof.
    unfold map'. unfold_ops @Map_Binddt.
    unfold binddt, binddt'.
    unfold_ops @ToKleisli.Binddt_categorical.
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
    unfold dist'. unfold_ops @ToCategorical.Dist_Binddt.
    unfold binddt, binddt'.
    unfold_ops @ToKleisli.Binddt_categorical.
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
    inversion H5.
    rewrite (fun_map_map (F := G)).
    rewrite (mon_join_map_ret (T := T)).
    rewrite (fun_map_id (F := G)).
    reassociate -> on right.
    rewrite (dfun_dec_extract (E := W) (F := T)).
    reflexivity.
  Qed.

  Goal joinT = join'.
  Proof.
    unfold join'. unfold_ops @ToCategorical.Join_Binddt.
    unfold binddt, binddt'.
    unfold_ops @ToKleisli.Binddt_categorical.
    ext A.
    rewrite (dist_unit (F := T)).
    reassociate -> on right.
    rewrite (dfun_dec_extract (E := W) (F := T)).
    reflexivity.
  Qed.

  Goal decorateT = decorate'.
  Proof.
    unfold decorate'. unfold_ops @ToCategorical.Decorate_Binddt.
    unfold binddt, binddt'.
    unfold_ops @ToKleisli.Binddt_categorical @Map_I.
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

  Context
    `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonadFull W T}.

  #[local] Instance map' : Map T := Map_Binddt W T T.
  #[local] Instance dist' : ApplicativeDist T := ToCategorical.Dist_Binddt W T.
  #[local] Instance join' : Join T := ToCategorical.Join_Binddt W T.
  #[local] Instance decorate' : Decorate W T := ToCategorical.Decorate_Binddt W T.

  Definition binddt' : Binddt W T T := ToKleisli.Binddt_categorical W T.

  #[local] Tactic Notation "binddt_to_bindd" :=
    rewrite <- bindd_to_binddt.
  #[local] Tactic Notation "binddt_to_bindt" :=
    rewrite <- bindt_to_binddt.
  #[local] Tactic Notation "bindd_to_map" :=
    rewrite <- map_to_bindd.

  Goal forall G `{Applicative G}, @binddt W T T Binddt_inst G _ _ _ = @binddt' G _ _ _ .
  Proof.
    intros.
    unfold binddt'. unfold_ops @ToKleisli.Binddt_categorical.
    ext A B f.
    unfold map at 2, map', Map_Binddt.
    unfold dist, dist', ToCategorical.Dist_Binddt.
    unfold dec, decorate', ToCategorical.Decorate_Binddt.
    binddt_to_bindd.
    binddt_to_bindd.
    binddt_to_bindt.
    bindd_to_map.
    unfold map'.
    reassociate -> on right.
    rewrite (map_bindd).
    reassociate -> on right.
    unfold_compose_in_compose.
    rewrite (bindt_bindd).
    reassociate <- on right.
    rewrite (bindt_map).
    rewrite (ktm_bindt0).
    unfold join, join'; unfold_ops @ToCategorical.Join_Binddt.
    unfold compose at 2.
    rewrite (kdtm_binddt2 (G1 := G) (G2 := fun A => A)).
    rewrite (binddt_app_r).
    rewrite (kc7_76).
    change (extract (W := (W ×)) (A := T B))
      with (id ∘ extract (W := (W ×)) (A := T B)).
    rewrite (kc6_06).
    inversion H3.
    rewrite (fun_map_id (F := G)).
    reflexivity.
  Qed.

End Roundtrip2.
