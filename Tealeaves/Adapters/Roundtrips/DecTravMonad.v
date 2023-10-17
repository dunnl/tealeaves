From Tealeaves Require Export
  Adapters.CategoricalToKleisli.DecTravMonad
  Adapters.KleisliToCategorical.DecTravMonad.

Import Product.Notations.
Import Kleisli.Monad.Notations.

#[local] Generalizable Variable T W.

Import Kleisli.DecTravMonad.DerivedInstances.
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
    `{! Categorical.DecTravMonad.DecoratedTraversableMonad W T}.

  #[local] Instance binddt' : Binddt W T T := ToKleisli.Binddt_ddj W T.

  Definition map' : Map T := DerivedInstances.Map_Binddt W T.
  Definition join' : Join T := ToCategorical.Join_Binddt W T.
  Definition decorate' : Decorate W T := ToCategorical.Decorate_Binddt W T.
  Definition dist' : ApplicativeDist T := ToCategorical.Dist_Binddt W T.

  Goal mapT = map'.
  Proof.
    unfold map'. unfold_ops @DerivedInstances.Map_Binddt.
    unfold binddt, binddt'.
    unfold_ops @ToKleisli.Binddt_ddj.
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
    unfold_ops @ToKleisli.Binddt_ddj.
    ext A.
    rewrite <- (fun_map_map (F := T)).
    unfold_compose_in_compose.
    reassociate <- on right.
    reassociate -> near (map T (map G (ret T A))).
    change (map T (map G (ret T A)))
      with ((map (T ○ G) (ret T A))).
    rewrite <- (natural (ϕ := @dist T _ G _ _ _)).
    unfold_ops @Map_compose.
    reassociate <- on right.
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
    unfold_ops @ToKleisli.Binddt_ddj.
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
    unfold_ops @ToKleisli.Binddt_ddj @Map_I.
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
    `{binddtT : Binddt W T T}
    `{Monoid W}
    `{Return T}
    `{! Kleisli.DecTravMonad.DecTravMonad W T}.

  #[local] Instance map' : Map T := DerivedInstances.Map_Binddt W T.
  #[local] Instance dist' : ApplicativeDist T := ToCategorical.Dist_Binddt W T.
  #[local] Instance join' : Join T := ToCategorical.Join_Binddt W T.
  #[local] Instance decorate' : Decorate W T := ToCategorical.Decorate_Binddt W T.

  Definition binddt' : Binddt W T T := ToKleisli.Binddt_ddj W T.

    #[local] Tactic Notation "binddt_to_bindd" :=
    change (binddt T (fun A0 : Type => A0) ?f) with (bindd T (U := T) f).
    #[local] Tactic Notation "binddt_to_bindt" :=
      change (binddt T ?G (?f ∘ extract (prod W) _)) with (bindt G _ _ f).
    #[local] Tactic Notation "bindd_to_map" :=
      change (bindd T (ret T _ ∘ ?f ∘ extract (prod W) _)) with (map T f).

  Goal forall G `{Applicative G}, @binddtT G _ _ _ = @binddt' G _ _ _ .
  Proof.
    intros.
    unfold binddt'. unfold_ops @ToKleisli.Binddt_ddj.
    ext A B f.
    unfold map at 2, map', Map_Binddt.
    unfold dist, dist', ToCategorical.Dist_Binddt.
    unfold dec, decorate', ToCategorical.Decorate_Binddt.
    binddt_to_bindd.
    binddt_to_bindt.
    bindd_to_map.
    unfold map'.
    reassociate -> on right.
    rewrite (DerivedInstances.map_bindd W T).
    reassociate -> on right.
    unfold_compose_in_compose.
    rewrite (DerivedInstances.bindt_bindd W T G).
    reassociate <- on right.
    rewrite (DecTravMonad.DerivedInstances.bindt_map W T G).
    rewrite (ktm_bindt0 G).
    unfold join, join'; unfold_ops @ToCategorical.Join_Binddt.
    rewrite (kdtm_binddt2 W T G (fun A => A)).
    change_left (binddt T G f).
    rewrite (binddt_app_r T G).
    rewrite (kc7_76 W T).
    change (extract (W ×) (T B)) with (id ∘ extract (W ×) (T B)).
    rewrite (DecTravFunctor.DerivedInstances.kc6_06 G).
    rewrite (fun_map_id (F := G)).
    reflexivity.
  Qed.

End Roundtrip2.
