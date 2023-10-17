From Tealeaves Require Export
  Classes.Categorical.TraversableMonad
  Classes.Kleisli.TraversableMonad
  Adapters.CategoricalToKleisli.TraversableMonad
  Adapters.KleisliToCategorical.TraversableMonad.

#[local] Generalizable Variables T.

Import TraversableMonad.Notations.

(** * Categorical ~> Kleisli ~> Categorical *)
(******************************************************************************)
Module Roundtrip1.

  Context
    `{mapT : Map T}
    `{distT : ApplicativeDist T}
    `{joinT : Join T}
    `{Return T}
    `{! Categorical.TraversableMonad.TraversableMonad T}.

  #[local] Instance bindt' : Bindt T T := ToKleisli.Bindt_distjoin T.

  Definition map'  : Map T := DerivedInstances.Map_Bindt T.
  Definition dist' : ApplicativeDist T := Dist_Bindt T.
  Definition join' : Join T := Join_Bindt T.

  Goal mapT = map'.
  Proof.
    unfold map'. unfold_ops @DerivedInstances.Map_Bindt.
    unfold bindt, bindt'.
    unfold_ops @ToKleisli.Bindt_distjoin.
    ext A B f.
    unfold_ops @Map_I.
    rewrite (dist_unit (F := T)).
    change (?g ∘ id) with g.
    rewrite <- (fun_map_map (F := T)).
    reassociate <- on right.
    now rewrite (mon_join_map_ret (T := T)).
  Qed.

  Goal forall G `{Applicative G}, @distT G _ _ _ = @dist' _ _ _ _.
  Proof.
    intros.
    unfold dist'. unfold_ops Dist_Bindt.
    unfold bindt, bindt'.
    unfold_ops @ToKleisli.Bindt_distjoin.
    ext A.
    change (map T (map G (ret T A))) with (map (T ∘ G) (ret T A)).
    reassociate -> on right.
    unfold_compose_in_compose.
    rewrite <- (natural (Natural := dist_natural (F := T)) (ϕ := @dist T _ G _ _ _)).
    reassociate <- on right.
    unfold_ops @Map_compose.
    rewrite (fun_map_map (F := G)).
    rewrite (mon_join_map_ret (T := T)).
    rewrite (fun_map_id (F := G)).
    reflexivity.
  Qed.

  Goal joinT = join'.
  Proof.
    unfold join'. unfold_ops @Join_Bindt.
    unfold bindt, bindt'.
    unfold_ops @ToKleisli.Bindt_distjoin.
    ext A. rewrite (fun_map_id (F := T)).
    unfold_ops @Map_I.
    rewrite (dist_unit (F := T)).
    reflexivity.
  Qed.

End Roundtrip1.

(** * Kleisli ~> Categorical ~> Kleisli *)
(******************************************************************************)
Module Roundtrip2.

  Context
    `{bindtT : Bindt T T}
    `{Return T}
    `{! Kleisli.TraversableMonad.TraversableMonad T}.

  #[local] Instance map'  : Map T  := DerivedInstances.Map_Bindt T.
  #[local] Instance dist' : ApplicativeDist T := Dist_Bindt T.
  #[local] Instance join' : Join T := Join_Bindt T.

  Definition bindt' : Bindt T T := ToKleisli.Bindt_distjoin T.

  Goal forall A B G `{Applicative G}, @bindtT G _ _ _ A B = @bindt' G _ _ _ A B.
  Proof.
    intros. ext f.
    unfold bindt'. unfold_ops @ToKleisli.Bindt_distjoin.
    unfold join, join', dist, dist', map at 2, map'.
    unfold_ops @Join_Bindt.
    unfold_ops @Dist_Bindt.
    unfold_ops @DerivedInstances.Map_Bindt.
    change (?g ∘ id) with g.
    reassociate -> on right.
    change (bindt G _ _ (map G (ret T (T B))))
      with (map (fun A => A) (bindt G _ _ (map G (ret T (T B))))).
    unfold_compose_in_compose.
    rewrite (ktm_bindt2 (fun A => A) G).

    unfold kc3.
    unfold_ops @Map_I.
    reassociate <- on right.
    rewrite (ktm_bindt0 (T := T) G).
    rewrite (bindt_app_l T G).
    rewrite (ktm_bindt2 (T := T) G (fun A => A)).
    rewrite (bindt_app_r T G).

    unfold bindt.
    fequal.
    unfold kc3.
    reassociate <-.
    rewrite (fun_map_map (F := G)).
    rewrite (ktm_bindt0 (T := T) (fun A => A)).
    rewrite (fun_map_id (F := G)).
    reflexivity.
  Qed.

End Roundtrip2.
