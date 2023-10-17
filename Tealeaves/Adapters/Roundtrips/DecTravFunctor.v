From Tealeaves Require Export
  Adapters.CategoricalToKleisli.DecTravFunctor
  Adapters.KleisliToCategorical.DecTravFunctor.

Import Product.Notations.
Import Functor.Notations.
Import Kleisli.Monad.Notations.

#[local] Generalizable Variable T.

Import Kleisli.DecoratedFunctor.DerivedInstances.

(** * Categorical ~> Kleisli ~> Categorical *)
(******************************************************************************)
Module Roundtrip1.

  Context
    (E : Type)
    (T : Type -> Type)
    `{mapT : Map T}
    `{distT : ApplicativeDist T}
    `{decorateT : Decorate E T}
    `{! Categorical.DecTravFunctor.DecoratedTraversableFunctor E T}.

  #[local] Instance mapdt' : Mapdt E T := ToKleisli.Mapdt_distdec E T.

  Definition map' : Map T := DerivedInstances.Map_Mapdt E T.
  Definition decorate' : Decorate E T := ToCategorical.Decorate_Mapdt E T.
  Definition dist' : ApplicativeDist T := ToCategorical.Dist_Mapdt E T.

  Goal mapT = map'.
  Proof.
    unfold map'. unfold_ops @DerivedInstances.Map_Mapdt.
    unfold mapdt, mapdt'.
    unfold_ops @ToKleisli.Mapdt_distdec.
    ext A B f.
    rewrite (dist_unit (F := T)).
    rewrite <- (fun_map_map (F := T)).
    reassociate -> on right.
    reassociate -> on right.
    rewrite (dfun_dec_extract (E := E) (F := T)).
    reflexivity.
  Qed.

  Goal distT = dist'.
  Proof.
    unfold dist'. unfold_ops ToCategorical.Dist_Mapdt.
    unfold mapdt, mapdt'.
    unfold_ops @ToKleisli.Mapdt_distdec.
    ext G Hmap Hpure Hmult. ext A.
    reassociate -> on right.
    rewrite (dfun_dec_extract (E := E) (F := T)).
    reflexivity.
  Qed.

  Goal decorateT = decorate'.
  Proof.
    unfold decorate'. unfold_ops @ToCategorical.Decorate_Mapdt.
    unfold mapdt, mapdt'.
    unfold_ops @ToKleisli.Mapdt_distdec.
    ext A.
    rewrite (dist_unit (F := T)).
    now rewrite (fun_map_id (F := T)).
  Qed.

End Roundtrip1.

(** * Kleisli ~> Categorical ~> Kleisli *)
(******************************************************************************)
Module Roundtrip2.

  Context
    (E : Type)
    (T : Type -> Type)
    `{mapdtT : Mapdt E T}
    `{@Kleisli.DecTravFunctor.DecoratedTraversableFunctor E T _}.

  #[local] Instance map' : Map T := DerivedInstances.Map_Mapdt E T.
  #[local] Instance dist' : ApplicativeDist T := ToCategorical.Dist_Mapdt E T.
  #[local] Instance decorate' : Decorate E T := ToCategorical.Decorate_Mapdt E T.

  Definition mapdt' : Mapdt E T := ToKleisli.Mapdt_distdec E T.

  Import DerivedInstances.

  Goal forall G `{Applicative G}, @mapdtT G _ _ _ = @mapdt' G _ _ _.
  Proof.
    intros.
    unfold mapdt'. unfold_ops @ToKleisli.Mapdt_distdec.
    unfold map, map', dist, dist', dec, decorate'.
    ext A B f.
    unfold_ops @ToCategorical.Dist_Mapdt.
    unfold_ops @DerivedInstances.Map_Mapdt.
    unfold_ops @ToCategorical.Decorate_Mapdt.
    change_right (mapdt T G (extract (prod E) (G B)) ∘
                    map T f ∘
                    mapd T id).
    unfold map'.
    rewrite (mapdt_map T G).
    rewrite (mapdt_mapd T G).
    fequal. ext [e a]. reflexivity.
  Qed.

End Roundtrip2.
