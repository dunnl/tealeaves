From Tealeaves Require Export
  Adapters.CategoricalToKleisli.DecoratedFunctor
  Adapters.KleisliToCategorical.DecoratedFunctor.

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
    `{decT : Decorate E T}
    `{! Categorical.DecoratedFunctor.DecoratedFunctor E T}.

  #[local] Instance mapd' : Mapd E T := ToKleisli.Mapd_dec E T.

  Definition map' : Map T := Map_Mapd E T.
  Definition dec' : Decorate E T := Decorate_Mapd E T.

  Goal mapT = map'.
  Proof.
    unfold map'. unfold_ops @Map_Mapd.
    unfold mapd, mapd'.
    unfold_ops @ToKleisli.Mapd_dec.
    ext A B f.
    rewrite <- (fun_map_map (F := T)).
    reassociate ->.
    rewrite (dfun_dec_extract (E := E) (F := T)).
    reflexivity.
  Qed.

  Goal decT = dec'.
  Proof.
    unfold dec'. unfold_ops @Decorate_Mapd.
    unfold mapd, mapd'.
    unfold_ops @ToKleisli.Mapd_dec.
    ext A.
    rewrite (fun_map_id (F := T)).
    reflexivity.
  Qed.

End Roundtrip1.

(** * Kleisli ~> Categorical ~> Kleisli *)
(******************************************************************************)
Module Roundtrip2.

  Context
    (E : Type)
    (T : Type -> Type)
    `{mapdT : Mapd E T}
    `{! Kleisli.DecoratedFunctor.DecoratedFunctor E T}.

  #[local] Instance map' : Map T := Map_Mapd E T.
  #[local] Instance dec' : Decorate E T := Decorate_Mapd E T.

  Definition mapd' : Mapd E T := ToKleisli.Mapd_dec E T.

  Goal mapdT = mapd'.
  Proof.
    unfold mapd'. unfold_ops @ToKleisli.Mapd_dec.
    unfold map, map', dec, dec'.
    unfold_ops @Map_Mapd.
    unfold_ops @Decorate_Mapd.
    ext A B f.
    unfold_compose_in_compose.
    rewrite (dfun_mapd2 (E := E) (T := T)).
    rewrite DerivedInstances.kc4_04.
    reflexivity.
  Qed.

End Roundtrip2.
