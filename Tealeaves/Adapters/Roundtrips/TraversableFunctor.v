From Tealeaves Require Export
  Classes.Categorical.TraversableFunctor
  Classes.Kleisli.TraversableFunctor
  Adapters.CategoricalToKleisli.TraversableFunctor
  Adapters.KleisliToCategorical.TraversableFunctor.

(** * Categorical ~> Kleisli ~> Categorical *)
(******************************************************************************)
Module Roundtrip1.

  Context
    (T : Type -> Type)
    `{mapT : Map T}
    `{distT : ApplicativeDist T}
    `{! Categorical.TraversableFunctor.TraversableFunctor T}.

  #[local] Instance traverse' : Traverse T := ToKleisli.Traverse_dist T.

  Definition map' : Map T := DerivedInstances.Map_Traverse T.
  Definition dist' : ApplicativeDist T := ToCategorical.Dist_Traverse T.

  Goal mapT = map'.
  Proof.
    unfold map'. unfold_ops @Map_Traverse.
    unfold traverse, traverse'.
    unfold_ops @ToKleisli.Traverse_dist.
    ext A B f.
    rewrite (dist_unit (F := T)).
    reflexivity.
  Qed.

  Goal distT = dist'.
  Proof.
    unfold dist'. unfold_ops @ToCategorical.Dist_Traverse.
    unfold traverse, traverse'.
    unfold_ops @ToKleisli.Traverse_dist.
    ext G Hmap Hpure Hmult. ext A.
    rewrite (fun_map_id (F := T)).
    reflexivity.
  Qed.

End Roundtrip1.

(** * Kleisli ~> Categorical ~> Kleisli *)
(******************************************************************************)
Module Roundtrip2.

  Context
    (T : Type -> Type)
    `{traverseT : Traverse T}
    `{@Classes.Kleisli.TraversableFunctor.TraversableFunctor T _}.

  #[local] Instance map' : Map T := Map_Traverse T.
  #[local] Instance dist' : ApplicativeDist T := ToCategorical.Dist_Traverse T.

  Definition traverse' : Traverse T := ToKleisli.Traverse_dist T.

  Goal forall G `{Applicative G}, @traverseT G _ _ _ = @traverse' G _ _ _.
  Proof.
    intros.
    unfold traverse'. unfold_ops @ToKleisli.Traverse_dist.
    unfold map, map', dist, dist'.
    ext A B f.
    unfold_ops @ToCategorical.Dist_Traverse.
    unfold_ops @Map_Traverse.
    change (traverse T G (@id (G B))) with (map (fun A => A) (traverse T G (@id (G B)))).
    rewrite (trf_traverse_traverse (T := T) (fun A => A) G);
      try typeclasses eauto.
    rewrite (traverse_app_l T G).
    reflexivity.
  Qed.

End Roundtrip2.
