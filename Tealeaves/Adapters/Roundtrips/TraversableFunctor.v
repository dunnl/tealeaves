From Tealeaves Require Export
  Classes.Categorical.TraversableFunctor
  Classes.Kleisli.TraversableFunctor
  Adapters.CategoricalToKleisli.TraversableFunctor
  Adapters.KleisliToCategorical.TraversableFunctor.

(** * Categorical ~> Kleisli ~> Categorical *)
(******************************************************************************)
Module traversable_functor_categorical_kleisli_categorical.

  Context
    (T: Type -> Type)
    `{mapT: Map T}
    `{distT: ApplicativeDist T}
    `{! Categorical.TraversableFunctor.TraversableFunctor T}.

  #[local] Instance traverse': Traverse T :=
    DerivedOperations.Traverse_Categorical T.

  Definition map2: Map T :=
    DerivedOperations.Map_Traverse T.
  Definition dist2: ApplicativeDist T :=
    DerivedOperations.Dist_Traverse T.

  Goal mapT = map2.
  Proof.
    unfold map2.
    unfold DerivedOperations.Map_Traverse.
    unfold traverse.
    unfold traverse'.
    unfold DerivedOperations.Traverse_Categorical.
    ext A B f.
    rewrite (dist_unit (F := T)).
    reflexivity.
  Qed.

  Goal distT = dist2.
  Proof.
    unfold dist2.
    unfold DerivedOperations.Dist_Traverse.
    unfold traverse.
    unfold traverse'.
    unfold DerivedOperations.Traverse_Categorical.
    ext G Hmap Hpure Hmult. ext A.
    rewrite (fun_map_id (F := T)).
    reflexivity.
  Qed.

End traversable_functor_categorical_kleisli_categorical.

(** * Kleisli ~> Categorical ~> Kleisli *)
(******************************************************************************)
Module traversable_functor_kleisli_categorical_kleisli.

  Context
    (T: Type -> Type)
    `{traverseT: Traverse T}
    `{@Classes.Kleisli.TraversableFunctor.TraversableFunctor T _}.

  Definition map': Map T :=
    DerivedOperations.Map_Traverse T.

  Definition dist': ApplicativeDist T :=
    DerivedOperations.Dist_Traverse T.

  Definition traverse2: Traverse T :=
    DerivedOperations.Traverse_Categorical T
      (Map_T := map') (Dist_T := dist').

  Goal forall (G: Type -> Type) `{Applicative G},
      @traverseT G _ _ _ = @traverse2 G _ _ _.
  Proof.
    intros.
    unfold traverse2.
    unfold DerivedOperations.Traverse_Categorical.
    unfold dist.
    unfold dist'.
    unfold DerivedOperations.Dist_Traverse.
    unfold map, map', dist, dist'.
    ext A B f.
    unfold DerivedOperations.Map_Traverse.
    change (traverse (T := T) (G := G) (@id (G B))) with
      (map (F := fun A => A) (traverse (T := T) (G := G) (@id (G B)))).
    rewrite (trf_traverse_traverse (T := T) (G1 := fun A => A)).
    rewrite (traverse_app_id_l).
    reflexivity.
  Qed.

End traversable_functor_kleisli_categorical_kleisli.

(** * Coalgebraic ~> Kleisli ~> Coalgebraic (TODO) *)
(******************************************************************************)

(** * Kleisli ~> Coalgebraic ~> Kleisli (TODO) *)
(******************************************************************************)
