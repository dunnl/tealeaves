From Tealeaves Require Export
  Adapters.CategoricalToKleisli.DecoratedTraversableFunctor
  Adapters.KleisliToCategorical.DecoratedTraversableFunctor.

Import Product.Notations.
Import Functor.Notations.
Import Kleisli.DecoratedTraversableFunctor.Notations.

#[local] Generalizable Variable T.

(** * Categorical ~> Kleisli ~> Categorical *)
(**********************************************************************)
Module Roundtrip1.

  Context
    (E: Type)
    (T: Type -> Type)
    `{mapT: Map T}
    `{distT: ApplicativeDist T}
    `{decorateT: Decorate E T}
    `{! Categorical.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}.

  #[local] Instance mapdt': Mapdt E T :=
    DerivedOperations.Mapdt_Categorical E T.

  Definition map2: Map T :=
    DerivedOperations.Map_Mapdt.
  Definition decorate2: Decorate E T :=
    DerivedOperations.Decorate_Mapdt E T.
  Definition dist2: ApplicativeDist T :=
    DerivedOperations.Dist_Mapdt E T.

  Goal mapT = map2.
  Proof.
    unfold map2.
    unfold DerivedOperations.Map_Mapdt.
    unfold mapdt.
    unfold mapdt'.
    unfold DerivedOperations.Mapdt_Categorical.
    ext A B f.
    rewrite (dist_unit (F := T)).
    rewrite <- (fun_map_map (F := T)).
    reassociate -> on right.
    reassociate -> on right.
    rewrite (dfun_dec_extract (E := E) (F := T)).
    reflexivity.
  Qed.

  Goal distT = dist2.
  Proof.
    ext G Hmap Hpure Hmult A.
    unfold dist2.
    unfold DerivedOperations.Dist_Mapdt.
    unfold mapdt.
    unfold mapdt'.
    unfold DerivedOperations.Mapdt_Categorical.
    reassociate -> on right.
    rewrite (dfun_dec_extract (E := E) (F := T)).
    reflexivity.
  Qed.

  Goal decorateT = decorate2.
  Proof.
    ext A.
    unfold decorate2.
    unfold DerivedOperations.Decorate_Mapdt.
    unfold mapdt.
    unfold mapdt'.
    unfold DerivedOperations.Mapdt_Categorical.
    rewrite (dist_unit (F := T)).
    rewrite (fun_map_id (F := T)).
    reflexivity.
  Qed.

End Roundtrip1.

(** * Kleisli ~> Categorical ~> Kleisli *)
(**********************************************************************)
Module Roundtrip2.

  Context
    (E: Type)
    (T: Type -> Type)
    `{mapdtT: Mapdt E T}
    `{! Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}.

  #[local] Instance map': Map T :=
    DerivedOperations.Map_Mapdt.
  #[local] Instance dist': ApplicativeDist T :=
    DerivedOperations.Dist_Mapdt E T.
  #[local] Instance decorate': Decorate E T :=
    DerivedOperations.Decorate_Mapdt E T.

  Definition mapdt2: Mapdt E T :=
    DerivedOperations.Mapdt_Categorical E T.

  Goal forall G `{Applicative G},
      @mapdtT G _ _ _ = @mapdt2 G _ _ _.
  Proof.
    intros.
    ext A B f.
    unfold mapdt2.
    unfold DerivedOperations.Mapdt_Categorical.
    unfold map.
    unfold map'.
    unfold DerivedOperations.Map_Mapdt.
    unfold dist.
    unfold dist'.
    unfold DerivedOperations.Dist_Mapdt.
    unfold dec.
    unfold decorate'.
    unfold DerivedOperations.Decorate_Mapdt.
    rewrite <- map_to_mapdt.
    rewrite mapdt_map.
    change (mapdt (extract ∘ map f))
      with (map (F := fun A => A) (mapdt (extract ∘ map f))).
    rewrite (kdtf_mapdt2 (G2 := G) (G1 := fun A => A)).
    rewrite mapdt_app_id_l.
    rewrite <- (natural (ϕ := fun A => extract)).
    rewrite kc3_23.
    unfold_ops @Map_I.
    reflexivity.
  Qed.

End Roundtrip2.
