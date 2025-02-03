From Tealeaves Require Import
  Functor
  Classes.Categorical.DecoratedFunctor
  Classes.Kleisli.DecoratedFunctor
  Adapters.CategoricalToKleisli.DecoratedFunctor
  Adapters.KleisliToCategorical.DecoratedFunctor.

Import Product.Notations.
Import Functor.Notations.
Import Comonad.Notations.

#[local] Generalizable Variable T.

(** * Categorical ~> Kleisli ~> Categorical *)
(**********************************************************************)
Section decorated_functor_categorical_kleisli_categorical.

  Context
    (E: Type)
    (T: Type -> Type)
    `{Map_T: Map T}
    `{Decorate_ET: Decorate E T}
    `{! Categorical.DecoratedFunctor.DecoratedFunctor E T}.

  Definition mapd': Mapd E T :=
    DerivedOperations.Mapd_Categorical E T.

  Definition map2: Map T :=
    DerivedOperations.Map_Mapd E T (Mapd_ET := mapd').

  Definition dec2: Decorate E T :=
    DerivedOperations.Decorate_Mapd E T (Mapd_ET := mapd').

  Goal Map_T = map2.
  Proof.
    unfold map2.
    unfold_ops @DerivedOperations.Map_Mapd.
    unfold mapd.
    unfold mapd'.
    unfold DerivedOperations.Mapd_Categorical.
    ext A B f.
    rewrite <- (fun_map_map (F := T)).
    reassociate ->.
    rewrite (dfun_dec_extract (E := E) (F := T)).
    reflexivity.
  Qed.

  Goal Decorate_ET = dec2.
  Proof.
    unfold dec2.
    unfold_ops @DerivedOperations.Decorate_Mapd.
    unfold mapd.
    unfold mapd'.
    unfold_ops @DerivedOperations.Mapd_Categorical.
    ext A.
    rewrite (fun_map_id (F := T)).
    reflexivity.
  Qed.

End decorated_functor_categorical_kleisli_categorical.

(** * Kleisli ~> Categorical ~> Kleisli *)
(**********************************************************************)
Section decorated_functor_kleisli_categorical_kleisli.

  Context
    (E: Type)
    (T: Type -> Type)
    `{Mapd_ET: Mapd E T}
    `{! Kleisli.DecoratedFunctor.DecoratedFunctor E T}.

  Definition map': Map T := DerivedOperations.Map_Mapd E T.
  Definition dec': Decorate E T := DerivedOperations.Decorate_Mapd E T.

  Definition mapd2: Mapd E T :=
    DerivedOperations.Mapd_Categorical E T
      (Map_F := map') (Decorate_EF := dec').

  Goal Mapd_ET = mapd2.
  Proof.
    unfold mapd2.
    unfold DerivedOperations.Mapd_Categorical.
    unfold map.
    unfold map'.
    unfold DerivedOperations.Map_Mapd.
    unfold dec.
    unfold dec'.
    unfold DerivedOperations.Decorate_Mapd.
    ext A B f.
    unfold_compose_in_compose.
    rewrite (kdf_mapd2 (E := E) (T := T)).
    rewrite Comonad.kc1_01.
    reflexivity.
  Qed.

End decorated_functor_kleisli_categorical_kleisli.
