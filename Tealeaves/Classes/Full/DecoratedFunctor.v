From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor.

Import Monoid.Notations.
Import Product.Notations.
Import Kleisli.Comonad.Notations.

#[local] Generalizable Variables E T.

(** ** Full typeclasses *)
(******************************************************************************)
Class DecoratedFunctorFull (E: Type) (T: Type -> Type)
  `{Mapd_ET: Mapd E T} `{Map_T: Map T} :=
  { kdff_df :> DecoratedFunctor E T;
    kdff_map_compat :> Compat_Map_Mapd E T;
  }.

Definition DecoratedFunctorFull_DecoratedFunctor
  `{DecoratedFunctor E T}:
  `{DecoratedFunctorFull E T} :=
  {| kdff_df := _ |}.
