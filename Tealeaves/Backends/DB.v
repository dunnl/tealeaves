From Tealeaves.Backends.DB Require Export
  DB AutosubstShim Simplification.
From Tealeaves.Simplification Require Export
  Simplification.

(* We do not export Backends.DB.DB.Notations by default.
   Import it for de Bruijn operation notations. *)

(* We do not export Backends.DB.AutosubstShim.Notations by default.
   Import it for Autosubst-compatible notations. *)

Module Notations.
  Export Categorical.Applicative.Notations.
  Export Kleisli.Comonad.Notations.
  Export Kleisli.DecoratedMonad.Notations.
  Export Kleisli.TraversableFunctor.Notations.
  Export Kleisli.TraversableMonad.Notations.
  Export Kleisli.DecoratedTraversableFunctor.Notations.
  Export Kleisli.DecoratedTraversableMonad.Notations.
  Export Kleisli.DecoratedContainerFunctor.Notations.
  Export Categorical.ContainerFunctor.Notations.
  Export Misc.Product.Notations.
  Export Monoid.Notations.
  Export Misc.Subset.Notations.
  Export List.ListNotations.
End Notations.
