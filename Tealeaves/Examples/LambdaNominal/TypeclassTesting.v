From Tealeaves Require Import
  Examples.LambdaNominal.Categorical.

(*|
***********************************************
Testing Typeclass Machinery
***********************************************
|*)

From Tealeaves Require
  Adapters.CategoricalToKleisli.Monad
  Adapters.CategoricalToKleisli.DecoratedFunctor
  Adapters.CategoricalToKleisli.TraversableFunctor
  Adapters.CategoricalToKleisli.DecoratedTraversableFunctor
  Adapters.CategoricalToKleisli.DecoratedTraversableMonad.

From Tealeaves Require
  Adapters.PolyToMono.Categorical.DecoratedFunctor
  Adapters.PolyToMono.Categorical.TraversableFunctor.

From Tealeaves Require
  Adapters.CategoricalToKleisli.DecoratedTraversableMonadPoly
  Adapters.CategoricalToKleisli.DecoratedTraversableFunctorPoly.

Module CategoricalPDTMUsefulInstances.

  Export
    Classes.Categorical.DecoratedTraversableMonadPoly.

  Export
    Adapters.CategoricalToKleisli.DecoratedTraversableMonadPoly
    Adapters.CategoricalToKleisli.DecoratedTraversableMonadPoly.DerivedOperations
    Adapters.CategoricalToKleisli.DecoratedTraversableMonadPoly.DerivedInstances.

  Export
    Adapters.CategoricalToKleisli.DecoratedTraversableFunctorPoly
    Adapters.CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedOperations
    Adapters.CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedInstances.

  (*
  Export
    Adapters.CategoricalToKleisli.DecoratedFunctorPoly
    Adapters.CategoricalToKleisli.DecoratedFunctorPoly.DerivedOperations
    Adapters.CategoricalToKleisli.DecoratedFunctorPoly.DerivedInstances.
   *)

  Export
    Adapters.CategoricalToKleisli.DecoratedTraversableMonad
    Adapters.CategoricalToKleisli.Monad.

  Export
    Adapters.PolyToMono.Categorical.DecoratedFunctor
    Adapters.PolyToMono.Categorical.TraversableFunctor.


  Export Adapters.CategoricalToKleisli.Monad.
  Export CategoricalToKleisli.Monad.DerivedOperations.
  Export CategoricalToKleisli.Monad.DerivedInstances.

  Export Adapters.CategoricalToKleisli.DecoratedFunctor.
  Export CategoricalToKleisli.DecoratedFunctor.DerivedOperations.
  Export CategoricalToKleisli.DecoratedFunctor.DerivedInstances.

  Export Adapters.CategoricalToKleisli.TraversableFunctor.
  Export CategoricalToKleisli.TraversableFunctor.DerivedOperations.
  Export CategoricalToKleisli.TraversableFunctor.DerivedInstances.

  Export Adapters.CategoricalToKleisli.DecoratedTraversableFunctor.
  Export CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.
  Export CategoricalToKleisli.DecoratedTraversableFunctor.DerivedInstances.

  Export Adapters.CategoricalToKleisli.DecoratedTraversableMonad.
  Export CategoricalToKleisli.DecoratedTraversableMonad.DerivedOperations.
  Export CategoricalToKleisli.DecoratedTraversableMonad.DerivedInstances.

  Export PolyToMono.Categorical.DecoratedFunctor.ToMono1.
  Export PolyToMono.Categorical.TraversableFunctor.ToMono.

  Context (B: Set) (V: Set).

  Goal Functor (term B).
    typeclasses eauto.
  Qed.

  Goal Categorical.Monad.Monad (term B).
    typeclasses eauto.
  Qed.

  Goal Categorical.DecoratedFunctor.DecoratedFunctor (list B) (term B).
    typeclasses eauto.
  Qed.

  Goal Categorical.TraversableFunctor.TraversableFunctor (term B).
    typeclasses eauto.
  Qed.

  Goal Categorical.DecoratedTraversableFunctor.DecoratedTraversableFunctor (list B) (term B).
    typeclasses eauto.
  Qed.

  Goal Kleisli.Monad.Monad (term B).
    typeclasses eauto.
  Qed.

  Goal Kleisli.DecoratedFunctor.DecoratedFunctor (list B) (term B).
    typeclasses eauto.
  Qed.

  Goal Kleisli.TraversableFunctor.TraversableFunctor (term B).
    typeclasses eauto.
  Qed.

  Goal Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor (list B) (term B).
    typeclasses eauto.
  Qed.

  (*
  Goal Kleisli.DecoratedFunctorPoly.DecoratedFunctorPoly term.
    typeclasses eauto.
  Qed.
   *)

  Goal Kleisli.DecoratedTraversableMonadPoly.DecoratedTraversableMonadPoly term.
    Fail typeclasses eauto.
  Abort.

  Goal Kleisli.DecoratedTraversableFunctorPoly.DecoratedTraversableFunctorPoly term.
    Fail typeclasses eauto.
  Abort.

End CategoricalPDTMUsefulInstances.

