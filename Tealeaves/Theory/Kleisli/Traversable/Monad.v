From Tealeaves Require Export
  Classes.Kleisli.Traversable.Monad
  Theory.Kleisli.Traversable.Functor
  Theory.Kleisli.Traversable.Monad.Container
  Theory.Kleisli.Traversable.Monad.ToFunctor
  Theory.Kleisli.Traversable.Monad.ToAlgebraic.

Module Derived.
  Module Operations.
    Include Theory.Kleisli.Traversable.Monad.ToFunctor.Operation.
    Include Theory.Kleisli.Traversable.Monad.DerivedInstances.Operations.
  End Operations.
  Module Instances.
    Include Theory.Kleisli.Traversable.Monad.ToFunctor.Instance.
    Include Theory.Kleisli.Traversable.Monad.DerivedInstances.Instances.
  End Instances.
  Module ToAlgebraic.
    Module Operations.
      Include Theory.Kleisli.Traversable.Monad.ToAlgebraic.Operations.
    End Operations.
    Module Instances.
      Include Theory.Kleisli.Traversable.Monad.ToAlgebraic.Instances.
    End Instances.
  End ToAlgebraic.
End Derived.
