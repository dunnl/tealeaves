From Tealeaves Require Export
  Theory.Kleisli.Decorated.Functor
  Classes.Kleisli.Decorated.Monad
  Theory.Kleisli.Decorated.Monad.ToAlgebraic
  Theory.Kleisli.Decorated.Monad.DerivedInstances.

Module Derived.
  Module Operations.
    Include Theory.Kleisli.Decorated.Monad.DerivedInstances.Operations.
  End Operations.
  Module Instances.
    Include Theory.Kleisli.Decorated.Monad.DerivedInstances.Instances.
  End Instances.
  Module ToAlgebraic.
    Module Operations.
      Include Theory.Kleisli.Decorated.Monad.ToAlgebraic.Operations.
    End Operations.
    Module Instances.
      Include Theory.Kleisli.Decorated.Monad.ToAlgebraic.Instances.
    End Instances.
  End ToAlgebraic.
End Derived.
