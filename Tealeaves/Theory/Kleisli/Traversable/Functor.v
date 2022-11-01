From Tealeaves Require Export
  Classes.Kleisli.Traversable.Functor
  Theory.Kleisli.Traversable.Functor.Container
  Theory.Kleisli.Traversable.Functor.ToFunctor
  Theory.Kleisli.Traversable.Functor.ToAlgebraic.

Module Derived.
  Module Operations.
    Include Theory.Kleisli.Traversable.Functor.ToFunctor.Operation.
  End Operations.
  Module Instances.
    Include Theory.Kleisli.Traversable.Functor.ToFunctor.Instances.
  End Instances.
  Module ToAlgebraic.
    Module Operations.
      Include Theory.Kleisli.Traversable.Functor.ToAlgebraic.Operations.
    End Operations.
    Module Instances.
      Include Theory.Kleisli.Traversable.Functor.ToAlgebraic.Instances.
    End Instances.
  End ToAlgebraic.
End Derived.
