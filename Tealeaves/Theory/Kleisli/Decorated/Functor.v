From Tealeaves Require Export
  Classes.Kleisli.DT.Functor
  Theory.Kleisli.Decorated.Functor.ToAlgebraic
  Theory.Kleisli.Decorated.Functor.ToFunctor.

Module Derived.
  Module Operations.
    Include Theory.Kleisli.Decorated.Functor.ToFunctor.Operation.
  End Operations.
  Module Instances.
    Include Theory.Kleisli.Decorated.Functor.ToFunctor.Instance.
  End Instances.
  Module ToAlgebraic.
    Module Operations.
      Include Theory.Kleisli.Decorated.Functor.ToAlgebraic.Operations.
    End Operations.
    Module Instances.
      Include Theory.Kleisli.Decorated.Functor.ToAlgebraic.Instances.
    End Instances.
  End ToAlgebraic.
End Derived.
