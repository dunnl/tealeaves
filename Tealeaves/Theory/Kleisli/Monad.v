From Tealeaves Require Export
  Classes.Kleisli.Monad
  Theory.Kleisli.Monad.Properties
  Theory.Kleisli.Monad.ToApplicative
  Theory.Kleisli.Monad.ToFunctor.

Module Derived.
  Module Operations.
    Include Monad.ToFunctor.Operation.
  End Operations.
  Module Instances.
    Include Monad.ToFunctor.Instances.
  End Instances.
End Derived.

Module Notations.
  Include Monad.Notations.
End Notations.
