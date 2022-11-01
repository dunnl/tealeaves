From Tealeaves Require Export
  Classes.Algebraic.Monad
  Theory.Algebraic.Monad.Properties
  Theory.Algebraic.Monad.ToKleisli.

Module Derived.
  Module Operations.
    Include Monad.ToKleisli.Operation.
  End Operations.
  Module Instances.
    Include Monad.ToKleisli.Instance.
  End Instances.
End Derived.

Module Notations.
  Include Functor.Notations.
  Include Monad.Notations.
End Notations.
