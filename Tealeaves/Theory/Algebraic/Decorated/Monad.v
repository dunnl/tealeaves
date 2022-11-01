From Tealeaves Require Export
  Theory.Algebraic.Decorated.Functor
  Classes.Algebraic.Decorated.Monad
  Theory.Algebraic.Decorated.Monad.Characterization
  Theory.Algebraic.Decorated.Monad.Helpers
  Theory.Algebraic.Decorated.Monad.Listable
  Theory.Algebraic.Decorated.Monad.Setlike
  Theory.Algebraic.Decorated.Monad.ToKleisli.

Module Derived.
  Module Operations.
    Include ToKleisli.Operation.
  End Operations.
  Module Instances.
    Include ToKleisli.Instance.
  End Instances.
End Derived.

Module Notations.
  Include Functor.Notations.
  Import Algebraic.Comonad.Notations.
  Import Product.Notations.
End Notations.
