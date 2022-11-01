From Tealeaves Require Export
  Theory.Algebraic.DT.Functor
  Classes.Algebraic.DT.Monad
  Theory.Algebraic.DT.Monad.ToKleisli.

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
  Include Algebraic.Comonad.Notations.
  Include Product.Notations.
  Include Traversable.Functor.Notations.
End Notations.
