From Tealeaves Require Export
  Classes.Algebraic.DT.Functor
  Theory.Algebraic.DT.Functor.Category
  Theory.Algebraic.DT.Functor.ToKleisli.

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
