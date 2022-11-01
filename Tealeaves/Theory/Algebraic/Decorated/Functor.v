From Tealeaves Require Export
  Classes.Algebraic.Decorated.Functor
  Theory.Algebraic.Decorated.Functor.Category
  Theory.Algebraic.Decorated.Functor.Characterization
  Theory.Algebraic.Decorated.Functor.Helpers
  Theory.Algebraic.Decorated.Functor.Properties
  Theory.Algebraic.Decorated.Functor.Setlike
  Theory.Algebraic.Decorated.Functor.ToKleisli.

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
