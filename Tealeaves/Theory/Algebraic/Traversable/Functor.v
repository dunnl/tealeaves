From Tealeaves Require Export
  Classes.Algebraic.Traversable.Functor
  Theory.Algebraic.Traversable.Functor.Category
  Theory.Algebraic.Traversable.Functor.Coalgebraic
  Theory.Algebraic.Traversable.Functor.Const
  Theory.Algebraic.Traversable.Functor.Instances
(*  Theory.Algebraic.Traversable.Functor.Listable *)
  Theory.Algebraic.Traversable.Functor.Product
  Theory.Algebraic.Traversable.Functor.Properties
  Theory.Algebraic.Traversable.Functor.ToKleisli.

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
  Import Traversable.Functor.Notations.
End Notations.
