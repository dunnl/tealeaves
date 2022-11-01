From Tealeaves Require Export
  Classes.Kleisli.DT.Functor
  Theory.Kleisli.DT.Functor.Container
  Theory.Kleisli.DT.Functor.DerivedInstances.
  (*Theory.Kleisli.DT.Functor.ToAlgebraic.*)

Module Derived.
  Module Operations.
    Include Theory.Kleisli.DT.Functor.DerivedInstances.Operations.
  End Operations.
  Module Instances.
    Include Theory.Kleisli.DT.Functor.DerivedInstances.Instances.
  End Instances.
  Module ToAlgebraic.
    Module Operations.
      (* Include Theory.Kleisli.DT.Functor.ToAlgebraic.Operations. *)
    End Operations.
    Module Instances.
      (* Include Theory.Kleisli.DT.Functor.ToAlgebraic.Instances. *)
    End Instances.
  End ToAlgebraic.
End Derived.
