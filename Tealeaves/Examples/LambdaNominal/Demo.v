From Tealeaves Require Export
  Examples.LambdaNominal.Categorical
  Backends.Named.FV
  Backends.Named.Barendregt
  Backends.Adapters.NamedToLN.

Import LambdaNominal.Syntax.Notations.

From Tealeaves Require Export
  Classes.Categorical.DecoratedTraversableFunctorPoly
  Classes.Kleisli.DecoratedTraversableMonadPoly.


From Tealeaves Require
  Adapters.MonoidHom.DecoratedTraversableMonad
  Adapters.PolyToMono.Kleisli.DecoratedFunctor
  Adapters.PolyToMono.Kleisli.DecoratedTraversableFunctor
  Adapters.PolyToMono.Kleisli.DecoratedTraversableMonad
  Adapters.CategoricalToKleisli.DecoratedTraversableMonadPoly
  Adapters.CategoricalToKleisli.TraversableFunctor
  Adapters.CategoricalToKleisli.DecoratedTraversableFunctor.


Import Kleisli.DecoratedFunctorPoly.
Import CategoricalToKleisli.DecoratedFunctorPoly.
Import CategoricalToKleisli.DecoratedFunctorPoly.DerivedOperations.
Import CategoricalToKleisli.DecoratedFunctorPoly.DerivedInstances.
Import CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedOperations.
Import CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedInstances.
Import CategoricalToKleisli.DecoratedTraversableMonadPoly.DerivedOperations.
Import CategoricalToKleisli.DecoratedTraversableMonadPoly.DerivedInstances.

Import DecoratedFunctorPoly.ToMono.
Import TraversableFunctor2.ToMono.
Import PolyToMono.Kleisli.DecoratedFunctor.ToMono1.

Import CategoricalToKleisli.TraversableFunctor.DerivedOperations.
Import CategoricalToKleisli.TraversableFunctor.DerivedInstances.

Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.
Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedInstances.

Existing Instance Theory.DecoratedTraversableFunctor.ToCtxset_Mapdt.
Existing Instance Theory.TraversableFunctor.ToSubset_Traverse.




Example term0 := (λ 0, `0).
Example term1 := (λ 1, `1 · `2).
Example term2 := (λ 0, `1 · `0).
Example term3 := (λ 2, `1 · `0).
Example term4 := (λ 2, `1 · `2).
Example term5 := (λ 2, `10 · `2).

Compute FV term0.
Compute FV term1.
Compute FV term2.
Compute FV term3.
Compute FV term4.
Compute FV term5.

Compute subst 0 term0 term0. (* (λ) 1 `1 *)
Compute subst 0 term1 term0. (* (λ) 1 `1 *)
Compute subst 0 term2 term0. (* (λ) 2 `2 *)
Compute subst 0 term3 term0. (* (λ) 2 `2 *)
Compute subst 0 term4 term0. (* (λ) 2 `2 *)
Compute subst 0 term5 term0. (* (λ) 1 `1 *)

Compute subst 0 term0 term1.
Compute subst 0 term1 term1.
Compute subst 0 term2 term1.
Compute subst 0 term4 term1.
Compute subst 0 term5 term1.

Compute term_nominal_to_ln term term0.
Compute term_nominal_to_ln term term1.
Compute term_nominal_to_ln term term5.
