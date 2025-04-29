From Tealeaves Require Export
  Examples.LambdaNominal.Categorical
  Backends.Nominal.FV
  Backends.Nominal.Barendregt
  Backends.Adapters.NominaltoLN.

Import LambdaNominal.Syntax.Notations.

From Tealeaves Require Export
  Classes.Categorical.DecoratedTraversableFunctorPoly
  Classes.Kleisli.DecoratedTraversableMonadPoly.

From Tealeaves Require
  Adapters.MonoidHom.DecoratedTraversableMonad
  Adapters.PolyToMono.PDTM.

Import PDTM.CategoricalToKleisliAll.


#[local] Existing Instance Theory.DecoratedTraversableFunctor.ToCtxset_Mapdt.
#[local] Existing Instance Theory.TraversableFunctor.ToSubset_Traverse.

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

Compute nomToLN term0.
Compute nomToLN term1.
Compute nomToLN term5.

Section freshening_demo.

  Notation "'x'" := 0.
  Notation "'y'" := 1.
  Notation "'z'" := 2.
  Notation "'v'" := 3.

  Example idfn := (λ v, `v).
  Example input := (λ x, λ x, `z · `x).
  Example output := subst y idfn input.
  Example expected_output := (λ x, λ y, `z · `y).

  Compute subst y idfn input.

  Goal output = expected_output.
    reflexivity.
  Qed.

End freshening_demo.
