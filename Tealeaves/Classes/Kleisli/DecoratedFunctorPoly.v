From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableMonad.

Import Product.Notations.
Import Monad.Notations.
Import Comonad.Notations.
Import DecoratedTraversableMonad.Notations.

(** * Polymorphically decorated traversable monads *)
(******************************************************************************)
Section DecoratedFunctorPoly.

  Class MapdP
    (T : Type -> Type -> Type) :=
    mapdp :
      forall (WA WB : Type) (A B : Type),
        (list WA * WA -> WB) ->
        (list WA * A -> B) ->
        T WA A -> T WB B.

End DecoratedFunctorPoly.
