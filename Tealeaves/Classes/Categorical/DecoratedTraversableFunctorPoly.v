From Tealeaves Require Export
  Classes.Categorical.DecoratedFunctorPoly
  Classes.Categorical.TraversableFunctor2
  Classes.Categorical.ApplicativeCommutativeIdempotent
  Classes.Categorical.Monad
  Functors.List
  Functors.Writer.

#[local] Generalizable Variables T F G W A B C.

(** * Polymorphic Decorated Traversable Functor *)
(**********************************************************************)
Class DecoratedTraversableFunctorPoly
  (T: Type -> Type -> Type)
  `{Map2 T} `{DecoratePoly T} `{ApplicativeDist2 T} :=
  {
    dtfp_functor :> Functor2 T;
    dtfp_decorated :> DecoratedFunctorPoly T;
    dtfp_traversable :> TraversableFunctor2 T;
    dtfp_dist2_decpoly:
    forall (B V: Type) `{ApplicativeCommutativeIdempotent G},
      dist2 (G := G) ∘ map2 (dist Z G) (dist2 (T := Z2)) ∘ (decp (B := G B) (V := G V)) =
        map (F := G) (decp (B := B) (V := V)) ∘ dist2 (T := T) (G := G);
  }.

