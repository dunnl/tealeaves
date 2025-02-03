From Tealeaves Require Export
  Classes.Categorical.DecoratedFunctor
  Classes.Categorical.TraversableFunctor.

Import Monoid.Notations.
Import Strength.Notations.
Import Product.Notations.
Import TraversableFunctor.Notations.
Import Strength.Notations.

#[local] Generalizable Variables T E G A B C W op zero F ϕ.

(** * Decorated Traversable Functors *)
(**********************************************************************)
#[local] Arguments map F%function_scope {Map}
  {A B}%type_scope f%function_scope _.
#[local] Arguments dist F%function_scope {ApplicativeDist}
  G%function_scope {H H0 H1} {A}%type_scope _.

(** ** Typeclass *)
(**********************************************************************)
Class DecoratedTraversableFunctor
  (E: Type)
  (F: Type -> Type)
  `{Map F} `{Decorate E F} `{ApplicativeDist F} :=
  { dtfun_decorated :> DecoratedFunctor E F;
    dtfun_traversable :> TraversableFunctor F;
    dtfun_compat: forall `{Applicative G},
      `(dist F G ∘ map F σ ∘ dec F (A := G A) =
          map G (dec F) ∘ dist F G);
  }.
