From Tealeaves Require Export
  Classes.Categorical.DecoratedFunctor
  Classes.Categorical.TraversableFunctor.

Import Monoid.Notations.
Import Strength.Notations.
Import Product.Notations.
Import TraversableFunctor.Notations.
Import Strength.Notations.

#[local] Generalizable Variables T E G A B C W op zero F ϕ.

(** * Decorated-traversable functors *)
(******************************************************************************)

(** ** Typeclass *)
(******************************************************************************)
Class DecoratedTraversableFunctor
  (E : Type)
  (F : Type -> Type)
  `{Map F} `{Decorate E F} `{ApplicativeDist F} :=
  { dtfun_decorated :> DecoratedFunctor E F;
    dtfun_traversable :> TraversableFunctor F;
    dtfun_compat : forall `{Applicative G},
      `(dist G ∘ map F (σ G) ∘ dec F (A := G A) =
          map G (dec F) ∘ dist G);
  }.

(*|
  At this stage we make sure our typeclass hierarchy works as expected.
|*)
Section test_typeclasses.

  Context
    `{DecoratedTraversableFunctor E T}.

  Goal Functor T. typeclasses eauto. Qed.
  Goal DecoratedFunctor E T. typeclasses eauto. Qed.
  Goal TraversableFunctor T. typeclasses eauto. Qed.
(*
  Goal ListableFunctor T. typeclasses eauto. Qed.
  Goal SetlikeFunctor T. typeclasses eauto. Qed.
 *)

End test_typeclasses.
