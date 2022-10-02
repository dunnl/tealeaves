From Tealeaves Require Export
  Classes.Algebraic.Decorated.Functor
  Classes.Algebraic.Traversable.Functor.

Import Strength.Notations.

#[local] Generalizable Variables T E G A.

(** * Decorated-traversable functors *)
(******************************************************************************)
Section DecoratedTraversableFunctor.

  Context
    (E : Type)
    (F : Type -> Type)
    `{Fmap F} `{Decorate E F} `{Dist F}.

  Class DecoratedTraversableFunctor :=
    { dtfun_decorated :> DecoratedFunctor E F;
      dtfun_traversable :> TraversableFunctor F;
      dtfun_compat : forall `{Applicative G},
        `(dist F G ∘ fmap F (σ G) ∘ dec F (A := G A) =
            fmap G (dec F) ∘ dist F G);
    }.

End DecoratedTraversableFunctor.

(*|
At this stage we make sure our typeclass hierarchy works as expected. Given a `DecoratedTraversableFunctor`, Coq should infer the following classes.
|*)
Section test_typeclasses.

  Context
    `{DecoratedTraversableFunctor E T}.

  Goal Functor T. typeclasses eauto. Qed.
  Goal DecoratedFunctor E T. typeclasses eauto. Qed.
  Goal TraversableFunctor T. typeclasses eauto. Qed.
  (* Goal ListableFunctor T. typeclasses eauto. Qed.
  Goal SetlikeFunctor T. typeclasses eauto. Qed.  *)

End test_typeclasses.
