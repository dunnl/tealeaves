From Tealeaves Require Export
  Classes.Decorated.Monad
  Classes.Traversable.Monad
  Classes.DT.Functor.

Import Product.Notations.
Import Monad.Notations.
Import Comonad.Notations.

#[local] Generalizable Variable W T.

(** * Decorated-traversable monads *)
(******************************************************************************)
Section DecoratedTraverableMonad.

  Context
  (W : Type)
  (T : Type -> Type)
  `{op : Monoid_op W}
  `{unit : Monoid_unit W}
  `{Fmap T} `{Return T} `{Join T}
  `{Decorate W T} `{Dist T}.

  Class DecoratedTraversableMonad :=
    { dtmon_decorated :> DecoratedMonad W T;
      dtmon_traversable :> TraversableMonad T;
      dtmon_functor :> DecoratedTraversableFunctor W T;
    }.

End DecoratedTraverableMonad.

(** Now we verify that the sub-classes can be inferred as well. *)
(******************************************************************************)
Section test_typeclasses.

  Context
    `{DecoratedTraversableMonad W T}.

  Goal Functor T. typeclasses eauto. Qed.
  Goal DecoratedFunctor W T. typeclasses eauto. Qed.
  (*Goal SetlikeFunctor T. typeclasses eauto. Qed.
  Goal ListableFunctor T. typeclasses eauto. Qed.
  Goal TraversableFunctor T. typeclasses eauto. Qed.
  Goal DecoratedTraversableFunctor W T. typeclasses eauto. Qed.

  Goal Monad T. typeclasses eauto. Qed.
  Goal DecoratedMonad W T. typeclasses eauto. Qed.
  Goal SetlikeMonad T. Fail typeclasses eauto. Abort.
  Goal ListableMonad T. Fail typeclasses eauto. Abort.
  Goal TraversableMonad T. typeclasses eauto. Qed. *)

End test_typeclasses.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Include Monad.Notations.
  Include Comonad.Notations.
End Notations.
