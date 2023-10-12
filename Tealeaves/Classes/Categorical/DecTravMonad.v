From Tealeaves Require Export
  Classes.Categorical.DecoratedMonad
  Classes.Categorical.TraversableMonad
  Classes.Categorical.DecTravFunctor.

Import Product.Notations.
Import Monad.Notations.
Import Comonad.Notations.

#[local] Generalizable Variables T F G W A B C.

(** * Decorated-traversable monads *)
(******************************************************************************)
Class DecoratedTraversableMonad
  (W : Type)
  (T : Type -> Type)
  `{op : Monoid_op W}
  `{unit : Monoid_unit W}
  `{Map T} `{Return T} `{Join T}
  `{Decorate W T} `{ApplicativeDist T} :=
  { dtmon_decorated :> DecoratedMonad W T;
    dtmon_traversable :> TraversableMonad T;
    dtmon_functor :> DecoratedTraversableFunctor W T;
  }.

(** Now we verify that the sub-classes can be inferred as well. *)
(******************************************************************************)
Section test_typeclasses.

  Context
    `{DecoratedTraversableMonad W T}.

  Goal Functor T. typeclasses eauto. Qed.
  Goal Monad T. typeclasses eauto. Qed.
  Goal DecoratedFunctor W T. typeclasses eauto. Qed.
  Goal DecoratedMonad W T. typeclasses eauto. Qed.
  Goal TraversableFunctor T. typeclasses eauto. Qed.
  Goal TraversableMonad T. typeclasses eauto. Qed.
  Goal DecoratedTraversableFunctor W T. typeclasses eauto. Qed.
(*
  Goal SetlikeFunctor T. typeclasses eauto. Qed.
  Goal SetlikeMonad T. Fail typeclasses eauto. Abort.
  Goal ListableFunctor T. typeclasses eauto. Qed.
  Goal ListableMonad T. Fail typeclasses eauto. Abort.
 *)

End test_typeclasses.
