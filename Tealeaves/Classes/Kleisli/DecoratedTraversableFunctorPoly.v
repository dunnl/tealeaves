From Tealeaves Require Export
  Functors.List
  Classes.Setlike.Functor
  Classes.Traversable.Functor
  Classes.Traversable.Listable
  Classes.DT.Monad.

Import Product.Notations.
Import Monad.Notations.
Import Comonad.Notations.
Import DT.Monad.Notations.
#[local] Open Scope tealeaves_scope.

(** * Polymorphically decorated traversable monads *)
(******************************************************************************)
Section PolyDecoratedTraverableMonad.

  Context
  (T : Type -> Type -> Type)
  `{forall B, Fmap (T B)} `{forall B, Return (T B)} `{forall B, Join (T B)}
  `{forall B, Decorate (list B) (T B)} `{forall B, Dist (T B)}.

  Class PolyDecoratedTraversableMonad :=
    { pdtmon_dtm :> forall B, DecoratedTraversableMonad (list B) (T B);
    }.

End PolyDecoratedTraverableMonad.

Import DT.Monad.Derived.

(** Now we verify that the sub-classes can be inferred as well. *)
(******************************************************************************)
Section test_typeclasses.

  Context
    (T : Type -> Type -> Type)
    `{PolyDecoratedTraversableMonad T}.

  Goal forall B, Functor (T B). typeclasses eauto. Qed.
  Goal forall B, DecoratedFunctor (list B) (T B). typeclasses eauto. Qed.
  Goal forall B, Functor (T B). typeclasses eauto. Qed.
  Goal forall B, SetlikeFunctor (T B). typeclasses eauto. Qed.
  Goal forall B, ListableFunctor (T B). typeclasses eauto. Qed.
  Goal forall B, TraversableFunctor (T B). typeclasses eauto. Qed.
  Goal forall B, DecoratedTraversableFunctor (list B) (T B). typeclasses eauto. Qed.
  Goal forall B, Monad (T B). typeclasses eauto. Qed.
  Goal forall B, DecoratedMonad (list B) (T B). typeclasses eauto. Qed.
  Goal forall B, SetlikeMonad (T B). typeclasses eauto. Qed.
  Goal forall B, ListableMonad (T B). typeclasses eauto. Qed.
  Goal forall B, TraversableMonad (T B). typeclasses eauto. Qed.

End test_typeclasses.
