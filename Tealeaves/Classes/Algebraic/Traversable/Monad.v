From Tealeaves Require Export
  Classes.Algebraic.Monad
  Classes.Algebraic.Traversable.Functor
  Theory.Algebraic.Traversable.Functor.Category.

Import Functor.Notations.
Import Monad.Notations.
Import Applicative.Notations.

#[local] Generalizable Variables F G T A.

(** * Traversable monads *)
(******************************************************************************)
Section TraversableMonad.

  Context
    (T : Type -> Type)
    `{Fmap T} `{Return T} `{Join T} `{Dist T}.

  Class TraversableMonad :=
    { trvmon_monad :> Monad T;
      trvmon_functor :> TraversableFunctor T;
      trvmon_ret : forall `{Applicative G},
          `(dist T G ∘ ret T (A := G A) = fmap G (ret T));
      trvmon_join : forall `{Applicative G},
          `(dist T G ∘ join T = fmap G (join T) ∘ dist (T ∘ T) G (A := A));
    }.

End TraversableMonad.
