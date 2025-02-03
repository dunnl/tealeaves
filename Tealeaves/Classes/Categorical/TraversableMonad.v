From Tealeaves Require Export
  Classes.Categorical.Monad
  Classes.Categorical.TraversableFunctor.

Import Functor.Notations.
Import Monad.Notations.
Import Applicative.Notations.

#[local] Generalizable Variables F G T A B.

(** * Traversable monads *)
(**********************************************************************)
#[local] Arguments dist F%function_scope {ApplicativeDist}
  G%function_scope  {H H0 H1} A%type_scope _.
#[local] Arguments map F%function_scope {Map}
  {A B}%type_scope f%function_scope _.
#[local] Arguments dist F%function_scope {ApplicativeDist}
  G%function_scope {H H0 H1} {A}%type_scope _.
#[local] Arguments ret T%function_scope {Return} (A)%type_scope _.
#[local] Arguments join T%function_scope {Join} {A}%type_scope _.

(** ** Typeclass *)
(**********************************************************************)
Class TraversableMonad
  (T: Type -> Type)
  `{Map T} `{Return T} `{Join T} `{ApplicativeDist T} :=
  { trvmon_monad :> Monad T;
    trvmon_functor :> TraversableFunctor T;
    trvmon_ret: forall `{Applicative G},
      `(dist T G ∘ ret T (G A) = map G (ret T A));
    trvmon_join: forall `{Applicative G},
      `(dist T G ∘ join T (A := G A) =
          map G (join T) ∘ dist T G ∘ map T (dist T G));
  }.
