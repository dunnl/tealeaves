(** This file implements "monads decorated by monoid <<W>>." *)
From Tealeaves Require Export
  Classes.Monoid
  Classes.Categorical.DecoratedFunctor
  Classes.Categorical.Monad
  Functors.Categorical.Writer.

Import Monoid.Notations.

#[local] Generalizable Variable W.

#[local] Arguments join T%function_scope {Join} (A)%type_scope _.

(** * Decorated monads *)
(******************************************************************************)
Class DecoratedMonad
  (W : Type)
  (T : Type -> Type)
  `{Map T} `{Return T} `{Join T} `{Decorate W T}
  `{Monoid_op W} `{Monoid_unit W} :=
  { dmon_functor :> DecoratedFunctor W T;
    dmon_monad :> Monad T;
    dmon_monoid :> Monoid W;
    dmon_ret : forall (A : Type),
      dec T ∘ ret T A = ret T (W * A) ∘ pair Ƶ;
    dmon_join : forall (A : Type),
      dec T ∘ join T A =
        join T (W * A) ∘ map T (shift T) ∘ dec T ∘ map T (dec T);
  }.

(** * Decorated right modules *)
(******************************************************************************)
Section DecoratedModule.

  Context
    (W : Type)
    (F T : Type -> Type)
    `{Map T} `{Return T} `{Join T} `{Decorate W T}
    `{Map F} `{RightAction F T} `{Decorate W F}
    `{Monoid_op W} `{Monoid_unit W}.

  Class DecoratedRightModule :=
    { dmod_monad :> DecoratedMonad W T;
      dmod_functor :> DecoratedFunctor W T;
      dmon_module :> RightModule F T;
      dmod_action : forall (A : Type),
        dec F ∘ right_action F (A := A) =
          right_action F ∘ map F (shift T) ∘ dec F ∘ map F (dec T);
    }.

End DecoratedModule.
