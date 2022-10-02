(** This file implements "monads decorated by monoid <<W>>." *)
From Tealeaves Require Export
  Classes.Monoid
  Classes.Algebraic.Decorated.Functor
  Classes.Algebraic.Monad
  Functors.Writer.

Import Monoid.Notations.

#[local] Generalizable Variable W.

(** * The <<shift>> operation *)
(******************************************************************************)
Definition shift F `{Fmap F} `{Monoid_op W} {A} : W * F (W * A) -> F (W * A) :=
  fmap F (join (prod W)) ∘ strength F.

(** * Decorated monads *)
(******************************************************************************)
Section DecoratedMonad.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Fmap T} `{Return T} `{Join T} `{Decorate W T}
    `{Monoid_op W} `{Monoid_unit W}.

  Class DecoratedMonad:=
    { dmon_functor :> DecoratedFunctor W T;
      dmon_monad :> Monad T;
      dmon_monoid :> Monoid W;
      dmon_ret : forall (A : Type),
        dec T ∘ ret T = ret T ∘ pair Ƶ (B:=A);
      dmon_join : forall (A : Type),
        dec T ∘ join T (A:=A) =
          join T ∘ fmap T (shift T) ∘ dec T ∘ fmap T (dec T);
    }.

End DecoratedMonad.

(** * Decorated right modules *)
(******************************************************************************)
Section DecoratedModule.

  Context
    (W : Type)
    (F T : Type -> Type)
    `{Fmap T} `{Return T} `{Join T} `{Decorate W T}
    `{Fmap F} `{RightAction F T} `{Decorate W F}
    `{Monoid_op W} `{Monoid_unit W}.

  Class DecoratedRightModule :=
    { dmod_monad :> DecoratedMonad W T;
      dmod_functor :> DecoratedFunctor W T;
      dmon_module :> RightModule F T;
      dmod_action : forall (A : Type),
        dec F ∘ right_action F (A := A) =
          right_action F ∘ fmap F (shift T) ∘ dec F ∘ fmap F (dec T);
    }.

End DecoratedModule.
