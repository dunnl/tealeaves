From Tealeaves Require Import
  Theory.Algebraic.Decorated.Functor.Setlike
  Classes.Algebraic.Setlike.Monad
  Classes.Algebraic.Decorated.Monad.

#[local] Generalizable Variables W.

Import Monoid.Notations.
Import Setlike.Notations.

(** * Decorated set-like monads *)
(******************************************************************************)

(** ** Basic properties *)
(******************************************************************************)
Section decorated_setlike_properties.

  Context
    (T : Type -> Type)
    `{Monoid W}
    `{Fmap T} `{Return T} `{Join T} `{Decorate W T} `{Toset T}
    `{! DecoratedMonad W T}
    `{! SetlikeMonad T}.

  Theorem ind_ret_iff {A} : forall w (a a' : A),
      (w, a') ∈d ret T a <-> w = Ƶ /\ a' = a.
  Proof.
    introv. unfold tosetd, compose.
    compose near a on left.
    rewrite (dmon_ret W T). unfold compose.
    rewrite (in_ret_iff T). now rewrite pair_equal_spec.
  Qed.

End decorated_setlike_properties.
