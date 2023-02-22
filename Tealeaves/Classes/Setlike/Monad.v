From Tealeaves Require Export
  Classes.Setlike.Functor
  Classes.Monad.

Import Sets.Notations.
Import Setlike.Functor.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables W A a b.

(** * Set-like monads *)
(******************************************************************************)
Section SetlikeMonad.

  Context
    (T : Type -> Type)
    `{Fmap T} `{Return T} `{Join T} `{Toset T}.

  Class SetlikeMonad :=
    { xmon_monad :> Monad T;
      xmon_functor :> SetlikeFunctor T;
      xmon_ret_injective :
        `(ret T (a : A) = ret T (b : A) -> a = b);
      xmon_ret :
        `(toset T ∘ ret T (A:=A) = ret set);
      xmon_join :
        `(toset (A:=A) T ∘ join T =
          join set ∘ toset T ∘ fmap T (toset T));
    }.

End SetlikeMonad.

(** ** Instance for [set] *)
(******************************************************************************)
Section SetlikeMonad_set_instance.

  Existing Instance Toset_set.
  Existing Instance Natural_toset_set.
  Existing Instance SetlikeFunctor_set.

  Instance SetlikeMonad_set : SetlikeMonad set.
  Proof.
    constructor; try typeclasses eauto.
    - apply set_ret_injective.
    - reflexivity.
    - intros. unfold compose. ext S a.
      cbv. propext.
      + firstorder.
      + firstorder (subst; firstorder).
  Qed.

End SetlikeMonad_set_instance.

(** ** Basic properties of set-like monads *)
(******************************************************************************)
Section setlike_monad_properties.

  Context
    (T : Type -> Type)
    `{SetlikeMonad T}.

  (** [ret] always acts like a singleton *)
  Theorem in_ret_iff {A} : forall (a a' : A),
      a' ∈ ret T a <-> a = a'.
  Proof.
    intros a a'. compose near a on left.
    now rewrite (xmon_ret T).
  Qed.

  (** [join] acts like a union operation *)
  Corollary in_join_iff {A} : forall (t : T (T A)) (a : A),
      a ∈ join T t <-> (exists t', t' ∈ t /\ a ∈ t').
  Proof.
    introv. compose near t on left.
    rewrite (xmon_join T).
    reassociate -> on left.
    rewrite <- (natural (B:=set A) (G:=(->Prop))).
    unfold transparent tcs; unfold compose.
    intuition (preprocess; eauto).
  Qed.

End setlike_monad_properties.
