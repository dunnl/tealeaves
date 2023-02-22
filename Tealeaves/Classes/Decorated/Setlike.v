From Tealeaves Require Export
  Classes.Monoid
  Classes.Decorated.Functor
  Classes.Decorated.Monad
  Classes.Setlike.Functor
  Classes.Setlike.Monad
  Functors.Sets
  Data.Strength.

Import Monoid.Notations.
Import Setlike.Functor.Notations.

#[local] Generalizable Variables W A F.

(** * Decorated set-like functors *)
(******************************************************************************)

(** ** Derived operation [tosetd] *)
(******************************************************************************)
Definition tosetd F `{Toset F} `{Decorate W F} {A} :
  F A -> (W * A -> Prop) := toset F ∘ dec F.

#[local] Notation "x ∈d t" :=
  (tosetd _ t x) (at level 50) : tealeaves_scope.

(** ** Utility lemmas for [shift] *)
(******************************************************************************)
Section shift_utility_lemmas.

  Context
    (F : Type -> Type)
    `{SetlikeFunctor F}
    `{Monoid W}.

  Theorem in_shift_iff {A} : forall w w1 a (t : F (W * A)),
      (w, a) ∈ shift F (w1, t) <->
      exists w2, (w2, a) ∈ t /\ w = w1 ● w2.
  Proof.
    introv. unfold shift, compose, strength.
    rewrite (in_fmap_iff F). split.
    - intros [ [w1' [w2' a']] [hin heq]].
      rewrite (in_fmap_iff F) in hin.
      destruct hin as [ [w_ a_] [hin' heq']].
      inverts heq'. inverts heq. now (exists w2').
    - intros [w2 [? ?]]. exists (w1, (w2, a)).
      rewrite (in_fmap_iff F). subst. split.
      + now (exists (w2, a)).
      + reflexivity.
  Qed.

  Theorem in_shift_mono {A} : forall w1 w2 a (t : F (W * A)),
      (w1, a) ∈ t -> (w2 ● w1, a) ∈ shift F (w2, t).
  Proof.
    introv. unfold shift, compose, strength.
    rewrite (in_fmap_iff F). exists (w2, (w1, a)).
    rewrite (in_fmap_iff F). split.
    - now (exists (w1, a)).
    - easy.
  Qed.

End shift_utility_lemmas.

(** ** Utility lemmas for [toset] and [tosetd] *)
(******************************************************************************)
Section tosetd_utility_lemmas.

  Context
    (F : Type -> Type)
    `{SetlikeFunctor F}
    `{Monoid W}
    `{Decorate W F}
    `{! DecoratedFunctor W F}
    {A : Type}.

  Implicit Types (w : W) (a : A) (t : F A).

  Theorem in_in_extract : forall w a (t : F (W * A)),
      (w, a) ∈ t -> a ∈ fmap F (extract (prod W)) t.
  Proof.
    introv hyp. apply (in_fmap_iff F). now exists (w, a).
  Qed.

  Theorem in_of_ind : forall w a t,
      (w, a) ∈d t -> a ∈ t.
  Proof.
    introv hyp. replace t with (fmap F (extract (prod W)) (dec F t)).
    rewrite (in_fmap_iff F). now (exists (w, a)).
    compose near t on left.
    now rewrite (dfun_dec_extract W F).
  Qed.

  Theorem ind_of_in : forall t a,
      a ∈ t <-> exists w, (w, a) ∈d t.
  Proof.
    introv. split; intro hyp.
    - replace t with (fmap F (extract (prod W)) (dec F t)) in hyp
        by (now compose near t on left; rewrite (dfun_dec_extract W F)).
      rewrite (in_fmap_iff F) in hyp. destruct hyp as [[w ?] [? heq]].
      inverts heq. now (exists w).
    - destruct hyp as [? hyp]. now apply in_of_ind in hyp.
  Qed.

End tosetd_utility_lemmas.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.
End Notations.

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
