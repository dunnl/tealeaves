From Tealeaves Require Export
     Classes.Functor
     Classes.Applicative
     Classes.TraversableFunctor
     Functors.Constant.

Import List.ListNotations.
#[local] Open Scope list_scope.

Import Functor.Notations.
Import SetlikeFunctor.Notations.
Import Monoid.Notations.
Import Applicative.Notations.
#[local] Open Scope tealeaves_scope.

(** * Domain-restricted operations *)
Section restrictions.

  Import SetlikeFunctor.
  Import SetlikeFunctor.Notations.

  Context
    `{TraversableFunctor T}
    (A : Type)
    (P : A -> Prop)
    (B : Type).

  Hypothesis ax : forall `(t : T A),
      (forall a, a ∈ t -> P a) ->
      runBatch_monoid (unit0 := True) (op := and) (B := B) P (iterate _ t).

  Context
    (t : T A)
    (hyp : forall a, a ∈ t -> P a)
    (f : sig P -> B).

  Definition sigma_fmap : T B.
    apply ax in hyp.
    induction (iterate _ t).
    - auto.
    - cbn in hyp.
      destruct hyp as [x1 x2].
      apply IHb. auto. auto.
      apply f. eexists. eauto.
  Defined.

End restrictions.
