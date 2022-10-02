From Tealeaves Require Export
  Classes.Functor
  Classes.Algebraic.Monad
  Classes.Kleisli.Monad
  Theory.Kleisli.Monad.ToFunctor.

Import Product.Notations.
Import Functor.Notations.
Import Kleisli.Monad.Notations.

#[local] Generalizable Variable T.

Module Operation.
  Section with_kleisli.

    Context
      (T : Type -> Type)
      `{Return T} `{Bind T T}.

  #[export] Instance Join_Bind  : Join T :=
      fun A => bind T (@id (T A)).

  End with_kleisli.
End Operation.

Section proofs.

  Import Operation.
  Import ToFunctor.Operation.
  Import ToFunctor.Instances.

  Context
    (T : Type -> Type)
    `{Monad T}.

  Instance: Algebraic.Monad.Monad T.
  Proof.
    constructor.
    - typeclasses eauto.
    - constructor.
      typeclasses eauto.
      typeclasses eauto.
      intros. unfold transparent tcs.
      now rewrite (kmon_bind0 T).
    - constructor.
      typeclasses eauto.
      typeclasses eauto.
      intros. unfold transparent tcs.
      unfold_compose_in_compose.
      do 2 rewrite (kmon_bind2 T).
      fequal. unfold kcompose.
      reassociate <- on right.
      now rewrite (kmon_bind0 T).
    - intros. unfold transparent tcs.
      unfold_compose_in_compose.
      now rewrite (kmon_bind0 T).
    - intros. unfold transparent tcs.
      unfold_compose_in_compose.
      rewrite (kmon_bind2 T).
      unfold kcompose.
      reassociate <- near (bind T (@id (T A))).
      rewrite (kmon_bind0 T). unfold compose.
      now rewrite <- (kmon_bind1 T A) at 1.
    - intros. unfold transparent tcs.
      unfold_compose_in_compose.
      rewrite (kmon_bind2 T).
      rewrite (kmon_bind2 T).
      unfold kcompose.
      reassociate <- near (bind T (@id (T A))).
      now rewrite (kmon_bind0 T).
  Qed.

End proofs.

