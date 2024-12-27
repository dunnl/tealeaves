From Tealeaves Require Export
  Classes.Categorical.Monad
  Classes.Kleisli.Monad.

(** * Categorical monads to Kleisli monads *)
(******************************************************************************)
#[export] Instance Join_Bind
  (T : Type -> Type)
  `{Return T} `{Bind T T} : Join T :=
  fun A => bind (@id (T A)).

Module Instance.

  Section proofs.

    Context
      (T : Type -> Type)
        `{Classes.Kleisli.Monad.Monad T}.

    Existing Instance Map_Bind.
    Existing Instance Functor_Monad.
    Existing Instance MonadFull_Monad.

    #[local] Instance CategoricalFromKleisli_Monad: Classes.Categorical.Monad.Monad T.
    Proof.
      constructor.
      -
        typeclasses eauto.
      - constructor.
        typeclasses eauto.
        typeclasses eauto.
        intros. unfold transparent tcs.
        now rewrite (kmon_bind0 (T := T)).
      - constructor.
        typeclasses eauto.
        typeclasses eauto.
        intros. unfold transparent tcs.
        unfold_compose_in_compose.
        do 2 rewrite (kmon_bind2 (T := T)).
        fequal. unfold kc1.
        reassociate <- on right.
        now rewrite (kmon_bind0 (T := T)).
      - intros. unfold transparent tcs.
        unfold_compose_in_compose.
        now rewrite (kmon_bind0 (T := T)).
      - intros. unfold transparent tcs.
        unfold_compose_in_compose.
        rewrite (kmon_bind2 (T := T)).
        unfold kc1.
        reassociate <- near (bind (@id (T A))).
        rewrite (kmon_bind0 (T := T)). unfold compose.
        now rewrite <- (kmon_bind1 (T := T) A) at 1.
      - intros. unfold transparent tcs.
        unfold_compose_in_compose.
        rewrite (kmon_bind2 (T := T)).
        rewrite (kmon_bind2 (T := T)).
        unfold kc1.
        reassociate <- near (bind (@id (T A))).
        now rewrite (kmon_bind0 (T := T)).
    Qed.

  End proofs.

End Instance.
