From Tealeaves Require Export
  Classes.Categorical.Monad
  Classes.Kleisli.Monad.

Import Kleisli.Monad.Notations.

(** * Kleisli Monads to Categorical Monads *)
(**********************************************************************)

(** ** Derived <<join>> Operation *)
(**********************************************************************)
Module DerivedOperations.
  #[export] Instance Join_Bind
    (T : Type -> Type)
    `{Return_T: Return T}
    `{Bind_TT: Bind T T}: Join T :=
  fun A => bind (@id (T A)).
End DerivedOperations.

(** ** Derived Categorical Laws *)
(**********************************************************************)
Module ToCategorical.

  Section proofs.

    Context
      (T : Type -> Type)
      `{Classes.Kleisli.Monad.Monad T}.

    (* Alectyron doesn't like this
       Import KleisliToCategorical.Monad.DerivedOperations.
     *)
    Import DerivedOperations.
    Existing Instance Kleisli.Monad.DerivedOperations.Map_Bind.
    Existing Instance Kleisli.Monad.DerivedInstances.Functor_Monad.

    #[export] Instance Natural_Ret: Natural (@ret T Return_T).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_ops @DerivedOperations.Map_Bind.
        unfold_ops @Map_I.
        rewrite (kmon_bind0 (T := T)).
        reflexivity.
    Qed.

    #[export] Instance Natural_Join:
      Natural (@join T (Join_Bind T)).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_ops @Map_compose.
        unfold_ops @DerivedOperations.Map_Bind.
        unfold_ops @DerivedOperations.Join_Bind.
        unfold_compose_in_compose.
        rewrite (kmon_bind2 (T := T)).
        unfold kc.
        change (?x ∘ id) with x.
        (* RHS *)
        rewrite (kmon_bind2 (T := T)).
        unfold kc.
        reassociate <- on right.
        rewrite (kmon_bind0 (T := T)).
        change (id ∘ ?x) with x.
        reflexivity.
    Qed.

    #[local] Instance CategoricalFromKleisli_Monad:
      Classes.Categorical.Monad.Monad T.
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold transparent tcs.
        unfold_compose_in_compose.
        rewrite (kmon_bind0 (T := T)).
        reflexivity.
      - intros.
        unfold transparent tcs.
        unfold_compose_in_compose.
        rewrite (kmon_bind2 (T := T)).
        unfold kc.
        reassociate <- near (bind (@id (T A))).
        rewrite (kmon_bind0 (T := T)).
        change (id ∘ ?x) with x.
        rewrite (kmon_bind1 (T := T) A).
        reflexivity.
      - intros.
        unfold transparent tcs.
        unfold_compose_in_compose.
        rewrite (kmon_bind2 (T := T)).
        rewrite (kmon_bind2 (T := T)).
        unfold kc.
        reassociate <- near (bind (@id (T A))).
        rewrite (kmon_bind0 (T := T)).
        reflexivity.
    Qed.

  End proofs.

End ToCategorical.
