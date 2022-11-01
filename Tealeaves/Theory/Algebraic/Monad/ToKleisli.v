From Tealeaves Require Export
  Classes.Algebraic.Monad
  Classes.Kleisli.Monad.

Import Kleisli.Monad.Notations.
Import Functor.Notations.

#[local] Generalizable Variables A B C T F.

(** * Algebraic monad to Kleisli monad *)
(******************************************************************************)

(** ** The <<bind>> operation *)
(******************************************************************************)
Module Operation.
  Section with_algebraic.

    Context
      (T : Type -> Type)
      `{Fmap T} `{Join T}.

    #[export] Instance Bind_alg : Bind T T :=
      fun `(f : A -> T B) => join T ∘ fmap T f.

  End with_algebraic.
End Operation.

Import Operation.

(** ** Kleisli laws for <<bind>> *)
(******************************************************************************)
Module Instance.

  Section with_monad.

    Context
      (T : Type -> Type)
      `{Algebraic.Monad.Monad T}.

    (** *** Identity law *)
    (******************************************************************************)
    Lemma mon_bind_id :
      `(bind T (ret T) = @id (T A)).
    Proof.
      intros. unfold_ops @Bind_alg.
      now rewrite (mon_join_fmap_ret T).
    Qed.

    (** *** Composition law *)
    (******************************************************************************)
    Lemma mon_bind_bind : forall `(g : B -> T C) `(f : A -> T B),
        bind T g ∘ bind T f = bind T (g ⋆ f).
    Proof.
      introv. unfold transparent tcs.
      unfold kcompose.
      unfold_ops @Bind_alg.
      rewrite <- 2(fun_fmap_fmap T).
      reassociate <- on right.
      change (fmap ?T (fmap ?T g)) with (fmap (T ∘ T) g).
      reassociate <- on right.
      rewrite <- (mon_join_join T).
      reassociate -> near (fmap (T ∘ T) g).
      now rewrite <- (natural (ϕ := @join T _)).
    Qed.

    (** *** Unit law *)
    (******************************************************************************)
    Lemma mon_bind_comp_ret : forall (A B : Type) (f : A -> T B),
        bind T f ∘ ret T = f.
    Proof.
      intros. unfold transparent tcs.
      reassociate -> on left.
      unfold_compose_in_compose; (* these rewrites are not visible *)
        change (@compose A) with (@compose ((fun A => A) A)).
      rewrite natural.
      reassociate <- on left.
      now rewrite (mon_join_ret T).
    Qed.

    #[export] Instance toKleisli : Kleisli.Monad.Monad T :=
      {| kmon_bind0 := @mon_bind_comp_ret;
        kmon_bind1 := @mon_bind_id;
        kmon_bind2 := @mon_bind_bind;
      |}.

  End with_monad.

End Instance.

(** * Derived laws *)
(******************************************************************************)

(** ** Specification for <<fmap>> *)
(******************************************************************************)
Section with_monad.

  Context
    (T : Type -> Type)
    `{Algebraic.Monad.Monad T}.

  Lemma fmap_to_bind : forall `(f : A -> B),
      fmap T f = bind T (ret T ∘ f).
  Proof.
    intros. unfold_ops @Bind_alg.
    rewrite <- (fun_fmap_fmap T).
    reassociate <-.
    rewrite (mon_join_fmap_ret T).
    reflexivity.
  Qed.

End with_monad.

(** ** Composition between <<bind>> and <<fmap>> *)
(******************************************************************************)
Section monad_suboperation_composition.

  Context
    (T : Type -> Type)
    `{Algebraic.Monad.Monad T}.

  Corollary bind_fmap : forall `(g : B -> T C) `(f : A -> B),
      bind T g ∘ fmap T f = bind T (g ∘ f).
  Proof.
    intros. unfold transparent tcs.
    now rewrite <- (fun_fmap_fmap T).
  Qed.

  Corollary fmap_bind : forall `(g : B -> C) `(f : A -> T B),
      fmap T g ∘ bind T f = bind T (fmap T g ∘ f).
  Proof.
    intros. unfold transparent tcs.
    reassociate <- on left.
    rewrite (natural). unfold_ops @Fmap_compose.
    now rewrite <- (fun_fmap_fmap T).
  Qed.

End monad_suboperation_composition.
