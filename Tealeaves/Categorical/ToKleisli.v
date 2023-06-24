
(** * Monad to Kleisli monad *)
(******************************************************************************)

Module ToKleisli.

  Export Kleisli.Monad.
  Import Kleisli.Monad.Notations.

  Generalizable All Variables.

  Section operation.

    Context
      (T : Type -> Type)
      `{Fmap T} `{Join T}.

    #[export] Instance Bind_join : Bind T T :=
      fun {A B} (f : A -> T B) => join T ∘ fmap T f.

  End operation.

  Section with_monad.

    Context
      (T : Type -> Type)
      `{Classes.Monad.Monad T}.

    (** *** Identity law *)
    (******************************************************************************)
    Lemma mon_bind_id :
      `(bind T (ret T) = @id (T A)).
    Proof.
      intros. unfold_ops @Bind_join.
      now rewrite (mon_join_fmap_ret T).
    Qed.

    (** *** Composition law *)
    (******************************************************************************)
    Lemma mon_bind_bind : forall `(g : B -> T C) `(f : A -> T B),
        bind T g ∘ bind T f = bind T (g ⋆ f).
    Proof.
      introv. unfold transparent tcs.
      unfold kcompose.
      unfold_ops @Bind_join.
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

    #[export] Instance Kleisli_Monad : Kleisli.Monad.Monad T :=
      {| kmon_bind0 := @mon_bind_comp_ret;
        kmon_bind1 := @mon_bind_id;
        kmon_bind2 := @mon_bind_bind;
      |}.

  End with_monad.

End ToKleisli.

(** ** Derived laws *)
(******************************************************************************)
Section ToKleisli_laws.

  Context
    (T : Type -> Type)
   `{Monad T}.

  Generalizable All Variables.
  Import Kleisli.Monad.Notations.
  Import ToKleisli.

  Lemma fmap_to_bind : forall `(f : A -> B),
      fmap T f = bind T (ret T ∘ f).
  Proof.
    intros. unfold_ops @Bind_join.
    rewrite <- (fun_fmap_fmap T).
    reassociate <-.
    rewrite (mon_join_fmap_ret T).
    reflexivity.
  Qed.

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

  (** ** Left identity law *)
  Theorem kleisli_id_l : forall `(f : A -> T B),
      (@ret T _ B) ⋆ f = f.
  Proof.
    intros. unfold kcompose. now rewrite (kmon_bind1 T).
  Qed.

  (** ** Right identity law *)
  Theorem kleisli_id_r : forall `(g : B -> T C),
      g ⋆ (@ret T _ B) = g.
  Proof.
    intros. unfold kcompose. now rewrite (kmon_bind0 T).
  Qed.

  (** ** Associativity law *)
  Theorem kleisli_assoc : forall `(h : C -> T D) `(g : B -> T C) `(f : A -> T B),
      h ⋆ (g ⋆ f) = (h ⋆ g) ⋆ f.
  Proof.
    intros. unfold kcompose at 3.
    now rewrite <- (kmon_bind2 T).
  Qed.

End ToKleisli_laws.























From Tealeaves Require Import Classes.Kleisli.Monad.

#[export] Instance Bind_RightAction (F T : Type -> Type) `{Fmap F} `{RightAction F T} : Bind F T :=
  fun {A B} (f : A -> T B) => right_action F ∘ fmap F f.

(** * Kleisli laws for <<bind>> *)
(******************************************************************************)
Module ToKleisli.

  Import Kleisli.Monad.Notations.
  Import Classes.Monad.ToKleisli.

  Section Monad_kleisli_laws.

    Generalizable All Variables.

    Context
      (T : Type -> Type)
        `{Classes.RightModule.RightModule F T}.

    (** *** Identity law *)
    Lemma bind_id :
      `(bind F (ret T A) = @id (F A)).
    Proof.
      intros. unfold transparent tcs.
      now rewrite (mod_action_fmap_ret F T).
    Qed.

    (** *** Composition law *)
    Lemma bind_bind : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
        bind F g ∘ bind F f = bind F (g ⋆ f).
    Proof.
      introv. unfold transparent tcs. unfold kcompose.
      unfold_ops @Bind_join.
      rewrite <- 2(fun_fmap_fmap F).
      reassociate <- on right.
      change (fmap ?F (fmap ?T g)) with (fmap (F ∘ T) g).
      reassociate <- on right.
      rewrite <- (mod_action_action F T).
      reassociate -> near (fmap (F ∘ T) g).
      now rewrite <- (natural (ϕ := @right_action F T _)).
    Qed.

  End Monad_kleisli_laws.

  #[local] Instance Kleisli_RightModule {F T} `{Classes.RightModule.RightModule F T} : Kleisli.Monad.RightModule F T :=
    {| kmod_bind1 := @bind_id T F _ _ _ _ _ _;
      kmod_bind2 := @bind_bind T F _ _ _ _ _ _;
    |}.

  (** ** Specification for <<fmap>>  *)
  (******************************************************************************)
  Section Monad_suboperations.

    Context
      (T : Type -> Type)
     `{Classes.Monad.Monad T}.

    (** *** [fmap] as a special case of [bind]. *)
    Lemma fmap_to_bind {A B} : forall `(f : A -> B),
        fmap T f = bind T (ret T B ∘ f).
    Proof.
      intros. unfold transparent tcs.
      rewrite <- (fun_fmap_fmap T).
      reassociate <- on right.
      now rewrite (mon_join_fmap_ret T).
    Qed.

  End Monad_suboperations.

End ToKleisli.

