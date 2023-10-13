From Tealeaves Require Import
  Classes.Categorical.Monad
  Classes.Categorical.RightModule.

#[local] Generalizable Variables T A B C.

(** * Algebraic monad to Kleisli monad *)
(******************************************************************************)
Module ToKleisli.

  Export Kleisli.Monad.
  Import Kleisli.Monad.Notations.

  Section operation.

    Context
      (T : Type -> Type)
      `{Map T} `{Join T}.

    #[export] Instance Bind_Join : Bind T T :=
      fun {A B} (f : A -> T B) => join T ∘ map T f.

  End operation.

  Section with_monad.

    Context
      (T : Type -> Type)
      `{Categorical.Monad.Monad T}.

    (** *** Identity law *)
    (******************************************************************************)
    Lemma mon_bind_id :
      `(bind T (ret T A) = @id (T A)).
    Proof.
      intros. unfold_ops @Bind_Join.
      now rewrite (mon_join_map_ret (T := T)).
    Qed.

    (** *** Composition law *)
    (******************************************************************************)
    Lemma mon_bind_bind : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
        bind T g ∘ bind T f = bind T (g ⋆1 f).
    Proof.
      introv. unfold transparent tcs.
      unfold kc1.
      unfold_ops @Bind_Join.
      rewrite <- 2(fun_map_map (F := T)).
      reassociate <- on right.
      reassociate <- on right.
      unfold_compose_in_compose.
      rewrite <- (mon_join_join (T := T)).
      change (map ?T (map ?T g)) with (map (T ∘ T) g).
      reassociate -> near (map (T ∘ T) g).
      rewrite <- (natural (ϕ := @join T _)).
      reflexivity.
    Qed.

    (** *** Unit law *)
    (******************************************************************************)
    Lemma mon_bind_comp_ret : forall (A B : Type) (f : A -> T B),
        bind T f ∘ ret T A = f.
    Proof.
      intros. unfold transparent tcs.
      reassociate -> on left.
      unfold_compose_in_compose; (* these rewrites are not visible *)
        change (@compose A) with (@compose ((fun A => A) A)).
      rewrite natural.
      reassociate <- on left.
      now rewrite (mon_join_ret (T := T)).
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

  Lemma map_to_bind : forall `(f : A -> B),
      map T f = bind T (ret T B ∘ f).
  Proof.
    intros. unfold_ops @Bind_Join.
    rewrite <- (fun_map_map (F := T)).
    reassociate <-.
    rewrite (mon_join_map_ret (T := T)).
    reflexivity.
  Qed.

  Corollary bind_map : forall `(g : B -> T C) `(f : A -> B),
      bind T g ∘ map T f = bind T (g ∘ f).
  Proof.
    intros. unfold transparent tcs.
    now rewrite <- (fun_map_map (F := T)).
  Qed.

  Corollary map_bind : forall `(g : B -> C) `(f : A -> T B),
      map T g ∘ bind T f = bind T (map T g ∘ f).
  Proof.
    intros. unfold transparent tcs.
    reassociate <- on left.
    rewrite (natural). unfold_ops @Map_compose.
    now rewrite <- (fun_map_map (F := T)).
  Qed.

  (** ** Left identity law *)
  Theorem kleisli_id_l : forall `(f : A -> T B),
      (@ret T _ B) ⋆1 f = f.
  Proof.
    intros. unfold kc1. now rewrite (kmon_bind1 (T := T)).
  Qed.

  (** ** Right identity law *)
  Theorem kleisli_id_r : forall `(g : B -> T C),
      g ⋆1 (@ret T _ B) = g.
  Proof.
    intros. unfold kc1. now rewrite (kmon_bind0 (T := T)).
  Qed.

  (** ** Associativity law *)
  Theorem kleisli_assoc : forall `(h : C -> T D) `(g : B -> T C) `(f : A -> T B),
      h ⋆1 (g ⋆1 f) = (h ⋆1 g) ⋆1 f.
  Proof.
    intros. unfold kc1 at 3. now rewrite <- (kmon_bind2 (T := T)).
  Qed.

End ToKleisli_laws.


(** * Right modules *)
(******************************************************************************)
Module ToKleisliRightModule.

  Import ToKleisli.
  Export Kleisli.Monad.
  Import Kleisli.Monad.Notations.

  #[export] Instance Bind_RightAction (F T : Type -> Type) `{Map F} `{RightAction F T} : Bind T F :=
    fun {A B} (f : A -> T B) => right_action F ∘ map F f.

  Section Monad_kleisli_laws.

    Context
      (T F : Type -> Type)
      `{Categorical.RightModule.RightModule F T}.

    (** *** Identity law *)
    Lemma bind_id :
      `(bind F (ret T A) = @id (F A)).
    Proof.
      intros. unfold transparent tcs.
      now rewrite (mod_action_map_ret).
    Qed.

    (** *** Composition law *)
    Lemma bind_bind : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
        bind F g ∘ bind F f = bind F (g ⋆1 f).
    Proof.
      introv. unfold transparent tcs. unfold kc1.
      unfold_ops @Bind_Join.
      rewrite <- 2(fun_map_map (F := F)).
      reassociate <- on right.
      change (map ?F (map ?T g)) with (map (F ∘ T) g).
      reassociate <- on right.
      rewrite <- (mod_action_action (U := T) (T := F)).
      reassociate -> near (map (F ∘ T) g).
      now rewrite <- (natural (ϕ := @right_action F T _)).
    Qed.

  End Monad_kleisli_laws.

  #[local] Instance Kleisli_RightModule {F T} `{Categorical.RightModule.RightModule F T}
    : Kleisli.Monad.RightModule T F :=
    {| kmod_bind1 := @bind_id T F _ _ _ _ _ _;
      kmod_bind2 := @bind_bind T F _ _ _ _ _ _;
    |}.

  (** ** Specification for <<map>>  *)
  (******************************************************************************)
  Section Monad_suboperations.

    Context
      (T : Type -> Type)
     `{Categorical.Monad.Monad T}.

    (** *** [map] as a special case of [bind]. *)
    Lemma map_to_bind {A B} : forall `(f : A -> B),
        map T f = bind T (ret T B ∘ f).
    Proof.
      intros. unfold transparent tcs.
      rewrite <- (fun_map_map (F := T)).
      reassociate <- on right.
      now rewrite (mon_join_map_ret (T := T)).
    Qed.

  End Monad_suboperations.

End ToKleisliRightModule.
