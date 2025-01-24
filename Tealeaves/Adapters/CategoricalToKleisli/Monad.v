From Tealeaves Require Import
  Classes.Categorical.Monad
  Classes.Categorical.RightModule
  Classes.Kleisli.Monad.

Import Kleisli.Monad.Notations.

#[local] Generalizable Variables T A B C.

(** * Categorical Monad to Kleisli Monad *)
(******************************************************************************)

(** ** Derived <<bind>> Operation *)
(******************************************************************************)
Module DerivedOperations.

  #[export] Instance Bind_Categorical (T: Type -> Type)
    `{map_T: Map T}
    `{join_T: Join T}
    : Bind T T :=
  fun {A B} (f: A -> T B) => join ∘ map (F := T) f.

End DerivedOperations.

(** ** Derived Kleisli Monad Laws *)
(******************************************************************************)
Module DerivedInstances.

  (* Alectryon doesn't like this
  Import CategoricalToKleisli.Monad.DerivedOperations.
   *)
  Import DerivedOperations.

  Section with_monad.

    Context
      `{Categorical.Monad.Monad T}.

    (** ** Derived <<bind>> is Compatible with Original <map>> *)
    (******************************************************************************)
    #[export] Instance Compat_Map_Bind_Derived:
      Compat_Map_Bind T T.
    Proof.
      hnf. ext A B f.
      change_left (map f).
      unfold DerivedOperations.Map_Bind.
      unfold bind, Bind_Categorical.
      rewrite <- fun_map_map.
      reassociate <- on right.
      rewrite mon_join_map_ret.
      reflexivity.
    Qed.

    (** *** Identity law *)
    (******************************************************************************)
    Lemma mon_bind_id:
      forall (A: Type),
        bind (ret (T := T) (A := A)) = @id (T A).
    Proof.
      intros.
      unfold_ops @Bind_Categorical.
      rewrite (mon_join_map_ret (T := T)).
      reflexivity.
    Qed.

    (** *** Composition law *)
    (******************************************************************************)
    Lemma mon_bind_bind:
      forall (A B C: Type) (g: B -> T C) (f: A -> T B),
        bind g ∘ bind f = bind (g ⋆ f).
    Proof.
      introv.
      unfold kc.
      unfold_ops @Bind_Categorical.
      rewrite <- 2(fun_map_map (F := T)).
      reassociate <- on right.
      reassociate <- on right.
      unfold_compose_in_compose.
      rewrite <- (mon_join_join (T := T)).
      change (map (F := T) (map g)) with (map (F := T ∘ T) g).
      reassociate -> near (map (F := T ∘ T) g).
      rewrite <- (natural (ϕ := @join T _)).
      reflexivity.
    Qed.

    (** *** Unit law *)
    (******************************************************************************)
    Lemma mon_bind_comp_ret: forall (A B: Type) (f: A -> T B),
        bind f ∘ ret = f.
    Proof.
      intros. unfold_ops @Bind_Categorical.
      reassociate -> on left.
      unfold_compose_in_compose; (* these rewrites are not visible *)
        change (@compose A) with (@compose ((fun A => A) A)).
      rewrite natural.
      reassociate <- on left.
      now rewrite (mon_join_ret (T := T)).
    Qed.

    #[export] Instance KleisliPreModule_CategoricalPreModule:
      Kleisli.Monad.RightPreModule T T :=
      {| kmod_bind1 := @mon_bind_id;
         kmod_bind2 := @mon_bind_bind;
      |}.
    #[export] Instance KleisliMonad_CategoricalMonad:
      Kleisli.Monad.Monad T :=
      {| kmon_bind0 := @mon_bind_comp_ret;
      |}.

  End with_monad.

End DerivedInstances.

(*
(** ** Derived laws *)
(******************************************************************************)
Section ToKleisli_laws.

  Context
    (T: Type -> Type)
   `{Categorical.Monad.Monad T}.

  Generalizable All Variables.
  Import Kleisli.Monad.Notations.
  Import ToKleisli.

  Lemma map_to_bind: forall `(f: A -> B),
      map T f = bind (ret T B ∘ f).
  Proof.
    intros. unfold_ops @Bind_Categorical.
    rewrite <- (fun_map_map (F := T)).
    reassociate <-.
    rewrite (mon_join_map_ret (T := T)).
    reflexivity.
  Qed.

  Corollary bind_map: forall `(g: B -> T C) `(f: A -> B),
      bind g ∘ map T f = bind (g ∘ f).
  Proof.
    intros. unfold transparent tcs.
    now rewrite <- (fun_map_map (F := T)).
  Qed.

  Corollary map_bind: forall `(g: B -> C) `(f: A -> T B),
      map T g ∘ bind f = bind (map T g ∘ f).
  Proof.
    intros. unfold transparent tcs.
    reassociate <- on left.
    rewrite (natural). unfold_ops @Map_compose.
    now rewrite <- (fun_map_map (F := T)).
  Qed.

  (** ** Left identity law *)
  Theorem kleisli_id_l: forall `(f: A -> T B),
      (@ret T _ B) ⋆1 f = f.
  Proof.
    intros. unfold kc1. now rewrite (kmon_bind1 (T := T)).
  Qed.

  (** ** Right identity law *)
  Theorem kleisli_id_r: forall `(g: B -> T C),
      g ⋆1 (@ret T _ B) = g.
  Proof.
    intros. unfold kc1. now rewrite (kmon_bind0 (T := T)).
  Qed.

  (** ** Associativity law *)
  Theorem kleisli_assoc: forall `(h: C -> T D) `(g: B -> T C) `(f: A -> T B),
      h ⋆1 (g ⋆1 f) = (h ⋆1 g) ⋆1 f.
  Proof.
    intros. unfold kc1 at 3. now rewrite <- (kmon_bind2 (T := T)).
  Qed.

End ToKleisli_laws.
*)


(** * Right modules *)
(******************************************************************************)
Module ToKleisliRightModule.

  Import DerivedOperations.
  Import DerivedInstances.

  #[export] Instance Bind_RightAction
    (T U: Type -> Type)
    `{Map_T: Map U}
    `{RightAction_TU: RightAction U T}:
    Bind T U :=
    fun A B (f: A -> T B) => right_action U ∘ map (F := U) f.

  Section Monad_kleisli_laws.

    Context
      (T F: Type -> Type)
      `{Categorical.RightModule.RightModule F T}.

    (** *** Identity law *)
    Lemma bind_id :
      `(bind (ret (T := T) (A := A)) = @id (F A)).
    Proof.
      intros. unfold transparent tcs.
      now rewrite (mod_action_map_ret).
    Qed.

    (** *** Composition law *)
    Lemma bind_bind: forall (A B C: Type) (g: B -> T C) (f: A -> T B),
        bind g ∘ bind f = bind (g ⋆ f).
    Proof.
      introv. unfold kc.
      unfold_ops @Bind_Categorical.
      unfold_ops @Bind_RightAction.
      rewrite <- 2(fun_map_map (F := F)).
      reassociate <- on right.
      change (map (F := F) (map (F := T) g)) with (map (F := F ∘ T) g).
      reassociate <- on right.
      rewrite <- (mod_action_action (U := T) (T := F)).
      reassociate -> near (map (F := F ∘ T) g).
      now rewrite <- (natural (ϕ := @right_action F T _)).
    Qed.

  End Monad_kleisli_laws.

  #[local] Instance Kleisli_RightModule {F T}
    `{Categorical.RightModule.RightModule F T}
   : Kleisli.Monad.RightPreModule T F :=
    {| kmod_bind1 := @bind_id T F _ _ _ _ _ _;
      kmod_bind2 := @bind_bind T F _ _ _ _ _ _;
    |}.

  (** ** Specification for <<map>>  *)
  (******************************************************************************)
  Section Monad_suboperations.

    Context
      (T: Type -> Type)
     `{Categorical.Monad.Monad T}.

    (** *** [map] as a special case of [bind]. *)
    Lemma map_to_bind {A B}: forall `(f: A -> B),
        map f = bind (ret ∘ f).
    Proof.
      intros. unfold transparent tcs.
      rewrite <- (fun_map_map (F := T)).
      reassociate <- on right.
      now rewrite (mon_join_map_ret (T := T)).
    Qed.

  End Monad_suboperations.

End ToKleisliRightModule.
