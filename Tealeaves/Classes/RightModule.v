From Tealeaves Require Export
     Classes.Monad.

Import Functor.Notations.
Import Monad.Notations.
#[local] Open Scope tealeaves_scope.

(** * Right Modules *)
(******************************************************************************)
Section rightmodule_operations.

  Context
    (F T : Type -> Type).

  Class RightAction :=
    right_action : F ∘ T ⇒ F.

End rightmodule_operations.

Section RightModule.

  Context
    (F T : Type -> Type).

  Class RightModule
        `{Fmap T} `{Return T} `{Join T}
        `{Fmap F} `{RightAction F T} :=
    { rmod_monad :> Monad T;
      rmod_object :> Functor F;
      rmod_natural :> Natural (@right_action F T _);
      rmod_action_fmap_ret :
        `(right_action F T A ∘ fmap F (ret T) = @id (F A));
      rmod_action_action :
        `(right_action F T A ∘ right_action F T (T A) =
          right_action F T A ∘ fmap F (join T));
    }.

End RightModule.

Arguments right_action F {T}%function_scope {RightAction} {A}%type_scope.

(** ** Right modules compose with functors *)
(******************************************************************************)
Section functor_module_composition.

  Context
    `{Functor F}
    `{RightModule G T}.

  #[global] Instance RightAction_compose : RightAction (F ∘ G) T :=
    fun A => fmap F (right_action G).

  #[local] Set Keyed Unification.

  (** It does not seem to be a good idea to add this globally. It is
      better to use it explicitly. *)
  Instance RightModule_compose : RightModule (F ∘ G) T.
  Proof.
    constructor; try typeclasses eauto.
    - constructor; try typeclasses eauto.
      introv. unfold transparent tcs.
      unfold_compose_in_compose.
      rewrite 2(fun_fmap_fmap F).
      now rewrite (natural (G := G) (F := G ∘ T)).
    - intros. unfold_ops @RightAction_compose @Fmap_compose.
      rewrite (fun_fmap_fmap F).
      rewrite (rmod_action_fmap_ret G T).
      now rewrite (fun_fmap_id F).
    - intros. unfold_ops @RightAction_compose @Fmap_compose.
      rewrite 2(fun_fmap_fmap F).
      now rewrite (rmod_action_action G T).
  Qed.

End functor_module_composition.

(** ** Monads form right modules *)
(** Monads form modules. To avoid cycles in the typeclass hierarchy (causing
    typeclass resolution to diverge) we do not expose these instances globally.
    To generate module instances for a particular monad (e.g. [list]), it is
    best to apply the instances explicitly. *)
(******************************************************************************)
Section module_of_monad.

  Context
    (T : Type -> Type).

  Instance RightAction_Join `{Join T} : RightAction T T :=
    @join T _.

  Instance RightModule_Monad `{Monad T} : RightModule T T :=
    {| rmod_action_fmap_ret := mon_join_fmap_ret T;
       rmod_action_action := mon_join_join T;
    |}.

  Instance RightModule_Monad_2 `{RightModule F T} : RightModule T T :=
    {| rmod_action_fmap_ret := mon_join_fmap_ret T;
       rmod_action_action := mon_join_join T;
    |}.

End module_of_monad.

(** * Kleisli presentation of right modules *)
(******************************************************************************)

(** ** Lifting operation <<sub>> *)
(******************************************************************************)
Class Sub (F T : Type -> Type) :=
  sub : forall {A B}, (A -> T B) -> F A -> F B.

Arguments sub F {T}%function_scope {Sub} {A B}%type_scope _%function_scope.

Instance Sub_RightAction `{Fmap F} `{RightAction F T} : Sub F T :=
  fun `(f : A -> T B) => right_action F ∘ fmap F f.

(** ** Specifications for <<fmap>>  *)
(******************************************************************************)
Section rightmodule_suboperations.

  Context
    (F T : Type -> Type)
    `{RightModule F T}.

  (** *** [fmap] as a special case of [sub]. *)
  Corollary fmap_to_sub : forall `(f : A -> B),
      fmap F f = sub F (ret T ∘ f).
  Proof.
    intros. unfold transparent tcs.
    rewrite <- (fun_fmap_fmap F).
    reassociate <- on right.
    now rewrite (rmod_action_fmap_ret F T).
  Qed.

End rightmodule_suboperations.

(** ** Functor laws for [sub] *)
(******************************************************************************)
Section rightmodule_kleisli.

  Context
    (F T : Type -> Type)
    `{RightModule F T}.

  (** *** Identity law *)
  Lemma sub_id :
    `(sub F (ret T) = @id (F A)).
  Proof.
    intros. unfold transparent tcs.
    now rewrite (rmod_action_fmap_ret F T).
  Qed.

  (** *** Composition law *)
  Lemma sub_sub : forall `(g : B -> T C) `(f : A -> T B),
      sub F g ∘ sub F f = sub F (g ⋆ f).
  Proof.
    introv. unfold kcompose.
    unfold transparent tcs.
    rewrite <- 2(fun_fmap_fmap F).
    reassociate <- on right.
    change (fmap ?F (fmap ?T g)) with (fmap (F ∘ T) g).
    reassociate <- on right.
    rewrite <- (rmod_action_action F T).
    reassociate -> near (fmap (F ∘ T) g).
    now rewrite <- natural.
  Qed.

End rightmodule_kleisli.

(** ** Composition laws for <<sub>>/<<fmap>> *)
(******************************************************************************)
Section rightmodule_suboperation_composition.

  Context
    (F T : Type -> Type)
    `{RightModule F T}.

  Corollary sub_fmap : forall `(g : B -> T C) `(f : A -> B),
      sub F g ∘ fmap F f = sub F (g ∘ f).
  Proof.
    intros. unfold transparent tcs.
    now rewrite <- (fun_fmap_fmap F).
  Qed.

  Corollary fmap_sub : forall `(g : B -> C) `(f : A -> T B),
      fmap F g ∘ sub F f = sub F (fmap T g ∘ f).
  Proof.
    intros. unfold transparent tcs.
    reassociate <- on left.
    rewrite (natural). unfold_ops @Fmap_compose.
    now rewrite <- (fun_fmap_fmap F).
  Qed.

End rightmodule_suboperation_composition.
