From Tealeaves Require Export
  Classes.Functor
  Classes.Monad.

Import Functor.Notations.

#[local] Generalizable Variables W T A.

(** * Right modules *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Section rightmodule_operations.

  Context
    (F T : Type -> Type).

  Class RightAction :=
    right_action : F ∘ T ⇒ F.

End rightmodule_operations.

#[local] Arguments ret _%function_scope {Return} A%type_scope.

(** ** Right modules *)
(******************************************************************************)
Section module_class.

  Context
    (F T : Type -> Type)
    `{Fmap T} `{Return T} `{Join T}
    `{Fmap F} `{RightAction F T}.

  Class RightModule :=
    { mod_object :> Functor F;
      mon_monoid :> Monad T;
      mod_natural :> Natural (@right_action F T _);
      mod_action_fmap_ret :
      `(right_action F T A ∘ fmap F (ret T _) = @id (F A));
      mod_action_action :
      `(right_action F T A ∘ right_action F T (T A) =
          right_action F T A ∘ fmap F (join T));
    }.

End module_class.

#[global] Arguments right_action F {T}%function_scope {RightAction} {A}%type_scope.

(** * Coerceing monads into modules *)
(******************************************************************************)
Module RightModule_Monad.

  #[export] Instance RightAction_Join `{Join T} : RightAction T T := @join T _.

  #[export] Instance RightModule_Monad `{Monad T} : RightModule T T :=
    {| mod_action_fmap_ret := mon_join_fmap_ret T;
      mod_action_action := mon_join_join T; |}.

End RightModule_Monad.

(** ** Right modules compose with functors *)
(******************************************************************************)
Section functor_module_composition.

  #[local] Generalizable Variables F G.
  
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
      rewrite (mod_action_fmap_ret G T).
      now rewrite (fun_fmap_id F).
    - intros. unfold_ops @RightAction_compose @Fmap_compose.
      rewrite 2(fun_fmap_fmap F).
      now rewrite (mod_action_action G T).
  Qed.

End functor_module_composition.

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
