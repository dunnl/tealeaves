From Tealeaves Require Export
  Classes.Functor
  Categorical.Classes.Monad.

Import Functor.Notations.

#[local] Generalizable Variables W T A.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments join T%function_scope {Join} {A}%type_scope _.
#[local] Arguments ret T%function_scope {Return} {A}%type_scope _.

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
    `{Map T} `{Return T} `{Join T}
    `{Map F} `{RightAction F T}.

  Class RightModule :=
    { mod_object :> Functor F;
      mon_monoid :> Monad T;
      mod_natural :> Natural (@right_action F T _);
      mod_action_map_ret :
      `(right_action F T A ∘ map F (ret T _) = @id (F A));
      mod_action_action :
      `(right_action F T A ∘ right_action F T (T A) =
          right_action F T A ∘ map F (join T));
    }.

End module_class.

#[global] Arguments right_action F {T}%function_scope {RightAction} {A}%type_scope.

(** * Coerceing monads into modules *)
(******************************************************************************)
Module RightModule_Monad.

  #[export] Instance RightAction_Join `{Join T} : RightAction T T := @join T _.

  #[export] Instance RightModule_Monad `{Monad T} : RightModule T T :=
    {| mod_action_map_ret := mon_join_map_ret T;
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
    fun A => map F (right_action G).

  #[local] Set Keyed Unification.

  (** It does not seem to be a good idea to add this globally. It is
      better to use it explicitly. *)
  Instance RightModule_compose : RightModule (F ∘ G) T.
  Proof.
    constructor; try typeclasses eauto.
    - constructor; try typeclasses eauto.
      introv. unfold transparent tcs.
      unfold_compose_in_compose.
      rewrite 2(fun_map_map F).
      now rewrite (natural (G := G) (F := G ∘ T)).
    - intros. unfold_ops @RightAction_compose @Map_compose.
      rewrite (fun_map_map F).
      rewrite (mod_action_map_ret G T).
      now rewrite (fun_map_id F).
    - intros. unfold_ops @RightAction_compose @Map_compose.
      rewrite 2(fun_map_map F).
      now rewrite (mod_action_action G T).
  Qed.

End functor_module_composition.