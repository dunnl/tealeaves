From Tealeaves Require Export
  Classes.Functor
  Classes.Algebraic.Monad.

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
