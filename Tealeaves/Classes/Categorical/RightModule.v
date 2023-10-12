From Tealeaves Require Export
  Classes.Functor
  Classes.Categorical.Monad.

Import Functor.Notations.

#[local] Generalizable Variables T U A.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments join T%function_scope {Join} {A}%type_scope _.
#[local] Arguments ret T%function_scope {Return} (A)%type_scope _.

(** * Right modules *)
(******************************************************************************)

(** ** Operation *)
(******************************************************************************)
Class RightAction (T U : Type -> Type) :=
  right_action : T ∘ U ⇒ T.

#[global] Arguments right_action (T)%function_scope {U} {RightAction} {A}%type_scope _.
#[local] Arguments right_action (T U)%function_scope {RightAction} A%type_scope _.

(** ** Typeclass *)
(******************************************************************************)
Class RightModule
  (T U : Type -> Type)
  `{Map U} `{Return U} `{Join U}
  `{Map T} `{RightAction T U} :=
  { mod_object :> Functor T;
    mon_monoid :> Monad U;
    mod_natural :> Natural (right_action T U);
    mod_action_map_ret :
    `(right_action T U A ∘ map T (ret U A) = @id (T A));
    mod_action_action :
    `(right_action T U A ∘ right_action T U (U A) =
        right_action T U A ∘ map T (join U));
    }.

(** * Coerceing monads into modules *)
(******************************************************************************)
#[export] Instance RightAction_Join `{Join T} : RightAction T T := @join T _.

#[export] Instance RightModule_Monad `{Monad T} : RightModule T T :=
  {| mod_action_map_ret := mon_join_map_ret T;
    mod_action_action := mon_join_join T; |}.

(** ** Right modules compose with functors *)
(******************************************************************************)
Section functor_module_composition.

  #[local] Generalizable Variables F G.

  Context
    `{Functor T1}
    `{RightModule T2 U}.

  #[global] Instance RightAction_compose : RightAction (T1 ∘ T2) U :=
    fun A => @map T1 _ (T2 (U A)) (T2 A) (right_action T2 U A).

  #[local] Set Keyed Unification.

  (** It does not seem to be a good idea to add this globally. It is
      better to use it explicitly. *)
  Instance RightModule_compose : RightModule (T1 ∘ T2) U.
  Proof.
    inversion H6; econstructor.
    - constructor; try typeclasses eauto.
      introv. unfold transparent tcs.
      unfold_compose_in_compose.
      rewrite 2(fun_map_map (F := T1)).
      now rewrite (natural (G := T2) (F := T2 ∘ U)).
    - intros. unfold_ops @RightAction_compose @Map_compose.
      rewrite (fun_map_map (F := T1)).
      rewrite (mod_action_map_ret (T := T2) (U := U)).
      now rewrite (fun_map_id (F := T1)).
    - intros. unfold_ops @RightAction_compose @Map_compose.
      rewrite 2(fun_map_map (F := T1)).
      now rewrite (mod_action_action (T := T2) (U := U)).
  Qed.

End functor_module_composition.
