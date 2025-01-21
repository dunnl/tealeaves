From Tealeaves.Classes Require Import
  Categorical.Monad
  Kleisli.Monad.

#[local] Generalizable Variables T U A B.

(** * Full Kleisli Typeclasses *)
(******************************************************************************)
Class MonadFull (T: Type -> Type)
  `{Return_T: Return T}
  `{Map_T: Map T}
  `{Bind_T: Bind T T} :=
  { kmonf_kmon:> Monad T;
    kmonf_map_to_bind:> Compat_Map_Bind T T;
  }.

Class RightModuleFull (T: Type -> Type) (U: Type -> Type)
  `{Return_T: Return T}
  `{Bind_T: Bind T T}
  `{Bind_TU: Bind T U}
  `{Map_T: Map T}
  `{Map_U: Map U}
  :=
  { kmodf_mod :> RightModule T U;
    kmodf_compat :> Compat_Map_Bind T U;
    kmodf_monad :> MonadFull T;
  }.

Module FullInstances.

  #[export] Instance MonadFull_Monad
    (T: Type -> Type)
    `{Monad_T: Monad T}:
  MonadFull T
    (Map_T := Monad.DerivedOperations.Map_Bind T T)
  :=
  {| kmonf_map_to_bind := _;
  |}.

  #[export] Instance RightModuleFull_RightModule
    (T U: Type -> Type)
    `{RightModule_TU: RightModule T U}:
    RightModuleFull T U
      (Map_T := DerivedOperations.Map_Bind T T)
      (Map_U := DerivedOperations.Map_Bind T U) :=
    {| kmodf_monad :=
        MonadFull_Monad T (Monad_T := kmod_monad)
    |}.

End FullInstances.


(** * Derived Categorical operations *)
(******************************************************************************)
Class Compat_Join_Bind
  (T : Type -> Type)
  `{return_T: Return T}
  `{map_T: Map T}
  `{bind_T: Bind T T}
  `{join_T: Join T}
  : Prop :=
  { compat_join_bind: forall (A: Type),
      @join T join_T A = @bind T T bind_T (T A) A (@id (T A));
    compat_bind_join: forall (A B: Type) (f: A -> T B),
      @bind T T bind_T A B f = @join T join_T B ∘ @map T map_T A (T B) f;
  }.

(** ** Rewriting *)
(******************************************************************************)
Lemma join_to_bind
  `{join_T: Join T}
  `{return_T: Return T}
  `{map_T: Map T}
  `{bind_T: Bind T T}
  `{compat: !Compat_Join_Bind T}:
  forall (A: Type),
    @join T join_T A =
      @bind T T bind_T (T A) A id.
Proof.
  intros. rewrite compat_join_bind.
  reflexivity.
Qed.

Class Monad (T : Type -> Type)
  `{Return_inst: Return T}
  `{Bind_inst: Bind T T}
  `{Join_inst: Join T}
  `{Map_inst: Map T}
  :=
  { fmon_cat :> Categorical.Monad.Monad T;
    fmon_kleisli :> Kleisli.Monad.Monad T;
    fmon_compat :> Compat_Join_Bind T;
  }.
