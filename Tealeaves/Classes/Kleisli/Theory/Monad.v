From Tealeaves Require Export
  Classes.Kleisli.Monad.

#[local] Generalizable Variables F G A B C D W T U ϕ.
Import Monad.Notations.
Import Functor.Notations.


(** ** Full typeclasses *)
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
    kmodf_compat :> Compat_Map_Bind U T;
    kmodf_monad :> MonadFull T;
  }.

Section instances.

  #[local] Instance MonadFull_Monad (T: Type -> Type)
    `{Monad_T: Monad T} :
  MonadFull T (Map_T := Map_Bind T T) :=
  {| kmonf_map_to_bind := _;
  |}.

  #[local] Instance RightModuleFull_RightModule
    (T U: Type -> Type)
    `{RightModule_TU: RightModule T U}:
    RightModuleFull T U
      (Map_T := Map_Bind T T)
      (Map_U := Map_Bind T U) :=
    {| kmodf_monad :=
        MonadFull_Monad T (Monad_T := kmod_monad)
    |}.

End instances.
