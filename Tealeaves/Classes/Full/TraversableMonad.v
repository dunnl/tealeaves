
Class TraversableMonadFull
  (T : Type -> Type)
  `{ret_inst : Return T}
  `{Map_inst : Map T}
  `{Traverse_inst : Traverse T}
  `{Bind_inst : Bind T T}
  `{Bindt_inst : Bindt T T} :=
  { ktmf_ktm :> TraversableMonad T;
    ktmf_map_compat :> Compat_Map_Bindt T T;
    ktmf_bind_compat :> Compat_Bind_Bindt T T;
    ktmf_traverse_compat :> Compat_Traverse_Bindt T T;
  }.

Class TraversableRightModuleFull
  (T : Type -> Type)
  (U : Type -> Type)
  `{ret_inst : Return T}
  `{Map_T_inst : Map T}
  `{Traverse_T_inst : Traverse T}
  `{Bind_T_inst : Bind T T}
  `{Bindt_T_inst : Bindt T T}
  `{Map_U_inst : Map U}
  `{Traverse_U_inst : Traverse U}
  `{Bind_U_inst : Bind T U}
  `{Bindt_U_inst : Bindt T U} :=
  { ktmodf_kmond :> TraversableMonadFull T;
    ktmodf_mod :> TraversableRightModule T U;
    ktmodf_map_compat :> Compat_Map_Bindt T U;
    ktmodf_traverse_compat :> Compat_Traverse_Bindt T U;
    ktmodf_bind_compat :> Compat_Bind_Bindt T U;
  }.

Section instances.

  #[local] Instance
    TraversableMonadFull_TraversableMonad
    (T : Type -> Type)
    `{Monad_inst : TraversableMonad T} :
  TraversableMonadFull T
    (Map_inst := Map_Bindt T T)
    (Traverse_inst := Traverse_Bindt T T)
    (Bind_inst := Bind_Bindt T T)
  :=
  {| ktmf_ktm := _
  |}.

  #[local] Instance TraversableRightModuleFull_TraversableRightModule
    (W : Type) (T : Type -> Type) (U : Type -> Type)
    `{Module_inst : TraversableRightModule T U} :
    TraversableRightModuleFull T U
    (Map_T_inst := Map_Bindt T T)
    (Traverse_T_inst := Traverse_Bindt T T)
    (Bind_T_inst := Bind_Bindt T T)
    (Map_U_inst := Map_Bindt T U)
    (Traverse_U_inst := Traverse_Bindt T U)
    (Bind_U_inst := Bind_Bindt T U) :=
    {| ktmodf_kmond := _;
    |}.

  #[local] Instance TraversableRightModuleFull_TraversableMonadFull
    (T : Type -> Type)
    `{Monad_inst : TraversableMonadFull T} :
    TraversableRightModuleFull T T.
  Proof.
    constructor.
    - typeclasses eauto.
    - apply TraversableRightModule_TraversableMonad.
      apply ktmf_ktm.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
  Qed.

End instances.


