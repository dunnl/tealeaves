
Class DecoratedTraversableMonadFull
  (W : Type)
  (T : Type -> Type)
  `{op : Monoid_op W}
  `{unit : Monoid_unit W}
  `{ret_inst : Return T}
  `{Map_inst : Map T}
  `{Mapd_inst : Mapd W T}
  `{Traverse_inst : Traverse T}
  `{Bind_inst : Bind T T}
  `{Mapdt_inst : Mapdt W T}
  `{Bindd_inst : Bindd W T T}
  `{Bindt_inst : Bindt T T}
  `{Binddt_inst : Binddt W T T}
  :=
  { kdtmf_kmond :> DecoratedTraversableMonad W T;
    kdtmf_map_compat :> Compat_Map_Binddt W T T;
    kdtmf_mapd_compat :> Compat_Mapd_Binddt W T T;
    kdtmf_traverse_compat :> Compat_Traverse_Binddt W T T;
    kdtmf_bind_compat :> Compat_Bind_Binddt W T T;
    kdtmf_mapdt_compat :> Compat_Mapdt_Binddt W T T;
    kdtmf_bindd_compat :> Compat_Bindd_Binddt W T T;
    kdtmf_bindt_compat :> Compat_Bindt_Binddt W T T;
  }.

Class DecoratedTraversableRightModuleFull
  (W : Type)
  (T : Type -> Type)
  (U : Type -> Type)
  `{op : Monoid_op W}
  `{unit : Monoid_unit W}
  `{ret_inst : Return T}
  `{Map_T_inst : Map T}
  `{Mapd_T_inst : Mapd W T}
  `{Traverse_T_inst : Traverse T}
  `{Bind_T_inst : Bind T T}
  `{Mapdt_T_inst : Mapdt W T}
  `{Bindd_T_inst : Bindd W T T}
  `{Bindt_T_inst : Bindt T T}
  `{Binddt_T_inst : Binddt W T T}
  `{Map_U_inst : Map U}
  `{Mapd_U_inst : Mapd W U}
  `{Traverse_U_inst : Traverse U}
  `{Bind_U_inst : Bind T U}
  `{Mapdt_U_inst : Mapdt W U}
  `{Bindd_U_inst : Bindd W T U}
  `{Bindt_U_inst : Bindt T U}
  `{Binddt_U_inst : Binddt W T U}
  :=
  { kdtmodf_kmond :> DecoratedTraversableMonadFull W T;
    kdtmodf_mod :> DecoratedTraversableRightModule W T U;
    kdtmodf_map_compat :> Compat_Map_Binddt W T U;
    kdtmodf_mapd_compat :> Compat_Mapd_Binddt W T U;
    kdtmodf_traverse_compat :> Compat_Traverse_Binddt W T U;
    kdtmodf_bind_compat :> Compat_Bind_Binddt W T U;
    kdtmodf_mapdt_compat :> Compat_Mapdt_Binddt W T U;
    kdtmodf_bindd_compat :> Compat_Bindd_Binddt W T U;
    kdtmodf_bindt_compat :> Compat_Bindt_Binddt W T U;
  }.

Section MonadFull.

  #[local] Instance
    DecoratedTraversableMonadFull_DecoratedTraversableMonad
    (W : Type) (T : Type -> Type)
    `{Monad_inst : DecoratedTraversableMonad W T} :
  DecoratedTraversableMonadFull W T
    (Map_inst := Map_Binddt W T T)
    (Mapd_inst := Mapd_Binddt W T T)
    (Traverse_inst := Traverse_Binddt W T T)
    (Bind_inst := Bind_Binddt W T T)
    (Mapdt_inst := Mapdt_Binddt W T T)
    (Bindd_inst := Bindd_Binddt W T T)
    (Bindt_inst := Bindt_Binddt W T T)
  :=
  {| kdtmf_kmond := _
  |}.

  #[local] Instance DecoratedTraversableRightModuleFull_DecoratedTraversableRightModule
    (W : Type) (T : Type -> Type) (U : Type -> Type)
    `{Module_inst : DecoratedTraversableRightModule W T U} :
    DecoratedTraversableRightModuleFull W T U
    (Map_T_inst := Map_Binddt W T T)
    (Mapd_T_inst := Mapd_Binddt W T T)
    (Traverse_T_inst := Traverse_Binddt W T T)
    (Bind_T_inst := Bind_Binddt W T T)
    (Mapdt_T_inst := Mapdt_Binddt W T T)
    (Bindd_T_inst := Bindd_Binddt W T T)
    (Bindt_T_inst := Bindt_Binddt W T T)
    (Map_U_inst := Map_Binddt W T U)
    (Mapd_U_inst := Mapd_Binddt W T U)
    (Traverse_U_inst := Traverse_Binddt W T U)
    (Bind_U_inst := Bind_Binddt W T U)
    (Mapdt_U_inst := Mapdt_Binddt W T U)
    (Bindd_U_inst := Bindd_Binddt W T U)
    (Bindt_U_inst := Bindt_Binddt W T U) :=
    {| kdtmodf_kmond := _
    |}.

  #[local] Instance DecoratedTraversableRightModuleFull_DecoratedTraversableMonadFull
    (W : Type) (T : Type -> Type)
    `{Monad_inst : DecoratedTraversableMonadFull W T} :
    DecoratedTraversableRightModuleFull W T T.
  Proof.
    constructor.
    - typeclasses eauto.
    - apply DecoratedTraversableRightModule_DecoratedTraversableMonad.
      apply kdtmf_kmond.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
  Qed.

End MonadFull.
