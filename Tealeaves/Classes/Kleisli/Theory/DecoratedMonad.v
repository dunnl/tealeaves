From Tealeaves Require Export
  Classes.Kleisli.DecoratedMonad
  Classes.Kleisli.Theory.Monad.

Import DecoratedMonad.Notations.
Import Kleisli.Comonad.Notations.
Import Kleisli.Monad.Notations.
Import Product.Notations.

#[local] Generalizable Variables W T U A B C.

Class DecoratedMonadFull
  (W: Type)
  (T: Type -> Type)
  `{ret_inst: Return T}
  `{Bindd_inst: Bindd W T T}
  `{Mapd_inst: Mapd W T}
  `{Bind_inst: Bind T T}
  `{Map_inst: Map T}
  `{op: Monoid_op W} `{unit: Monoid_unit W}
  :=
  { kmondf_kmond :> DecoratedMonad W T;
    kmondf_map_compat :> Compat_Map_Bindd W T T;
    kmondf_mapd_compat :> Compat_Mapd_Bindd W T T;
    kmondf_bind_compat :> Compat_Bind_Bindd W T T;
  }.

Class DecoratedRightModuleFull
  (W: Type)
  (T: Type -> Type)
  (U: Type -> Type)
  `{ret_inst: Return T}
  `{Bindd_T_inst: Bindd W T T}
  `{Bindd_U_inst: Bindd W T U}
  `{Mapd_T_inst: Mapd W T}
  `{Mapd_U_inst: Mapd W U}
  `{Bind_T_inst: Bind T T}
  `{Bind_U_inst: Bind T U}
  `{Map_T_inst: Map T}
  `{Map_U_inst: Map U}
  `{op: Monoid_op W}
  `{unit: Monoid_unit W}
  :=
  { kmoddf_kmond :> DecoratedMonadFull W T;
    kmoddf_mod :> DecoratedRightModule W T U;
    kmoddf_map_compat :> Compat_Map_Bindd W T U;
    kmoddf_mapd_compat :> Compat_Mapd_Bindd W T U;
    kmoddf_bind_compat :> Compat_Bind_Bindd W T U;
  }.

Section MonadFull.

  #[local] Instance DecoratedMonadFull_DecoratedMonad
    (W: Type) (T: Type -> Type)
    `{Monad_inst: DecoratedMonad W T} :
  DecoratedMonadFull W T
    (Map_inst := Map_Bindd W T T)
    (Mapd_inst := Mapd_Bindd W T T)
    (Bind_inst := Bind_Bindd W T T)
  :=
  {| kmondf_kmond := _
  |}.

  #[local] Instance DecoratedRightModuleFull_DecoratedRightModule
    (W: Type) (T: Type -> Type) (U: Type -> Type)
    `{Module_inst: DecoratedRightModule W T U} :
    DecoratedRightModuleFull W T U
      (Map_T_inst := Map_Bindd W T T)
      (Map_U_inst := Map_Bindd W T U)
      (Mapd_T_inst := Mapd_Bindd W T T)
      (Mapd_U_inst := Mapd_Bindd W T U)
      (Bind_T_inst := Bind_Bindd W T T)
      (Bind_U_inst := Bind_Bindd W T U) :=
    {| kmoddf_kmond := _
    |}.

  #[export] Instance MonadFull_DecoratedMonadFull :
    MonadFull T :=
    {| kmonf_kmon := _ |}.


  #[local] Instance DecoratedRightModuleFull_DecoratedMonadFull
    (W: Type) (T: Type -> Type)
    `{Monad_inst: DecoratedMonadFull W T} :
    DecoratedRightModuleFull W T T.
  Proof.
    constructor.
    - typeclasses eauto.
    - apply DecoratedRightModule_DecoratedMonad.
      apply kmondf_kmond.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
  Qed.

End MonadFull.

