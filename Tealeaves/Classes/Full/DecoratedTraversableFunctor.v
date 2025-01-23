
(** *** "Full" typeclass *)
(******************************************************************************)
Class DecoratedTraversableFunctorFull
  (E : Type) (T : Type -> Type)
  `{Map_inst: Map T}
  `{Mapd_inst: Mapd E T}
  `{Traverse_inst: Traverse T}
  `{Mapdt_inst: Mapdt E T} :=
  { kdtfunf_dtf :> DecoratedTraversableFunctor E T;
    kdtfunf_map_compat :> Compat_Map_Mapdt;
    kdtfunf_mapd_compat :> Compat_Mapd_Mapdt;
    kdtfunf_traverse_compat :> Compat_Traverse_Mapdt;
  }.


