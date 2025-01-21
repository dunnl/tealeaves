

Class TraversableFunctorFull (T : Type -> Type)
  `{Traverse_inst : Traverse T}
  `{Map_inst : Map T} :=
  { trff_trf :> TraversableFunctor T;
    trff_map_compat :> Compat_Map_Traverse T;
  }.

(*
#[local] Instance TraversableFunctorFull_Intro
  (T : Type -> Type)
  `{Traverse_inst : Traverse T}
  `{Map_inst : Map T}
  `{Traverse_compat : Compat_Map_Traverse T}
  `{! TraversableFunctor T}:
  TraversableFunctorFull T :=
  ltac:(constructor; typeclasses eauto).
*)
