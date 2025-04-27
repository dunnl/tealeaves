From Tealeaves Require Import
  Classes.Categorical.RightComodule
  Classes.Kleisli.DecoratedFunctorZ.

#[local] Generalizable Variables F.

(** * Categorical Z-Decorated Functors to Kleisli Z-Decorated Functors *)
(**********************************************************************)

(** ** Derived <<mapdz>> Operation *)
(**********************************************************************)
Module DerivedOperations.

  #[export] Instance Mapdz_Categorical
    (F: Type -> Type)
    `{Map_F: Map F}
    `{Decorate_Z_F: RightCoaction F Z}: MapdZ F :=
  fun A B (f: Z A -> B) => map (F := F) f ∘ right_coaction F.

End DerivedOperations.

(** ** Derived co-Kleisli Laws *)
(**********************************************************************)
Module DerivedInstances.

  Import DerivedOperations.

  Section with_functor.

    Context
      (F: Type -> Type)
      `{Map F}
      `{RightCoaction F Z}
      `{! Classes.Categorical.RightComodule.RightComodule F Z}.

    Instance DecoratedFunctorZ_Kleisli_from_Categorical: Kleisli.DecoratedFunctorZ.DecoratedFunctorZ F.
    Proof.
      constructor.
      - intros.
        unfold_ops @Mapdz_Categorical.
        apply rcom_map_extr_coaction.
      - intros.
        unfold_ops @Mapdz_Categorical.
        unfold kc_dz.
        unfold cobind.
        unfold Cobind_Z.
        reassociate <- on left.
        reassociate -> near (map ρ1).
        rewrite <- natural.
        reassociate -> on left.
        reassociate -> on left.
        rewrite (rcom_coaction_coaction (W := Z) (F := F)).
        reassociate <- on left.
        reassociate <- on left.
        unfold_ops @Map_compose.
        unfold_compose_in_compose.
        rewrite fun_map_map.
        rewrite fun_map_map.
        fequal.
        fequal.
        ext [l b].
        unfold compose; cbn.
        rewrite mapd_list_prefix_spec.
        reflexivity.
    Qed.

  End with_functor.
End DerivedInstances.
