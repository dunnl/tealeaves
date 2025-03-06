From Tealeaves Require Import
  Classes.Categorical.DecoratedFunctorPoly
  Classes.Kleisli.DecoratedFunctorPoly
  Functors.List.

#[local] Generalizable Variables T.

Import Functor2.Notations.

(** * Kleisli DTMs from Categorical DTMs *)
(**********************************************************************)

(** ** Derived Operations *)
(**********************************************************************)
Module DerivedOperations.

  #[export] Instance Mapdp_Categorical
    (T: Type -> Type -> Type)
    `{Map2 T}
    `{DecoratePoly T}: MapdPoly T :=
    fun (B1 B2 V1 V2: Type)
      (ρ: list B1 * B1 -> B2) (* rename binders *)
      (σ: list B1 * V1 -> V2) (* insert subtrees *)
    => map2 ρ σ ∘ decp (F := T) (B := B1) (V := V1).

End DerivedOperations.

Module DerivedInstances.

  Import DerivedOperations.

  Section context.

    Context
      `{Categorical.DecoratedFunctorPoly.DecoratedFunctorPoly T}.

    Print Instances Traverse.
    #[export] Instance: Kleisli.DecoratedFunctorPoly.DecoratedFunctorPoly T.
    Proof.
      constructor; intros.
      - unfold mapdp, Mapdp_Categorical.
        rewrite dfunp_dec_extract.
        reflexivity.
      - unfold mapdp, Mapdp_Categorical.
        reassociate <- on left.
        reassociate -> near (map2 ρ1 σ1).
        rewrite polydecnat.
        repeat reassociate <- on left.
        rewrite (fun2_map_map).
        reassociate -> on left.
        rewrite dfunp_dec_dec.
        reassociate <- on left.
        rewrite fun2_map_map.
        fequal.
        fequal.
        unfold kc_dfunp.
        ext [ctx a].
        unfold mapdt_ci.
        unfold Mapdt_CommIdem_list_prefix.
        unfold compose.
        cbn.
        unfold mapdt_list_prefix.
        rewrite map_to_traverse.
        reflexivity.
    Qed.
  End context.

End DerivedInstances.

