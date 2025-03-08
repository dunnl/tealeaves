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

Class Compat_Mapdp_Categorical
    (T: Type -> Type -> Type)
    `{Map_T: Map2 T}
    `{Decorate_T: DecoratePoly T}
    `{Mapdp_T: MapdPoly T} :=
  compat_mapdp_categorical:
    Mapdp_T = @DerivedOperations.Mapdp_Categorical T Map_T Decorate_T.

#[export] Instance Mapdp_Categorical_Self
  (T: Type -> Type -> Type)
  `{Map2 T}
  `{DecoratePoly T}:
  @Compat_Mapdp_Categorical T _ _ (@DerivedOperations.Mapdp_Categorical T _ _).
Proof.
  reflexivity.
Qed.

Lemma mapdp_to_categorical {T}
    `{Map_T: Map2 T}
    `{Decorate_T: DecoratePoly T}
    `{Mapdp_T: MapdPoly T}
    `{Compat: Compat_Mapdp_Categorical T}:
  forall (B1 B2 V1 V2: Type)
      (ρ: list B1 * B1 -> B2)
      (σ: list B1 * V1 -> V2)
      (t: T B1 V1),
      mapdp ρ σ t = map2 ρ σ (decp t).
Proof.
  now rewrite compat_mapdp_categorical.
Qed.

Module DerivedInstances.

  Import DerivedOperations.

  Section context.

    Context
      `{Categorical.DecoratedFunctorPoly.DecoratedFunctorPoly T}.

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
        unfold kc_dz.
        unfold kc_dfunp.
        reassociate -> on left.
        rewrite cobind_Z_spec.
        reflexivity.
    Qed.
  End context.

End DerivedInstances.

