From Tealeaves Require Export
  Classes.Categorical.DecoratedFunctorPoly
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.DecoratedFunctorPoly
  CategoricalToKleisli.DecoratedFunctorPoly
  Classes.Monoid
  Functors.List
  Functors.Writer.

Import Monoid.Notations.
Import Product.Notations.

#[local] Generalizable Variables ϕ T W G A B C D F M.

Module ToMono1.

  Section dfunp_to_dfun.

    Context
      {T: Type -> Type -> Type}
        `{Kleisli.DecoratedFunctorPoly.DecoratedFunctorPoly T}.

    #[export] Instance Mapd_of_Mapdp1 {B}: Mapd (list B) (T B) :=
      fun V1 V2 ρ => mapdp  (T := T) (extract (W := prod (list B)) (A := B)) ρ.

    #[export] Instance DecoratedFunctor_of_DecoratedFunctorPoly1 {B}:
      DecoratedFunctor (list B) (T B).
    Proof.
      constructor.
      - intros.
        unfold_ops @Mapd_of_Mapdp1.
        rewrite kdfunp_mapdp1.
        reflexivity.
      - intros.
        unfold_ops @Mapd_of_Mapdp1.
        rewrite kdfunp_mapdp2.
        fequal.
        { unfold kc_dz.
          ext [w b].
          cbn.
          reflexivity.
        }
        { unfold kc_dfunp.
          ext [w b].
          unfold mapdt_ci.
          unfold Mapdt_CommIdem_list_prefix.
          rewrite kdtfci_mapdt1_list_prefix.
          reflexivity.
        }
    Qed.

  End dfunp_to_dfun.

End ToMono1.

Module ToMono2.

  Section dfunp_to_dfun_bin.

    Context
      {T: Type -> Type -> Type}
        `{DecoratedFunctorPoly T}.

    #[export] Instance MapdZ_of_Mapdp2 {V}: MapdZ (fun B => T B V) :=
      fun A B ρ => mapdp (T := T) ρ (extract).

    #[export] Instance DecoratedFunctorZ_of_DecoratedFunctorPoly2 {V}: DecoratedFunctorZ (fun B => T B V).
    Proof.
      constructor.
      - unfold_ops @MapdZ_of_Mapdp2.
        intros.
        apply kdfunp_mapdp1.
      - intros.
        unfold_ops @MapdZ_of_Mapdp2.
        rewrite kdfunp_mapdp2.
        fequal.
    Qed.

  End dfunp_to_dfun_bin.

End ToMono2.

(* Relating Mono to Poly *)
Section relating.

  Context
    `{Kleisli.DecoratedFunctorPoly.DecoratedFunctorPoly T}.

  Import ToMono1.
  Import ToMono2.

  Definition rename_binders
    {B1 V1 B2: Type}
    (ρ: list B1 * B1 -> B2)
    := mapdz (T := fun B => T B V1) ρ.

  Context
    {B1 V1 B2 V2: Type}
      {ρ: list B1 * B1 -> B2}
      {σ: list B1 * V1 -> V2}.

  Lemma mapd_decompose:
    mapdp ρ σ =
      rename_binders ρ ∘ mapd σ.
  Proof.
    unfold rename_binders.
    unfold_ops @MapdZ_of_Mapdp2.
    unfold_ops @Mapd_of_Mapdp1.
    rewrite (kdfunp_mapdp2).
    fequal.
    - ext [w b].
      unfold kc_dz.
      compose near (w, b).
      fold_Z.
      change (@extract (prod (list B1)) (Extract_reader (list B1)) B1)
        with (@extract Z _ B1).
      rewrite (com_map_extr_cojoin (W := Z)).
      reflexivity.
    - unfold kc_dfunp.
      ext [w v].
      cbn.
      reflexivity.
  Qed.

End relating.

(* Relating Categorical Mono to Kleisli Mono *)
From Tealeaves Require
  Import CategoricalToKleisli.DecoratedFunctor.

Section relating.

  Context
    `{Map_T: Map2 T}
      `{Decorate_T: DecoratePoly T}
      `{MapdPoly_T: MapdPoly T}
      `{Compat1: ! Compat_Mapdp_Categorical T}
      `{! Categorical.DecoratedFunctorPoly.DecoratedFunctorPoly T}
      `{! Kleisli.DecoratedFunctorPoly.DecoratedFunctorPoly T}.

  Import Categorical.DecoratedFunctorPoly.ToMono.
  Import ToMono1.

  #[export] Instance Compat_Mapd_Categorical_Poly1 {B}:
    Compat_Mapd_Categorical (list B) (T B).
  Proof.
    unfold Compat_Mapd_Categorical.
    ext X Y f t.
    unfold Mapd_of_Mapdp1.
    unfold DerivedOperations.Mapd_Categorical.
    unfold_ops @Map2_1.
    unfold dec.
    unfold_ops @Decorate_PolyVar.
    rewrite mapdp_to_categorical.
    reassociate <- on right.
    rewrite fun2_map_map.
    reflexivity.
  Qed.

End relating.
