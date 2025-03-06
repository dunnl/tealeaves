From Tealeaves Require Export
  Classes.Categorical.DecoratedFunctorPoly
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.DecoratedFunctorPoly
  CategoricalToKleisli.DecoratedFunctorPoly
  (* CategoricalToKleisli.DecoratedFunctorPoly*)
  Classes.Monoid
  Functors.List
  Functors.Writer
  Functors.List_Telescoping_General.

Import Monoid.Notations.
Import Product.Notations.

#[local] Generalizable Variables ϕ T W G A B C D F M.

Section dfunp_to_dfun.

  Context
    {T: Type -> Type -> Type}
    `{DecoratedFunctorPoly T}.

  #[export] Instance Mapd_of_Mapdp {B}: Mapd (list B) (T B) :=
    fun V1 V2 ρ => mapdp  (T := T) (extract (W := prod (list B)) (A := B)) ρ.

  #[export] Instance DFUN_of_DFUNP {B}: DecoratedFunctor (list B) (T B).
  Proof.
    constructor.
    - intros.
      unfold_ops @Mapd_of_Mapdp.
      rewrite kdfunp_mapdp1.
      reflexivity.
    - intros.
      unfold_ops @Mapd_of_Mapdp.
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


Section dfunp_to_dfun_bin.

  Context
    {T: Type -> Type -> Type}
    `{DecoratedFunctorPoly T}.

  #[export] Instance MapdB_of_Mapdp {V}: MapdZ (fun B => T B V) :=
    fun A B ρ => mapdp (T := T) ρ (extract).

  #[export] Instance DFUNCI_of_DFUNP {V}: DecoratedFunctorZ (fun B => T B V).
  Proof.
    constructor.
    - unfold_ops @MapdB_of_Mapdp.
      intros.
      apply kdfunp_mapdp1.
    - intros.
      unfold_ops @MapdB_of_Mapdp.
      rewrite kdfunp_mapdp2.
      fequal.
  Qed.

End dfunp_to_dfun_bin.

(* Relating Mono to Poly *)
Section relating.

  Context
    `{Categorical.DecoratedFunctorPoly.DecoratedFunctorPoly T}.


  Import CategoricalToKleisli.DecoratedFunctorPoly.DerivedOperations.
  Import CategoricalToKleisli.DecoratedFunctorPoly.DerivedInstances.

  Definition rename_binders
    {B1 V1 B2: Type}
      (ρ: list B1 * B1 -> B2)
    := mapdz (T := fun B => T B V1) ρ.

  Context
    {B1 V1 B2 V2: Type}
    {ρ: list B1 * B1 -> B2}
    {σ: list B1 * V1 -> V2}
    (t: T B1 V1).

  Lemma mapdt_decompose:
    mapdp ρ σ t =
      rename_binders ρ (mapd σ t).
  Proof.
    unfold rename_binders.
    unfold_ops @MapdB_of_Mapdp.
    unfold_ops @Mapd_of_Mapdp.
    compose near t on right.
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

