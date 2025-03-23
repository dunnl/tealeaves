From Tealeaves Require Import
  Classes.Categorical.DecoratedMonadPoly
  Classes.Kleisli.DecoratedMonadPoly.

#[local] Generalizable Variables T.

Import Monoid.Notations.

(** * Kleisli DTMs from Categorical DTMs *)
(**********************************************************************)

(** ** Derived Operations *)
(**********************************************************************)
Module DerivedOperations.

  Print BinddP.
  #[export] Instance BinddP_Categorical
    (T: Type -> Type -> Type)
    `{Map2 T}
    `{DecoratePoly T}
    `{forall B, Join (T B)}: BinddP T :=
    fun (B1 B2 V1 V2: Type)
      (ρ: list B1 * B1 -> B2)
      (σ: list B1 * V1 -> T B2 V2)
    => (join ∘ map2 ρ σ ∘ decp (F := T) (B := B1) (V := V1)).

End DerivedOperations.

Module DerivedInstances.

  Import DerivedOperations.

  Section section.

  Context
    `{Categorical.DecoratedMonadPoly.DecoratedMonadPoly T}.

  #[export] Instance: Kleisli.DecoratedMonadPoly.DecoratedMonadPoly T.
  Proof.
    constructor; intros.
    - unfold binddp, BinddP_Categorical.
      reassociate -> on left.
      rewrite xxx_dec_ret.
      reassociate <- on left.
      fequal.
      reassociate ->.
      unfold_compose_in_compose.
      rewrite xxx_map_ret.
      reassociate <- on left.
      change σ with (id ∘ σ) at 2.
      fequal.
      setoid_rewrite mon_join_ret.
      reflexivity.
    - unfold binddp, BinddP_Categorical.
      rewrite <- fun2_map21_map2.
      reassociate <-.
      reassociate -> on left.
      rewrite dfunp_dec_extract.
      change (?x ∘ id) with x.
      apply mon_join_map_ret.
    - unfold binddp, BinddP_Categorical.
      repeat reassociate <- on left.
      change_left (join ∘ map2 ρ2 σ2 ∘ (decp ∘ join) ∘ map2 ρ1 σ1 ∘ decp).
      rewrite xxx_dec_join.
      repeat reassociate <- on left.
      change_left (join ∘ map2 ρ2 σ2 ∘ join ∘ map2 id (shift2 ∘ map_snd decp) ∘ (decp ∘ map2 ρ1 σ1) ∘ decp).
      rewrite polydecnat.
      repeat reassociate <- on left.
      reassociate -> on left.
      rewrite dfunp_dec_dec.
      change_left (join ∘ map2 ρ2 σ2 ∘ join ∘
                     (map2 id (shift2 ∘ map_snd decp) ∘ map2 (map ρ1) (map2 ρ1 σ1))
                     ∘ (map2 cojoin cojoin_Z2 ∘ decp)).
      rewrite fun2_map_map.
      repeat reassociate <- on left.
      change_left ( join ∘ map2 ρ2 σ2 ∘ join ∘
                      (map2 (id ∘ map (F := Z) ρ1) (shift2 ∘ map_snd decp ∘ map2 ρ1 σ1) ∘
                         map2 (cojoin (W := Z)) cojoin_Z2) ∘ decp).
      rewrite fun2_map_map.
      change (id ∘ ?f) with f.
      change_left (join ∘ (map2 ρ2 σ2 ∘ join) ∘ map2 (map (F := Z) ρ1 ∘ (cojoin (W := Z)))
                     (shift2 ∘ map_snd decp ∘ map2 ρ1 σ1 ∘ cojoin_Z2) ∘ decp).
      rewrite xxx_map_join.
      reassociate <- on left.
      rewrite mon_join_join.
      fequal.
      repeat reassociate ->.
      fequal.
      repeat reassociate <-.
      unfold_compose_in_compose.
      rewrite (fun2_map21_map2 (F := T)).
      rewrite fun2_map_map.
      fequal.
      + fequal.
        unfold_ops @Map_Z Cojoin_Z @Cobind_Z.
        unfold compose.
        ext [l b]. cbn.
        unfold id. fequal.
        now rewrite mapd_list_prefix_spec.
      + unfold kc_dmp.
        ext [ctx v].
        unfold compose.
        cbn.
        unfold id.
        unfold binddp, BinddP_Categorical.
        fequal.
        admit.

        unfold preincr, incr, compose.
        fereflexivity.
        admit
      change_left (join ∘ join ∘ map2 ρ2 (map2 ρ2 σ2) ∘ map2 (map ρ1 ∘ cojoin (W := Z))
                     (shift2 ∘ map_snd decp ∘ map2 ρ1 σ1 ∘ cojoin_Z2) ∘ decp).
      reassociate -> on left.

      change_left (join ∘ map2 ρ2 σ2 ∘ join ∘ (map2 (id ∘ map ρ1) (shift2 ∘ map_snd decp ∘ map2 ρ1 σ1)
                     ∘ map2 (cojoin (W := Z)) cojoin_Z2) ∘ decp).

      unfold kc_dmp.
      unfold binddp, BinddP_Categorical.
      change (

      unfold bindp.
      Search join map2.
      unfold cobind, Cobind_Z.
      unfold mapd_Z.
      admit.
    - unfold substitute.
      unfold Substitute_Categorical.
      repeat reassociate <- on left.
      rewrite appmor_natural_pf.
      reassociate -> near dist2.
      unfold compose at 9.
      rewrite <- (dist2_morph (T := T) (ϕ := ϕ)).
      reassociate <- on left.
      reassociate -> near (map2 ρ σ).
      rewrite fun2_map_map.
      reflexivity.
  Admitted.

  End section.

End DerivedInstances.
