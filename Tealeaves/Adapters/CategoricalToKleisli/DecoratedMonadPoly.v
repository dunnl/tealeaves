From Tealeaves Require Import
  Classes.Categorical.DecoratedMonadPoly
  Classes.Kleisli.DecoratedMonadPoly.

#[local] Generalizable Variables T.

Import Monoid.Notations.
Import Product.Notations.

(** * Kleisli DTMs from Categorical DTMs *)
(**********************************************************************)

(** ** Derived Operations *)
(**********************************************************************)
Module DerivedOperations.

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

(** ** Derived Instances *)
(**********************************************************************)
Module DerivedInstances.

  Import DerivedOperations.

  Section section.

  Context
    `{Categorical.DecoratedMonadPoly.DecoratedMonadPoly T}.

  #[local] Arguments ret (T)%function_scope {Return} {A}%type_scope _.

  Lemma binddp_ret {B1 B2 V1 V2}:
    forall (ρ: list B1 * B1 -> B2)
      (σ: list B1 * V1 -> T B2 V2),
      binddp ρ σ ∘ ret (T B1) = σ ∘ ret ((list B1) ×).
  Proof.
    intros.
    unfold binddp, BinddP_Categorical.
    reassociate -> on left.
    rewrite dmp_dec_ret.
    reassociate <- on left.
    reassociate -> near (ret (T (Z B1))).
    unfold_compose_in_compose.
    rewrite dmp_map_ret.
    reassociate <- on left.
    setoid_rewrite mon_join_ret.
    reflexivity.
  Qed.

  Lemma binddp_id {B V}:
    binddp extract (ret (T B) ∘ extract) = @id (T B V).
  Proof.
    unfold binddp, BinddP_Categorical.
    rewrite <- fun2_map21_map2.
    reassociate <-.
    reassociate -> on left.
    rewrite dfunp_dec_extract.
    change (?x ∘ id) with x.
    apply mon_join_map_ret.
  Qed.

  Lemma binddp_composition_law:
    forall {B1 B2 B3 V1 V2 V3: Type}
      (ρ1: list B1 * B1 -> B2)
      (ρ2: list B2 * B2 -> B3)
      (σ1: list B1 * V1 -> T B2 V2)
      (σ2: list B2 * V2 -> T B3 V3),
      map2 (ρ2 ∘ map ρ1 ∘ cojoin (W := Z)) (join ∘ (map2 ρ2 σ2 ∘ (shift2 ∘ map_snd decp) ∘ map2 ρ1 σ1 ∘ cojoin_L)) =
        map2 (ρ2 ∘ cobind (W := Z) ρ1) (kc_dmp ρ1 σ1 ρ2 σ2).
  Proof.
    intros.
    unfold kc_dmp.
    rewrite cobind_Z_spec.
    fequal.
    ext [ctx v].
    unfold binddp, BinddP_Categorical.
    unfold compose.
    cbn.
    unfold id.
    unfold shift2.
    unfold compose.
    unfold strength2.
    compose near (decp (σ1 (ctx, v))) on left.
    rewrite fun2_map_map.
    compose near (decp (σ1 (ctx, v))) on left.
    rewrite fun2_map_map.
    rewrite mapd_list_prefix_spec.
    unfold preincr.
    reflexivity.
  Qed.

  #[export] Instance: Kleisli.DecoratedMonadPoly.DecoratedMonadPoly T.
  Proof.
    constructor; intros.
    - apply binddp_ret.
    - apply binddp_id.
    - unfold binddp, BinddP_Categorical.
      repeat reassociate <- on left.
      change_left (join ∘ map2 ρ2 σ2 ∘ (decp ∘ join) ∘ map2 ρ1 σ1 ∘ decp).
      rewrite dmp_dec_join.
      repeat reassociate <- on left.
      reassociate -> near (join (T := T (Z B2))).
      rewrite dmp_map_join.
      reassociate <- on left.
      rewrite mon_join_join.
      reassociate -> near (map2 ρ1 σ1).
      rewrite polydecnat.
      reassociate <- on left.
      reassociate -> on left.
      rewrite dfunp_dec_dec.
      reassociate -> near (map2 id (shift2 ∘ map_snd decp)).
      rewrite fun2_map_map.
      reassociate -> near (map2 (map ρ1) (map2 ρ1 σ1)).
      rewrite fun2_map_map.
      reassociate <- on left.
      reassociate -> near (map2 cojoin cojoin_L).
      rewrite fun2_map_map.
      reassociate -> near (map2 (ρ2 ∘ id ∘ map ρ1 ∘ cojoin (W := Z))
                            (map2 ρ2 σ2 ∘ (shift2 ∘ map_snd decp) ∘ map2 ρ1 σ1 ∘ cojoin_L)).
      rewrite fun2_map21_map2.

      reassociate -> on right.
      setoid_rewrite <- (binddp_composition_law ρ1 ρ2 σ1 σ2).
      reflexivity.
  Qed.

  End section.

End DerivedInstances.
