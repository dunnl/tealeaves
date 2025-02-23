From Tealeaves Require Import
  Classes.Categorical.DecoratedTraversableMonadPoly
  Classes.Kleisli.DecoratedTraversableMonadPoly.

#[local] Generalizable Variables T.

(** * Kleisli DTMs from Categorical DTMs *)
(**********************************************************************)

(** ** Derived Operations *)
(**********************************************************************)
Module DerivedOperations.

  #[export] Instance Binddt_Categorical
    (T: Type -> Type -> Type)
    `{Map2 T}
    `{DecoratePoly T}
    `{ApplicativeDist2 T}
    `{forall B, Join (T B)}: Substitute T T :=
    fun (B1 V1 B2 V2: Type)
      (G : Type -> Type)
      `{Map_G: Map G} `{Pure_G: Pure G} `{Mult_G: Mult G}
      (ρ: list B1 * B1 -> G B2) (* rename binders *)
      (σ: list B1 * V1 -> G (T B2 V2)) (* insert subtrees *)
    => (map (F := G) join ∘ dist2 (T := T) (G := G) ∘ map2 ρ σ ∘ decp (F := T) (B := B1) (V := V1)).

End DerivedOperations.

Module DerivedInstances.

  Import DerivedOperations.

  Context
    `{Categorical.DecoratedTraversableMonadPoly.DecoratedTraversableMonadPoly T}.

  Instance: Kleisli.DecoratedTraversableMonadPoly.DecoratedTraversableMonadPoly T.
  Proof.
    constructor; intros.
    - unfold substitute, Binddt_Categorical.
      reassociate -> on left.
      rewrite xxx_dec_ret.
      reassociate <- on left.
      fequal.
      reassociate ->.
      rewrite xxx_map_ret.
      reassociate <- on left.
      change σ with (id ∘ σ) at 2.
      fequal.
      reassociate -> on left.
      rewrite (xxx_dist2_ret (G := G) (T := T) (B := B2) (V := T B2 A2)).
      rewrite fun_map_map.
      setoid_rewrite mon_join_ret.
      rewrite fun_map_id.
      reflexivity.
    - unfold substitute, Binddt_Categorical.
      rewrite <- fun2_map21_map2.
      (* unfold_ops @Map2_1. *)
      reassociate <-.
      reassociate -> on left.
      rewrite dfunp_dec_extract.
      change (?x ∘ id) with x.
      rewrite dist2_unit.
      change (?x ∘ id) with x.
      unfold_ops Map_I.
      apply mon_join_map_ret.
    - unfold substitute.
      unfold Binddt_Categorical.
      repeat reassociate <- on left.
      rewrite fun_map_map.
      fequal.
      admit.
    - unfold substitute.
      unfold Binddt_Categorical.
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

End DerivedInstances.

