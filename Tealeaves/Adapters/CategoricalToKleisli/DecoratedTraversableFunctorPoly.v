From Tealeaves Require Import
  Classes.Categorical.DecoratedTraversableFunctorPoly
  Classes.Kleisli.DecoratedTraversableMonadPoly.

#[local] Generalizable Variables T.

Import Functor2.Notations.

(** * Kleisli DTMs from Categorical DTMs *)
(**********************************************************************)

(** ** Derived Operations *)
(**********************************************************************)
Module DerivedOperations.

  #[export] Instance Mapdtp_Categorical
    (T: Type -> Type -> Type)
    `{Map2 T}
    `{DecoratePoly T}
    `{ApplicativeDist2 T}: MapdtPoly T :=
    fun (B1 B2 V1 V2: Type)
      (G : Type -> Type)
      `{Map_G: Map G} `{Pure_G: Pure G} `{Mult_G: Mult G}
      (ρ: list B1 * B1 -> G B2) (* rename binders *)
      (σ: list B1 * V1 -> G V2) (* insert subtrees *)
    => (dist2 (T := T) (G := G) ∘ map2 ρ σ ∘ decp (F := T) (B := B1) (V := V1)).

End DerivedOperations.

Module DerivedInstances.

  Import DerivedOperations.

  Section context.

  Context
    `{Categorical.DecoratedTraversableFunctorPoly.DecoratedTraversableFunctorPoly T}.

  #[export] Instance: Kleisli.DecoratedTraversableFunctorPoly.DecoratedTraversableFunctorPoly T.
  Proof.
    constructor; intros.
    - unfold mapdtp, Mapdt_Categorical.
      reassociate -> on left.
      rewrite dfunp_dec_extract.
      rewrite dist2_unit.
      reflexivity.
    - unfold mapdtp, Mapdt_Categorical.
      rewrite <- fun_map_map.
      reassociate <- on left.
      reassociate <- on left.
      reassociate -> near dist2.
      rewrite <- dtfp_dist2_decpoly.
      2:{ admit. } (* Commutative idempotence issue *)
      reassociate <- on left.
      reassociate <- on left.
      reassociate -> near (map2 ρ1 σ1).
      rewrite polydecnat.
      repeat reassociate <- on left.
      rewrite <- (fun_map_map).
      reassociate -> near dist2.
      change (map (F := G1) (map2 (F := T) ρ2 σ2))
        with (map2 (F := G1 ○12 T) ρ2 σ2).
      setoid_rewrite (natural2 (Natural2 := dist2_natural)).
      reassociate <- on left.
      rewrite dist2_linear.
      reassociate -> near (map2 (map ρ1) (map2 ρ1 σ1)).
      rewrite (fun2_map_map).
      change_left
        (@map G1 Map_G (T (G2 B3) (G2 A3)) ((G2 ∘ T B3) A3) (@dist2 T H1 G2 Map_G0 Pure_G0 Mult_G0 B3 A3)
  ∘ @dist2 T H1 G1 Map_G Pure_G Mult_G (G2 B3) (G2 A3)
  ∘ (@map2 (T ○21 G1) (@Map21_compose G1 Map_G T H) (list B2 * B2) (list B2 * A2) (G2 B3) (G2 A3) ρ2 σ2
  ∘ @map2 T H (Z (list B1 * B1)) (Z2 (list B1 * B1) (list B1 * A1)) (G1 (Z B2)) ((G1 ∘ Z2 B2) A2)
      (@dist Z Dist_Z G1 Map_G Pure_G Mult_G B2 ∘ @map Z Map_Z (list B1 * B1) (G1 B2) ρ1)
      (@dist2 Z2 Dist2_Z2 G1 Map_G Pure_G Mult_G B2 A2
         ∘ @map2 Z2 Map2_Z2 (list B1 * B1) (list B1 * A1) (G1 B2) (G1 A2) ρ1 σ1)) ∘ @decp T H0 (list B1 * B1) (list B1 * A1) ∘ @decp T H0 B1 A1).
      unfold_ops @Map21_compose.
      rewrite fun2_map_map.
      unfold kc_dtfp.
      change_left
        (@map G1 Map_G (T (G2 B3) (G2 A3)) ((G2 ∘ T B3) A3) (@dist2 T H1 G2 Map_G0 Pure_G0 Mult_G0 B3 A3)
            ∘ @dist2 T H1 G1 Map_G Pure_G Mult_G (G2 B3) (G2 A3)
            ∘ (@map2 T H (Z (list B1 * B1)) (Z2 (list B1 * B1) (list B1 * A1)) (G1 (G2 B3)) (G1 (G2 A3))
            (@map G1 Map_G (list B2 * B2) (G2 B3) ρ2
               ∘ (@dist Z Dist_Z G1 Map_G Pure_G Mult_G B2 ∘ @map Z Map_Z (list B1 * B1) (G1 B2) ρ1))
            (@map G1 Map_G (list B2 * A2) (G2 A3) σ2
               ∘ (@dist2 Z2 Dist2_Z2 G1 Map_G Pure_G Mult_G B2 A2
                    ∘ @map2 Z2 Map2_Z2 (list B1 * B1) (list B1 * A1) (G1 B2) (G1 A2) ρ1 σ1))
            ∘ @decp T H0 (list B1 * B1) (list B1 * A1)) ∘ @decp T H0 B1 A1).
      repeat reassociate -> on left.
      rewrite dfunp_dec_dec.
      repeat reassociate <- on left.
      reassociate -> near (map2 cojoin cojoin_Z2).
      rewrite fun2_map_map.
      fequal.
      fequal.
      fequal.
      { unfold kc3_ci.
        unfold mapdt_ci.
        unfold Mapdt_CommIdem_Z.
        rewrite traverse_dist_Z.
        reflexivity.
      }
      ext [ctx a].
      unfold compose.
      cbn.
      unfold mapdt_ci.
      unfold Mapdt_CommIdem_list_prefix.
      fequal.
      fequal.
      fequal.
      unfold mapdt_list_prefix.
      unfold compose.
      admit.
    - unfold mapdtp, Mapdt_Categorical.
      reassociate <- on left.
      reassociate <- on left.
      rewrite <- dist2_morph.
      fequal.
      reassociate -> on left.
      rewrite fun2_map_map.
      reflexivity.
  Admitted.

  End context.

End DerivedInstances.

