From Tealeaves Require Import
  Classes.Categorical.TraversableMonad
  Classes.Kleisli.TraversableMonad
  Classes.Coalgebraic.TraversableMonad
  Adapters.CategoricalToKleisli.TraversableMonad
  Adapters.KleisliToCategorical.TraversableMonad
  Adapters.CoalgebraicToKleisli.TraversableMonad
  Adapters.KleisliToCoalgebraic.TraversableMonad.

Import Kleisli.TraversableMonad.Notations.
Import Functors.Early.Batch.

#[local] Generalizable Variables T.

(** * Categorical ~> Kleisli ~> Categorical *)
(******************************************************************************)
Module Categorical_Kleisli_Categorical.

  Context
    `{mapT: Map T}
    `{distT: ApplicativeDist T}
    `{joinT: Join T}
    `{Return T}
    `{! Categorical.TraversableMonad.TraversableMonad T}.

  Definition bindt':
    Bindt T T :=
    CategoricalToKleisli.TraversableMonad.DerivedOperations.Bindt_Categorical T.

  Definition map2: Map T :=
    DerivedOperations.Map_Bindt T T (Bindt_TU := bindt').

  Definition dist2: ApplicativeDist T :=
    DerivedOperations.Dist_Bindt T (Bindt_TT := bindt').

  Definition join2: Join T :=
    DerivedOperations.Join_Bindt T (Bindt_TT := bindt').

  Goal mapT = map2.
  Proof.
    ext A B f.
    unfold map2.
    unfold DerivedOperations.Map_Bindt.
    unfold bindt.
    unfold bindt'.
    unfold DerivedOperations.Bindt_Categorical.
    unfold_ops @Map_I.
    rewrite (dist_unit (F := T)).
    change (?g ∘ id) with g.
    rewrite <- (fun_map_map (F := T)).
    reassociate <- on right.
    rewrite (mon_join_map_ret (T := T)).
    reflexivity.
  Qed.

  Goal forall G `{Applicative G},
      @distT G _ _ _ = @dist2 G _ _ _.
  Proof.
    intros.
    ext A.
    unfold dist2.
    unfold DerivedOperations.Dist_Bindt.
    unfold bindt.
    unfold bindt'.
    unfold DerivedOperations.Bindt_Categorical.
    change (map (map (ret (T := T)))) with
      (map (F := T ∘ G) (ret (T := T) (A := A))).
    reassociate -> on right.
    unfold_compose_in_compose.
    rewrite <- (natural (Natural := dist_natural (F := T))
                 (ϕ := @dist T _ G _ _ _)).
    reassociate <- on right.
    unfold_ops @Map_compose.
    rewrite (fun_map_map (F := G)).
    rewrite (mon_join_map_ret (T := T)).
    rewrite (fun_map_id (F := G)).
    reflexivity.
  Qed.

  Goal joinT = join2.
  Proof.
    ext A.
    unfold join2.
    unfold DerivedOperations.Join_Bindt.
    unfold bindt.
    unfold bindt'.
    unfold DerivedOperations.Bindt_Categorical.
    rewrite (fun_map_id (F := T)).
    unfold_ops @Map_I.
    rewrite (dist_unit (F := T)).
    reflexivity.
  Qed.

End Categorical_Kleisli_Categorical.

(** * Kleisli ~> Categorical ~> Kleisli *)
(******************************************************************************)
Module Kleisli_Categorical_Kleisli.

  Context
    `{bindtT: Bindt T T}
    `{Return T}
    `{! Kleisli.TraversableMonad.TraversableMonad T}.

  Definition map': Map T :=
    DerivedOperations.Map_Bindt T T.
  Definition dist': ApplicativeDist T :=
    DerivedOperations.Dist_Bindt T.
  Definition join': Join T :=
    DerivedOperations.Join_Bindt T.

  Definition bindt2: Bindt T T :=
    DerivedOperations.Bindt_Categorical T
      (Map_T := map') (Join_T := join') (Dist_T := dist').

  Goal forall A B G `{Applicative G},
      @bindtT G _ _ _ A B = @bindt2 G _ _ _ A B.
  Proof.
    intros. ext f.
    unfold bindt2.
    unfold DerivedOperations.Bindt_Categorical.
    unfold join.
    unfold join'.
    unfold DerivedOperations.Join_Bindt.
    unfold dist.
    unfold dist'.
    unfold DerivedOperations.Dist_Bindt.
    unfold map at 3.
    unfold map'.
    unfold DerivedOperations.Map_Bindt.
    reassociate -> on right.
    change (bindt (A := G (T B)) (B := T B)
              (map (F := G) (ret (A := T B)))) with
      (map (F := fun A => A) (bindt (A := G (T B)) (B := T B)
                             (map (F := G) ret))).
    unfold_compose_in_compose.
    rewrite (ktm_bindt2 (G1 := fun A => A)).
    unfold kc6.
    unfold_ops @Map_I.
    reassociate <- on right.
    rewrite (ktm_bindt0 (T := T)).
    rewrite (bindt_app_id_l).
    change ((fun A => A) ∘ ?G) with G.
    unfold compose at 2.
    rewrite (ktm_bindt2 (T := T) (G1 := G) (G2 := fun A => A)).
    rewrite bindt_app_id_r.
    unfold kc6.
    reassociate <-.
    rewrite (fun_map_map).
    rewrite (ktm_bindt0 (G := fun A => A)).
    rewrite fun_map_id.
    reflexivity.
  Qed.

End Kleisli_Categorical_Kleisli.


(** * Coalgebraic ~> Kleisli ~> Coalgebraic *)
(******************************************************************************)
Module Coalgebraic_Kleisli_Coalgebraic.

  Context
    `{toBatch6_T: ToBatch6 T T}
    `{Return T}
    `{! Coalgebraic.TraversableMonad.TraversableMonad T}.

  Definition bindt': Bindt T T :=
    @DerivedOperations.Bindt_ToBatch6 T T toBatch6_T.

  Definition toBatch6_2: ToBatch6 T T :=
    @DerivedOperations.ToBatch6_Bindt T T bindt'.

  Goal forall A B, @toBatch6_T A B = @toBatch6_2 A B.
  Proof.
    intros.
    unfold toBatch6_2.
    unfold DerivedOperations.ToBatch6_Bindt.
    unfold bindt.
    unfold bindt'.
    unfold DerivedOperations.Bindt_ToBatch6.
    rewrite runBatch_batch_id.
    reflexivity.
  Qed.

End Coalgebraic_Kleisli_Coalgebraic.


(** * Kleisli ~> Coalgebraic ~> Kleisli *)
(******************************************************************************)
Module Kleisli_Coalgebraic_Kleisli.

  Context
    `{bindtT: Bindt T T}
    `{Return T}
    `{! Kleisli.TraversableMonad.TraversableMonad T}.

  Definition toBatch6': ToBatch6 T T :=
    DerivedOperations.ToBatch6_Bindt.

  Definition bindt2: Bindt T T :=
    DerivedOperations.Bindt_ToBatch6 T T
      (H := toBatch6').

  Goal forall A B G `{Applicative G},
      @bindtT G _ _ _ A B = @bindt2 G _ _ _ A B.
  Proof.
    intros. ext f.
    unfold bindt2.
    unfold DerivedOperations.Bindt_ToBatch6.
    unfold toBatch6.
    unfold toBatch6'.
    unfold DerivedOperations.ToBatch6_Bindt.
    rewrite (ktm_morph (U := T)
               (morphism := Batch.ApplicativeMorphism_runBatch)
               (ϕ := @Batch.runBatch _ _ G _ _ _ f)).
    rewrite (Batch.runBatch_batch G).
    reflexivity.
  Qed.

End Kleisli_Coalgebraic_Kleisli.
