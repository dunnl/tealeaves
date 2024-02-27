From Tealeaves Require Export
  Classes.Categorical.TraversableMonad
  Classes.Kleisli.TraversableMonad
  Classes.Coalgebraic.TraversableMonad
  Adapters.CategoricalToKleisli.TraversableMonad
  Adapters.KleisliToCategorical.TraversableMonad
  Adapters.CoalgebraicToKleisli.TraversableMonad
  Adapters.KleisliToCoalgebraic.TraversableMonad.

#[local] Generalizable Variables T.

#[local] Arguments ret (T)%function_scope {Return} (A)%type_scope _.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments bindt {T} (U)%function_scope {Bindt} G%function_scope
  {H H0 H1} {A B}%type_scope _%function_scope _.

(** * Categorical ~> Kleisli ~> Categorical *)
(******************************************************************************)
Module Categorical_Kleisli_Categorical.

  Context
    `{mapT : Map T}
    `{distT : ApplicativeDist T}
    `{joinT : Join T}
    `{Return T}
    `{! Categorical.TraversableMonad.TraversableMonad T}.

  #[local] Instance bindt' : Bindt T T := ToKleisli.Bindt_categorical T.

  Definition map'  : Map T := Map_Bindt T T.
  Definition dist' : ApplicativeDist T := Dist_Bindt T.
  Definition join' : Join T := Join_Bindt T.

  Goal mapT = map'.
  Proof.
    unfold map'. unfold_ops @Map_Bindt.
    unfold bindt, bindt'.
    unfold_ops @ToKleisli.Bindt_categorical.
    ext A B f.
    unfold_ops @Map_I.
    rewrite (dist_unit (F := T)).
    change (?g ∘ id) with g.
    rewrite <- (fun_map_map (F := T)).
    reassociate <- on right.
    now rewrite (mon_join_map_ret (T := T)).
  Qed.

  Goal forall G `{Applicative G}, @distT G _ _ _ = @dist' _ _ _ _.
  Proof.
    intros.
    unfold dist'. unfold_ops Dist_Bindt.
    unfold bindt, bindt'.
    unfold_ops @ToKleisli.Bindt_categorical.
    ext A.
    change (map T (map G (ret T A))) with (map (T ∘ G) (ret T A)).
    reassociate -> on right.
    unfold_compose_in_compose.
    rewrite <- (natural (Natural := dist_natural (F := T)) (ϕ := @dist T _ G _ _ _)).
    reassociate <- on right.
    unfold_ops @Map_compose.
    inversion H4.
    rewrite (fun_map_map (F := G)).
    rewrite (mon_join_map_ret (T := T)).
    rewrite (fun_map_id (F := G)).
    reflexivity.
  Qed.

  Goal joinT = join'.
  Proof.
    unfold join'. unfold_ops @Join_Bindt.
    unfold bindt, bindt'.
    unfold_ops @ToKleisli.Bindt_categorical.
    ext A. rewrite (fun_map_id (F := T)).
    unfold_ops @Map_I.
    rewrite (dist_unit (F := T)).
    reflexivity.
  Qed.

End Categorical_Kleisli_Categorical.

(** * Kleisli ~> Categorical ~> Kleisli *)
(******************************************************************************)
Module Kleisli_Categorical_Kleisli.

  Context
    `{bindtT : Bindt T T}
    `{Return T}
    `{! Kleisli.TraversableMonad.TraversableMonad T}.

  #[local] Instance map'  : Map T  := Map_Bindt T T.
  #[local] Instance dist' : ApplicativeDist T := Dist_Bindt T.
  #[local] Instance join' : Join T := Join_Bindt T.

  Definition bindt' : Bindt T T := ToKleisli.Bindt_categorical T.

  Goal forall A B G `{Applicative G}, @bindtT G _ _ _ A B = @bindt' G _ _ _ A B.
  Proof.
    intros. ext f.
    unfold bindt'. unfold_ops @ToKleisli.Bindt_categorical.
    unfold join, join', dist, dist', map at 2, map'.
    unfold_ops @Join_Bindt.
    unfold_ops @Dist_Bindt.
    unfold_ops @Map_Bindt.
    change (?g ∘ id) with g.
    reassociate -> on right.
    change (bindt T G (map G (ret T (T B))))
      with (map (fun A => A) (bindt T G (map G (ret T (T B))))).
    unfold_compose_in_compose.
    rewrite (ktm_bindt2 (G1 := fun A => A)).
    unfold kc3.
    unfold_ops @Map_I.
    reassociate <- on right.
    rewrite (ktm_bindt0 (T := T)).
    rewrite (bindt_app_l).
    change ((fun A => A) ∘ ?G) with G.
    Set Printing Implicit.
    unfold compose at 2.
    rewrite (ktm_bindt2 (B:= (T B)) (T := T) (G1 := G) (G2 := fun A => A)).
    rewrite (bindt_app_r).
    unfold bindt.
    fequal.
    unfold kc3.
    reassociate <-.
    inversion H4.
    rewrite (fun_map_map (F := G)).
    rewrite (ktm_bindt0 (T := T) (G := fun A => A)).
    rewrite (fun_map_id (F := G)).
    reflexivity.
  Qed.

End Kleisli_Categorical_Kleisli.

(** * Kleisli ~> Coalgebraic ~> Kleisli *)
(******************************************************************************)
Module Kleisli_Coalgebraic_Kleisli.

  Context
    `{bindtT : Bindt T T}
    `{Return T}
    `{! Kleisli.TraversableMonad.TraversableMonad T}.

  #[local] Instance toBatch3' : ToBatch3 T T :=
    ToBatch3_Bindt.

  #[local] Instance bindt' : Bindt T T :=
    Bindt_ToBatch3 T T.

  Goal forall A B G `{Applicative G}, @bindtT G _ _ _ A B = @bindt' G _ _ _ A B.
  Proof.
    intros. ext f.
    unfold bindt'.
    unfold_ops @Bindt_ToBatch3.
    unfold toBatch3.
    unfold toBatch3'.
    unfold_ops @ToBatch3_Bindt.
    erewrite (ktm_morph).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

End Kleisli_Coalgebraic_Kleisli.


(** * Coalgebraic ~> Kleisli ~> Coalgebraic *)
(******************************************************************************)
Module Coalgebraic_Kleisli_Coalgebraic.

  Context
    `{toBatch3T : ToBatch3 T T}
    `{Return T}
    `{! Coalgebraic.TraversableMonad.TraversableMonad T}.

  #[local] Instance bindt': Bindt T T :=
    @Bindt_ToBatch3 T T toBatch3T.

  #[local] Instance toBatch3': ToBatch3 T T :=
    @ToBatch3_Bindt T T bindt'.

  Lemma runBatch_batch2 : forall (A B : Type),
      runBatch (Batch A B) (batch A B) B = @id (Batch A B B).
  Proof.
    intros. ext b.
    induction b as [C c | C rest IHrest a].
    - reflexivity.
    - cbn. unfold id in *.
      fequal. rewrite IHrest.
      compose near rest.
      rewrite (fun_map_map (F := Batch A B)).
      compose near rest.
      rewrite (fun_map_map (F := Batch A B)).
      unfold compose, strength_arrow.
      change rest with (id rest) at 2.
      rewrite <- (fun_map_id (F := Batch A B)).
      fequal.
  Qed.

  Goal forall A B, @toBatch3T A B = @toBatch3' A B.
  Proof.
    intros.
    unfold toBatch3'. unfold_ops @ToBatch3_Bindt.
    unfold bindt.
    unfold bindt'.
    unfold_ops @Bindt_ToBatch3.
    Search runBatch batch.
    rewrite runBatch_batch2.
    reflexivity.
  Qed.

End Coalgebraic_Kleisli_Coalgebraic.
