From Tealeaves Require Import
  Theory.Algebraic.Traversable.Monad.ToKleisli
  Theory.Kleisli.Traversable.Monad.ToAlgebraic.

#[local] Generalizable Variables T.

Import Traversable.Monad.Notations.

Module AlgebraicToKleisli.

  Context
    `{fmapT : Fmap T}
    `{distT : Dist T}
    `{joinT : Join T}
    `{Return T}
    `{! Classes.Algebraic.Traversable.Monad.TraversableMonad T}.

  #[local] Instance bindt' : Bindt T T := ToKleisli.Operation.Bindt_alg T.

  Definition fmap' : Fmap T := ToFunctor.Operation.Fmap_Bindt T.
  Definition dist' : Dist T := ToAlgebraic.Operations.Dist_Bindt T.
  Definition join' : Join T := ToAlgebraic.Operations.Join_Bindt T.

  Goal fmapT = fmap'.
  Proof.
    unfold fmap'. unfold_ops @ToFunctor.Operation.Fmap_Bindt.
    unfold bindt, bindt'.
    unfold_ops @Operation.Bindt_alg.
    ext A B f.
    unfold_ops @Fmap_I.
    rewrite (dist_unit T).
    change (?g ∘ id) with g.
    rewrite <- (fun_fmap_fmap T).
    reassociate <- on right.
    now rewrite (mon_join_fmap_ret T).
  Qed.

  Goal forall G `{Applicative G}, @distT G _ _ _ = @dist' _ _ _ _.
  Proof.
    intros.
    unfold dist'. unfold_ops @Operations.Dist_Bindt.
    unfold bindt, bindt'.
    unfold_ops @Operation.Bindt_alg.
    ext A.
    change (?g ∘ id) with g.
    change (fmap T (fmap G (ret T)))
      with (fmap (T ∘ G) (ret (A := A) T)).
    reassociate -> on right.
    unfold_compose_in_compose.
    rewrite <- (natural (Natural := dist_natural T) (ϕ := @dist T _ G _ _ _)).
    reassociate <- on right.
    unfold_ops @Fmap_compose.
    rewrite (fun_fmap_fmap G).
    rewrite (mon_join_fmap_ret T).
    rewrite (fun_fmap_id G).
    reflexivity.
  Qed.

  Goal joinT = join'.
  Proof.
    unfold join'. unfold_ops @ToAlgebraic.Operations.Join_Bindt.
    unfold bindt, bindt'.
    unfold_ops @Operation.Bindt_alg.
    ext A. rewrite (fun_fmap_id T).
    unfold_ops @Fmap_I.
    rewrite (dist_unit T).
    reflexivity.
  Qed.

End AlgebraicToKleisli.

Module KleisliToAlgebraic.

  Context
    `{bindtT : Bindt T T}
    `{Return T}
    `{! Classes.Kleisli.Traversable.Monad.Monad T}.

  #[local] Instance fmap' : Fmap T := ToFunctor.Operation.Fmap_Bindt T.
  #[local] Instance dist' : Dist T := ToAlgebraic.Operations.Dist_Bindt T.
  #[local] Instance join' : Join T := ToAlgebraic.Operations.Join_Bindt T.

  Definition bindt' : Bindt T T := ToKleisli.Operation.Bindt_alg T.

  Goal forall A B G `{Applicative G}, @bindtT G A B _ _ _ = @bindt' G A B _ _ _.
  Proof.
    intros. ext f.
    unfold bindt'. unfold_ops @Operation.Bindt_alg.
    unfold join, join', dist, dist', fmap at 2, fmap'.
    unfold_ops @Operations.Join_Bindt.
    unfold_ops @Operations.Dist_Bindt.
    unfold_ops @ToFunctor.Operation.Fmap_Bindt.
    change (?g ∘ id) with g.
    reassociate -> on right.
    change (bindt T G (fmap G (ret T (A := T B))))
      with (fmap (fun A => A) (bindt T G (fmap G (ret T (A := T B))))).
    unfold_compose_in_compose.
    rewrite (ktm_bindt2 T _ _ _ (G2 := G) (G1 := fun A => A)).
    unfold kcompose_tm.
        unfold_ops @Fmap_I.
    reassociate <- on right.
    unfold_compose_in_compose.
    rewrite (ktm_bindt0 T (G (T B)) (T B) (fmap G (ret T (A := T B))) (G := G)).
    change ((fun A0 : Type => A0) ∘ G) with G.
    rewrite (Mult_compose_identity2).
    unfold_ops @Fmap_compose @Pure_compose.
    unfold_ops @Pure_I @Mult_compose @Mult_I.
    Set Keyed Unification.
    unfold id at 3.
    change ((fun (A0 : Type) (a : A0) => @pure G H2 A0 a)) with H2.
    change (@mult G H3) with H3.
    rewrite (ktm_bindt2 T A _ _ (G1 := G) (G2 := fun A => A)).
    Unset Keyed Unification.
    unfold kcompose_tm.
    reassociate <- on right.
    rewrite (fun_fmap_fmap G).
    rewrite (ktm_bindt0 T _ _ (G := fun A => A)).
    rewrite (fun_fmap_id G).
    fequal. rewrite Mult_compose_identity1.
    reflexivity.
  Qed.

End KleisliToAlgebraic.
