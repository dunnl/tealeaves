From Tealeaves Require Import
  Theory.Algebraic.DT.Monad.ToKleisli
  Theory.Kleisli.DT.Monad.ToAlgebraic.

#[local] Generalizable Variables W T.

Import Comonad.Notations.
Import Traversable.Monad.Notations.
Import DT.Monad.Notations.
Import Product.Notations.

Module AlgebraicToKleisli.

  Context
    `{Monoid W}
    `{fmapT : Fmap T}
    `{distT : Dist T}
    `{joinT : Join T}
    `{decorateT : Decorate W T}
    `{Return T}
    `{! Classes.Algebraic.DT.Monad.DecoratedTraversableMonad W T}.

  #[local] Instance binddt' : Binddt W T T := ToKleisli.Operation.Binddt_alg T.

  Definition fmap' : Fmap T := ToFunctor.Operation.Fmap_Binddt T.
  Definition join' : Join T := ToAlgebraic.Operations.Join_Binddt W T.
  Definition decorate' : Decorate W T := ToAlgebraic.Operations.Decorate_Binddt W T.
  Definition dist' : Dist T := ToAlgebraic.Operations.Dist_Binddt W T.

  Goal fmapT = fmap'.
  Proof.
    unfold fmap'. unfold_ops @ToFunctor.Operation.Fmap_Binddt.
    unfold binddt, binddt'.
    unfold_ops @Operation.Binddt_alg.
    ext A B f.
    unfold_ops @Fmap_I.
    rewrite (dist_unit T).
    change (?f ∘ id) with f.
    do 2 rewrite <- (fun_fmap_fmap T).
    do 2 reassociate <- on right.
    rewrite (mon_join_fmap_ret T).
    change (id ∘ ?f) with f.
    reassociate -> on right.
    rewrite (dfun_dec_extract W T).
    reflexivity.
  Qed.

  Goal forall G `{Applicative G}, @distT G _ _ _ = @dist' G _ _ _.
  Proof.
    intros.
    unfold dist'. unfold_ops @Operations.Dist_Binddt.
    unfold binddt, binddt'.
    unfold_ops @Operation.Binddt_alg.
    ext A.
    rewrite <- (fun_fmap_fmap T).
    unfold_compose_in_compose.
    reassociate <- on right.
    reassociate -> near (fmap T (fmap G (ret T (A := A)))).
    change (fmap T (fmap G (ret T (A := A))))
      with ((fmap (T ○ G) (ret T (A := A)))).
    rewrite <- (natural (ϕ := @dist T _ G _ _ _)).
    unfold_ops @Fmap_compose.
    reassociate <- on right.
    rewrite (fun_fmap_fmap G).
    rewrite (mon_join_fmap_ret T).
    rewrite (fun_fmap_id G).
    reassociate -> on right.
    rewrite (dfun_dec_extract W T).
    reflexivity.
  Qed.

  Goal joinT = join'.
  Proof.
    unfold join'. unfold_ops @Operations.Join_Binddt.
    unfold binddt, binddt'.
    unfold_ops @Operation.Binddt_alg.
    ext A.
    rewrite (dist_unit T).
    reassociate -> on right.
    rewrite (dfun_dec_extract W T).
    reflexivity.
  Qed.

  Goal decorateT = decorate'.
  Proof.
    unfold decorate'. unfold_ops @Operations.Decorate_Binddt.
    unfold binddt, binddt'.
    unfold_ops @Operation.Binddt_alg @Fmap_I.
    ext A.
    rewrite (dist_unit T).
    change (?f ∘ id) with f.
    rewrite (mon_join_fmap_ret T).
    reflexivity.
  Qed.

End AlgebraicToKleisli.

Module KleisliToAlgebraic.

  Context
    `{binddtT : Binddt W T T}
    `{Monoid W}
    `{Return T}
    `{! Classes.Kleisli.DT.Monad.Monad W T}.

  #[local] Instance fmap' : Fmap T := ToFunctor.Operation.Fmap_Binddt T.
  #[local] Instance dist' : Dist T := ToAlgebraic.Operations.Dist_Binddt W T.
  #[local] Instance join' : Join T := ToAlgebraic.Operations.Join_Binddt W T.
  #[local] Instance decorate' : Decorate W T := ToAlgebraic.Operations.Decorate_Binddt W T.

  Definition binddt' : Binddt W T T := ToKleisli.Operation.Binddt_alg T.

  Import DerivedInstances.Operations.
  Import DerivedInstances.Instances.

  Goal forall G `{Applicative G}, @binddtT G _ _ _ = @binddt' G _ _ _.
  Proof.
    intros.
    unfold binddt'. unfold_ops @Operation.Binddt_alg.
    ext A B f.
    unfold fmap at 2, fmap', dist, dist', dec, decorate'.
    unfold_ops @Operations.Dist_Binddt.
    unfold_ops @ToFunctor.Operation.Fmap_Binddt.
    unfold_ops @Operations.Decorate_Binddt.
    change_right (fmap G (join T) ∘ bindt T G (fmap G (ret T))
                    ∘ fmap T f ∘ bindd T (ret T)).
    reassociate -> on right.
    unfold fmap'.
    rewrite (DerivedInstances.fmap_bindd T).
    reassociate -> on right.
    unfold_compose_in_compose.
    rewrite (DerivedInstances.bindt_bindd T G).
    reassociate <- on right.
    rewrite (DerivedInstances.bindt_fmap T G).
    rewrite (ktm_bindt0 T); [| assumption].
    unfold join, join'; unfold_ops @Operations.Join_Binddt.
    unfold compose at 2.
    rewrite (kdtm_binddt2 W T _ _ _ (G1 := G) (G2 := fun A => A)).
    change_left (binddt T G f).
    fequal. now rewrite Mult_compose_identity1.
    change_right (id ∘ extract (prod W) ⋆dtm fmap G (ret T) ∘ f).
    rewrite (DerivedInstances.dtm_kleisli_37 W T).
    rewrite (DerivedInstances.kcompose_tm21 T); [| assumption].
    rewrite (fun_fmap_id G).
    reflexivity.
  Qed.

End KleisliToAlgebraic.
