From Tealeaves Require Import
  Theory.Algebraic.DT.Functor.ToKleisli
  Theory.Kleisli.DT.Functor.ToAlgebraic.

#[local] Generalizable Variables E T.

Import Comonad.Notations.
Import DT.Functor.Notations.
Import Product.Notations.

Module AlgebraicToKleisli.

  Context
    `{fmapT : Fmap T}
    `{distT : Dist T}
    `{decorateT : Decorate E T}
    `{! Classes.Algebraic.DT.Functor.DecoratedTraversableFunctor E T}.

  #[local] Instance fmapdt' : Fmapdt E T := ToKleisli.Operation.Fmapdt_alg E T.

  Definition fmap' : Fmap T := Operation.Fmap_Fmapdt T.
  Definition decorate' : Decorate E T := ToAlgebraic.Operations.Decorate_Fmapdt E T.
  Definition dist' : Dist T := ToAlgebraic.Operations.Dist_Fmapdt E T.

  Goal fmapT = fmap'.
  Proof.
    unfold fmap'. unfold_ops @Operation.Fmap_Fmapdt.
    unfold fmapdt, fmapdt'.
    unfold_ops @Operation.Fmapdt_alg.
    ext A B f.
    rewrite (dist_unit T).
    rewrite <- (fun_fmap_fmap T).
    reassociate -> on right.
    reassociate -> on right.
    rewrite (dfun_dec_extract E T).
    reflexivity.
  Qed.

  Goal distT = dist'.
  Proof.
    unfold dist'. unfold_ops @Operations.Dist_Fmapdt.
    unfold fmapdt, fmapdt'.
    unfold_ops @Operation.Fmapdt_alg.
    ext G Hmap Hpure Hmult. ext A.
    reassociate -> on right.
    rewrite (dfun_dec_extract E T).
    reflexivity.
  Qed.

  Goal decorateT = decorate'.
  Proof.
    unfold decorate'. unfold_ops @Operations.Decorate_Fmapdt.
    unfold fmapdt, fmapdt'.
    unfold_ops @Operation.Fmapdt_alg.
    ext A.
    rewrite (dist_unit T).
    now rewrite (fun_fmap_id T).
  Qed.

End AlgebraicToKleisli.

Module KleisliToAlgebraic.

  Context
    `{fmapdtT : Fmapdt E T}
    `{@Classes.Kleisli.DT.Functor.DecoratedTraversableFunctor E T _}.

  #[local] Instance fmap' : Fmap T := Operation.Fmap_Fmapdt T.
  #[local] Instance dist' : Dist T := ToAlgebraic.Operations.Dist_Fmapdt E T.
  #[local] Instance decorate' : Decorate E T := ToAlgebraic.Operations.Decorate_Fmapdt E T.

  Definition fmapdt' : Fmapdt E T := ToKleisli.Operation.Fmapdt_alg E T.

  Import DerivedInstances.Operations.

  Goal forall G `{Applicative G}, @fmapdtT G _ _ _ = @fmapdt' G _ _ _.
  Proof.
    intros.
    unfold fmapdt'. unfold_ops @Operation.Fmapdt_alg.
    unfold fmap, fmap', dist, dist', dec, decorate'.
    ext A B f.
    unfold_ops @Operations.Dist_Fmapdt.
    unfold_ops @Operation.Fmap_Fmapdt.
    unfold_ops @Operations.Decorate_Fmapdt.
    change_right (fmapdt T G (extract (prod E)) ∘
                    fmap T f ∘
                    fmapd T id).
    unfold fmap'.
    change (@Operation.Fmap_Fmapdt T) with (@Operation.Fmap_Fmapdt T).
    rewrite (fmapdt_fmap T G).
    rewrite (fmapdt_fmapd T G).
    fequal. ext [e a]. reflexivity.
  Qed.

End KleisliToAlgebraic.
