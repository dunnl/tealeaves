From Tealeaves Require Import
  Theory.Algebraic.Decorated.Functor.ToKleisli
  Theory.Kleisli.Decorated.Functor.ToAlgebraic.

#[local] Generalizable Variables E T.

Import Product.Notations.
Import Comonad.Notations.

Module AlgebraicToKleisli.

  Context
    `{fmapT : Fmap T}
    `{decT : Decorate E T}
    `{! Classes.Algebraic.Decorated.Functor.DecoratedFunctor E T}.

  #[local] Instance fmapd' : Fmapd E T := ToKleisli.Operation.Fmapd_alg E T.

  Definition fmap' : Fmap T := ToAlgebraic.Operations.Fmap_Fmapd E T.
  Definition dec' : Decorate E T := ToAlgebraic.Operations.Decorate_Fmapd E T.

  Goal fmapT = fmap'.
  Proof.
    unfold fmap'. unfold_ops @Operations.Fmap_Fmapd.
    unfold fmapd, fmapd'.
    unfold_ops @Operation.Fmapd_alg.
    ext A B f.
    rewrite <- (fun_fmap_fmap T).
    reassociate ->.
    rewrite (dfun_dec_extract E T).
    reflexivity.
  Qed.

  Goal decT = dec'.
  Proof.
    unfold dec'. unfold_ops @Operations.Decorate_Fmapd.
    unfold fmapd, fmapd'.
    unfold_ops @ToKleisli.Operation.Fmapd_alg.
    ext A.
    rewrite (fun_fmap_id T).
    reflexivity.
  Qed.

End AlgebraicToKleisli.

Module KleisliToAlgebraic.

  Context
    `{fmapdT : Fmapd E T}
    `{! Classes.Kleisli.Decorated.Functor.DecoratedFunctor E T}.

  #[local] Instance fmap' : Fmap T := ToAlgebraic.Operations.Fmap_Fmapd E T.
  #[local] Instance dec' : Decorate E T := ToAlgebraic.Operations.Decorate_Fmapd E T.

  Definition fmapd' : Fmapd E T := ToKleisli.Operation.Fmapd_alg E T.

  Goal fmapdT = fmapd'.
  Proof.
    unfold fmapd'. unfold_ops @Operation.Fmapd_alg.
    unfold fmap, fmap', dec, dec'.
    unfold_ops @Operations.Fmap_Fmapd.
    unfold_ops @Operations.Decorate_Fmapd.
    ext A B f.
    unfold_compose_in_compose.
    rewrite (dfun_fmapd2 E T).
    reassociate -> on right.
    rewrite (extract_cobind (E ×)).
    reflexivity.
  Qed.

End KleisliToAlgebraic.
