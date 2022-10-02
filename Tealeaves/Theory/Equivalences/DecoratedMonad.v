From Tealeaves Require Import
  Theory.Algebraic.Decorated.Monad.ToKleisli
  Theory.Kleisli.Decorated.Monad.ToAlgebraic.

#[local] Generalizable Variables W T.

Import Classes.Kleisli.Decorated.Monad.Notations.
Import Product.Notations.
Import Comonad.Notations.

Module AlgebraicToKleisli.

  Context
    `{fmapT : Fmap T}
    `{decT : Decorate W T}
    `{joinT : Join T}
    `{retT : Return T}
    `{Monoid W}
    `{! Classes.Algebraic.Decorated.Monad.DecoratedMonad W T}.

  #[local] Instance bindd' : Bindd W T T := ToKleisli.Operation.Bindd_alg W T.

  Definition fmap' : Fmap T := ToAlgebraic.Operations.Fmap_Bindd W T.
  Definition dec' : Decorate W T := ToAlgebraic.Operations.Decorate_Bindd W T.
  Definition join' : Join T := ToAlgebraic.Operations.Join_Bindd W T.

  Goal fmapT = fmap'.
  Proof.
    unfold fmap'. unfold_ops @Operations.Fmap_Bindd.
    unfold bindd, bindd'.
    unfold_ops @Operation.Bindd_alg.
    ext A B f.
    rewrite <- (fun_fmap_fmap T).
    reassociate <-.
    reassociate ->.
    rewrite (dfun_dec_extract W T).
    rewrite <- (fun_fmap_fmap T).
    reassociate <-.
    rewrite (mon_join_fmap_ret T).
    reflexivity.
  Qed.

  Goal decT = dec'.
  Proof.
    unfold dec'. unfold_ops @Operations.Decorate_Bindd.
    unfold bindd, bindd'.
    unfold_ops @ToKleisli.Operation.Bindd_alg.
    ext A.
    rewrite (mon_join_fmap_ret T).
    reflexivity.
  Qed.

  Goal joinT = join'.
  Proof.
    unfold join'. unfold_ops @Operations.Join_Bindd.
    unfold bindd, bindd'.
    unfold_ops @Operation.Bindd_alg.
    ext A.
    reassociate ->.
    rewrite (dfun_dec_extract W T).
    reflexivity.
  Qed.

End AlgebraicToKleisli.

Module KleisliToAlgebraic.

  Context
    `{binddT : Bindd W T T}
    `{retT : Return T}
    `{Monoid W}
    `{@Classes.Kleisli.Decorated.Monad.Monad W T retT binddT _ _}.

  #[local] Instance fmap' : Fmap T := ToAlgebraic.Operations.Fmap_Bindd W T.
  #[local] Instance dec' : Decorate W T := ToAlgebraic.Operations.Decorate_Bindd W T.
  #[local] Instance join' : Join T := ToAlgebraic.Operations.Join_Bindd W T.

  Definition bindd' : Bindd W T T := ToKleisli.Operation.Bindd_alg W T.

  Goal binddT = bindd'.
  Proof.
    unfold bindd'. unfold_ops @Operation.Bindd_alg.
    unfold fmap, fmap', dec, dec', join, join'.
    unfold_ops @Operations.Fmap_Bindd.
    unfold_ops @Operations.Join_Bindd.
    unfold_ops @Operations.Decorate_Bindd.
    ext A B f.
    unfold_compose_in_compose.
    rewrite (kmond_bindd2 T).
    rewrite (kmond_bindd2 T).
    fequal.
    reassociate -> near (extract (W ×)).
    rewrite DerivedInstances.dm_kleisli_star1.
    rewrite cokleisli_id_l.
    change (@ret T _ (W * A)) with (@ret T _ (W * A) ∘ id).
    rewrite DerivedInstances.dm_kleisli_star5.
    reflexivity.
  Qed.

End KleisliToAlgebraic.
