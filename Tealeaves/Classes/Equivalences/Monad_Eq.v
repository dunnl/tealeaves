From Tealeaves Require Import
  Classes.Functor
  Theory.Algebraic.Monad.ToKleisli
  Theory.Kleisli.Monad.ToAlgebraic.

#[local] Generalizable Variable T.

Import ToFunctor.Operation.
Import ToAlgebraic.Operation.
Import ToKleisli.Operation.

Module AlgebraicRoundtrip.

  Context
    `{Return T}
    `{fmap1 : Fmap T}
    `{join1 : Join T}
    `{! Algebraic.Monad.Monad T}.

  #[local] Instance bind_derived: Bind T T := Bind_alg T.

  Definition fmap2 := Fmap_Bind T.
  Definition join2 := Join_Bind T.

  Goal fmap1 = fmap2.
  Proof.
    ext A B f.
    unfold fmap2, Operation.Fmap_Bind,
      bind, bind_derived, Bind_alg.
    rewrite <- (fun_fmap_fmap T).
    reassociate <-.
    rewrite (mon_join_fmap_ret T).
    reflexivity.
  Qed.

  Goal join1 = join2.
  Proof.
    ext A t.
    unfold join2, Join_Bind,
      bind, bind_derived, Bind_alg.
    rewrite (fun_fmap_id T).
    reflexivity.
  Qed.

End AlgebraicRoundtrip.

Section KleisliRoundTrip.

  Context
    `{Return T}
    `{bind1 : Bind T T}
    `{! Kleisli.Monad.Monad T}.

  Definition fmap_derived := Fmap_Bind.
  Definition join_derived := Join_Bind.
  Definition bind2 : Bind T T := Bind_alg T.

  Goal bind1 = bind2.
  Proof.
    ext A B f.
    unfold bind2, Bind_alg.
    unfold join, Join_Bind.
    unfold fmap, Fmap_Bind.
    unfold_compose_in_compose.
    rewrite (kmon_bind2 T).
    fequal. unfold kcompose.
    reassociate <-.
    rewrite (kmon_bind0 T).
    reflexivity.
  Qed.

End KleisliRoundTrip.
