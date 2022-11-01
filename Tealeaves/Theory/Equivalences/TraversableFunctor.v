From Tealeaves Require Import
  Theory.Algebraic.Traversable.Functor.ToKleisli
  Theory.Kleisli.Traversable.Functor.ToAlgebraic.

#[local] Generalizable Variables T.

Import Classes.Algebraic.Traversable.Functor.Notations.

Module AlgebraicToKleisli.

  Context
    `{fmapT : Fmap T}
    `{distT : Dist T}
    `{! Classes.Algebraic.Traversable.Functor.TraversableFunctor T}.

  #[local] Instance traverse' : Traverse T := ToKleisli.Operation.Traverse_alg T.

  Definition fmap' : Fmap T := ToFunctor.Operation.Fmap_Traverse T.
  Definition dist' : Dist T := ToAlgebraic.Operations.Dist_Traverse T.

  Goal fmapT = fmap'.
  Proof.
    unfold fmap'. unfold_ops @Fmap_Traverse.
    unfold traverse, traverse'.
    unfold_ops @Operation.Traverse_alg.
    ext A B f.
    rewrite (dist_unit T).
    reflexivity.
  Qed.

  Goal distT = dist'.
  Proof.
    unfold dist'. unfold_ops @Operations.Dist_Traverse.
    unfold traverse, traverse'.
    unfold_ops @Operation.Traverse_alg.
    ext G Hmap Hpure Hmult. ext A.
    rewrite (fun_fmap_id T).
    reflexivity.
  Qed.

End AlgebraicToKleisli.

Module KleisliToAlgebraic.

  Context
    `{traverseT : Traverse T}
    `{@Classes.Kleisli.Traversable.Functor.TraversableFunctor T _}.

  #[local] Instance fmap' : Fmap T := ToFunctor.Operation.Fmap_Traverse T.
  #[local] Instance dist' : Dist T := ToAlgebraic.Operations.Dist_Traverse T.

  Definition traverse' : Traverse T := ToKleisli.Operation.Traverse_alg T.

  Goal forall G `{Applicative G}, @traverseT G _ _ _ = @traverse' G _ _ _.
  Proof.
    intros.
    unfold traverse'. unfold_ops @Operation.Traverse_alg.
    unfold fmap, fmap', dist, dist'.
    ext A B f.
    unfold_ops @Operations.Dist_Traverse.
    unfold_ops @Fmap_Traverse.
    change (traverse T G (@id (G B))) with (fmap (fun A => A) (traverse T G (@id (G B)))).
    rewrite (trf_traverse_traverse T (fun A => A) G);
      try typeclasses eauto.
    rewrite (fun_fmap_id (fun A => A)).
    change (id ∘ f) with f.
    change_left (traverse T G f).
    fequal.
    now rewrite (Mult_compose_identity2).
  Qed.

End KleisliToAlgebraic.
