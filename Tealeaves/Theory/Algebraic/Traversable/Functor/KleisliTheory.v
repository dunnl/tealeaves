From Tealeaves Require Export
  Theory.Algebraic.Traversable.Functor.ToKleisli.

#[local] Generalizable Variables A B C G ϕ.

(** * Properties of <<traverse>> *)
(******************************************************************************)

Import ToKleisli.Operation.

(** ** Specification for <<fmap>> *)
(******************************************************************************)
Section TraversableFunctor_fmap.

  Context
    (T : Type -> Type)
    `{Algebraic.Traversable.Functor.TraversableFunctor T}.

  Corollary fmap_to_traverse : forall `(f : A -> B),
      fmap T f = traverse T (fun A => A) f.
  Proof.
    intros. unfold traverse. unfold_ops @Traverse_alg.
    ext t. now rewrite (dist_unit T).
  Qed.

End TraversableFunctor_fmap.

(** ** Purity laws *)
(******************************************************************************)
Section traverse_purity_law.

  Context
    (T : Type -> Type)
    `{Algebraic.Traversable.Functor.TraversableFunctor T}
    `{Applicative G1}
    `{Applicative G2}.

  Corollary traverse_purity : forall A B (f : A -> G1 B),
      traverse T (G2 ∘ G1) (pure G2 ∘ f) = pure G2 ∘ traverse T G1 f.
  Proof.
    intros. unfold traverse.
    unfold_ops @Traverse_alg.
    now rewrite (fmap_purity_2 T (G2 := G2) f).
  Qed.

End traverse_purity_law.

(** ** Composition with sub-operations  *)
(******************************************************************************)
Section TraversableFunctor_composition.

  Context
    (T : Type -> Type)
    `{Algebraic.Traversable.Functor.TraversableFunctor T}
    `{Applicative G}.

  Corollary fmap_traverse : forall `(g : B -> C) `(f : A -> G B),
      fmap G (fmap T g) ∘ traverse T G f = traverse T G (fmap G g ∘ f).
  Proof.
    intros. unfold traverse.
    unfold_ops @Traverse_alg.
    ext t.
    repeat reassociate <-.
    change (fmap G (fmap T g)) with (fmap (G ∘ T) g).
    rewrite (natural (ϕ := @dist T _ G _ _ _)).
    reassociate ->.
    unfold_ops @Fmap_compose.
    now rewrite (fun_fmap_fmap T).
  Qed.

  Corollary traverse_fmap : forall `(g : B -> G C) `(f : A -> B),
      traverse T G g ∘ fmap T f = traverse T G (g ∘ f).
  Proof.
    intros. unfold_ops @Traverse_alg.
    now rewrite <- (fun_fmap_fmap T).
  Qed.

End TraversableFunctor_composition.
