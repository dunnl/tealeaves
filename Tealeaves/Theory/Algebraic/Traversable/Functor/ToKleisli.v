From Tealeaves Require Export
     Classes.Algebraic.Traversable.Functor
     Classes.Kleisli.Traversable.Functor
     Theory.Algebraic.Traversable.Functor.Properties.

#[local] Generalizable Variables A B C G ϕ.

(** * Kleisi presentation of traversable functors *)
(******************************************************************************)

(** ** <<Traverse>> operation *)
(******************************************************************************)
Module Operation.
  Section with_algebraic.

    Context
      (T : Type -> Type)
      `{Fmap T} `{Dist T}.

    #[export] Instance Traverse_alg : Traverse T :=
      fun (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G}
        (A B : Type) (f : A -> G B) => dist T G ∘ fmap T f.

    End with_algebraic.
End Operation.

Import Operation.

(** ** Kleisi presentation of traversable functors *)
(******************************************************************************)
Module Instance.

  Section with_functor.

    Context
      (T : Type -> Type)
      `{Algebraic.Traversable.Functor.TraversableFunctor T}.

    Theorem traverse_id : forall (A : Type),
        traverse T (fun A => A) id = @id (T A).
    Proof.
      intros. unfold traverse. unfold_ops @Traverse_alg.
      ext t. rewrite (dist_unit T).
      now rewrite (fun_fmap_id T).
    Qed.

    Theorem traverse_id_purity : forall `{Applicative G} (A : Type),
        traverse T G (pure G) = @pure G _ (T A).
    Proof.
      intros. unfold traverse.
      unfold_ops @Traverse_alg.
      ext t. now rewrite fmap_purity_1.
    Qed.

    Lemma traverse_traverse (G1 G2 : Type -> Type) `{Applicative G2} `{Applicative G1} :
      forall `(g : B -> G2 C) `(f : A -> G1 B),
        fmap G1 (traverse T G2 g) ∘ traverse T G1 f = traverse T (G1 ∘ G2) (fmap G1 g ∘ f).
    Proof.
      introv. unfold traverse.
      unfold_ops @Traverse_alg.
      rewrite (dist_linear T).
      repeat reassociate <-.
      rewrite <- (fun_fmap_fmap T).
      repeat reassociate <-.
      reassociate -> near (fmap T (fmap G1 g)).
      change (fmap T (fmap G1 g)) with (fmap (T ∘ G1) g).
      rewrite <- (natural (ϕ := @dist T _ G1 _ _ _)).
      unfold_ops @Fmap_compose.
      reassociate <-.
      unfold_compose_in_compose.
      now rewrite (fun_fmap_fmap G1).
    Qed.

    Lemma traverse_morphism `{morph : ApplicativeMorphism G1 G2 ϕ} : forall `(f : A -> G1 B),
        ϕ (T B) ∘ traverse T G1 f = traverse T G2 (ϕ B ∘ f).
    Proof.
      intros. unfold traverse.  unfold_ops @Traverse_alg.
      reassociate <-.
      inversion morph.
      rewrite <- (dist_morph T).
      reassociate ->.
      now rewrite (fun_fmap_fmap T).
    Qed.

    #[export] Instance: Kleisli.Traversable.Functor.TraversableFunctor T :=
      {| trf_traverse_id := @traverse_id;
        trf_traverse_traverse := @traverse_traverse;
        trf_traverse_morphism := @traverse_morphism;
      |}.

  End with_functor.

End Instance.