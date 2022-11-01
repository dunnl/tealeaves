From Tealeaves Require Export
  Classes.Kleisli.Decorated.Functor
  Classes.Kleisli.Traversable.Functor
  Classes.Kleisli.DT.Functor.

Import Data.Strength.Notations.
Import DT.Functor.Notations.
Import Product.Notations.
Import Comonad.Notations.

#[local] Generalizable Variables W T A B C.

(** * Lesser Kleisli operations *)
(******************************************************************************)
Module Operations.
  Section with_kleisli.

    Context
      (T : Type -> Type)
      `{Fmapdt W T}.

    #[export] Instance Fmap_Fmapdt: Fmap T := fun A B f => fmapdt T (fun A => A) (f ∘ extract (W ×)).
    #[export] Instance Fmapd_Fmapdt: Fmapd W T := fun A B f => fmapdt T (fun A => A) f.
    #[export] Instance Traverse_Fmapdt: Traverse T := fun G _ _ _ A B f => fmapdt T G (f ∘ extract (W ×)).

  End with_kleisli.
End Operations.

Import Operations.

Module Instances.

  Section with_functor.

    Context
      (T : Type -> Type)
      `{DT.Functor.DecoratedTraversableFunctor W T}.

    (** * Lessor Kleisli instances *)
    (******************************************************************************)
    #[export] Instance: Functor T.
    Proof.
      constructor; unfold_ops @Fmap_Fmapdt.
      - intros. now rewrite (kdtfun_fmapdt1 W T).
      - intros.
        change_left (fmap (fun A => A) (fmapdt T (fun A0 : Type => A0) (g ∘ extract (prod W))) ∘
                                       fmapdt T (fun A0 : Type => A0) (f ∘ extract (prod W))).
        rewrite (kdtfun_fmapdt2 W T (G1 := fun A => A) (G2 := fun A => A)).
        fequal. now rewrite Mult_compose_identity1.
        admit.
    Admitted.

    #[export] Instance: Kleisli.Decorated.Functor.DecoratedFunctor W T.
    Proof.
      constructor; unfold_ops @Fmapd_Fmapdt.
      - intros. now rewrite (kdtfun_fmapdt1 W T).
      - intros.
        change_left ((fmap (fun A => A) (fmapdt T (fun A0 : Type => A0) g) ∘
                                       fmapdt T (fun A0 : Type => A0) f)).
        rewrite (kdtfun_fmapdt2 W T (G1 := fun A => A) (G2 := fun A => A) g f).
        fequal. now rewrite Mult_compose_identity1.
        unfold kcompose_dt. now ext [w a].
    Qed.

    #[export] Instance: Kleisli.Traversable.Functor.TraversableFunctor T.
    Proof.
      constructor; unfold_ops @Traverse_Fmapdt.
      - intros. now rewrite (kdtfun_fmapdt1 W T).
      - intros. rewrite (kdtfun_fmapdt2 W T _ _ (G1 := G1) (G2 := G2)).
        fequal. admit.
      - intros. rewrite <- (kdtfun_morph W T).
        reflexivity.
    Admitted.

    (** * Composition with lesser Kleisli operations *)
    (******************************************************************************)
    Section with_applicatives.

      Context
        (G1 G2 : Type -> Type)
          `{Applicative G1}
          `{Applicative G2}.

      (** *** <<fmapdt>> on the right *)
      (******************************************************************************)
      Corollary traverse_fmapdt {A B C} : forall (g : B -> G2 C) (f : W * A -> G1 B),
          fmap G1 (traverse T G2 g) ∘ fmapdt T G1 f = fmapdt T (G1 ∘ G2) (fmap G1 g ∘ f).
      Proof.
        intros. unfold_ops @Traverse_Fmapdt.
        rewrite (kdtfun_fmapdt2 W T).
        admit.
      Admitted.

      Corollary fmapd_fmapdt {A B C} : forall (g : W * B -> C) (f : W * A -> G1 B),
          fmap G1 (fmapd T g) ∘ fmapdt T G1 f = fmapdt T G1 (fmap G1 g ∘ σ G1 ∘ cobind (W ×) f).
      Proof.
        intros. unfold_ops @Fmapd_Fmapdt.
        rewrite (kdtfun_fmapdt2 W T (G2 := fun A => A)).
        fequal. now rewrite Mult_compose_identity1.
      Qed.

      Corollary fmap_fmapdt {A B C} : forall (g : B -> C) (f : W * A -> G1 B),
          fmap G1 (fmap T g) ∘ fmapdt T G1 f = fmapdt T G1 (fmap G1 g ∘ f).
      Proof.
        intros. unfold_ops @Fmap_Fmapdt.
        rewrite (kdtfun_fmapdt2 W T (G2 := fun A => A)).
        fequal. now rewrite Mult_compose_identity1.
        admit.
      Admitted.

      (** *** <<fmapdt>> on the right *)
      (******************************************************************************)
      Corollary fmapdt_traverse {A B C} : forall (g : W * B -> G2 C) (f : A -> G1 B),
          fmap G1 (fmapdt T G2 g) ∘ traverse T G1 f = fmapdt T (G1 ∘ G2) (fmap G1 g ∘ σ G1 ∘ fmap (W ×) f).
      Proof.
        introv. unfold_ops @Traverse_Fmapdt.
        rewrite (kdtfun_fmapdt2 W T).
        fequal. admit.
      Admitted.

      Lemma fmapdt_fmapd {A B C} : forall (g : W * B -> G2 C) (f : W * A -> B),
          fmapdt T G2 g ∘ fmapd T f = fmapdt T G2 (g co⋆ f).
      Proof.
        introv. unfold_ops @Fmapd_Fmapdt.
        change (fmapdt T G2 g) with (fmap (fun A => A) (fmapdt T G2 g)).
        rewrite (kdtfun_fmapdt2 W T (G1 := fun A => A)).
        fequal. now rewrite Mult_compose_identity2.
        admit.
      Admitted.

      Lemma fmapdt_fmap {A B C} : forall (g : W * B -> G2 C) (f : A -> B),
          fmapdt T G2 g ∘ fmap T f = fmapdt T G2 (g ∘ fmap (prod W) f).
      Proof.
        intros. unfold_ops @Fmap_Fmapdt.
        change (fmapdt T G2 g) with (fmap (fun A => A) (fmapdt T G2 g)).
        rewrite (kdtfun_fmapdt2 W T (G1 := fun A => A)).
        fequal. now rewrite Mult_compose_identity2. admit.
      Admitted.

      (** *** Mixes *)
      (******************************************************************************)
      Corollary fmap_fmapd {A B C} : forall (g : B -> C) (f : W * A -> B),
          fmap T g ∘ fmapd T f = fmapd T (g ∘ f).
      Proof.
        intros.
        change_left (fmap (fun A => A) (fmap T g) ∘ fmapd T f).
        admit.
      Admitted.

    End with_applicatives.

  End with_functor.

End Instances.
