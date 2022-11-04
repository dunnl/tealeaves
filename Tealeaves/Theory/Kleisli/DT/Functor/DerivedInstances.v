From Tealeaves Require Export
  Classes.Kleisli.Decorated.Functor
  Classes.Kleisli.Traversable.Functor
  Classes.Kleisli.DT.Functor
  Theory.Kleisli.DT.Functor.ToFunctor.

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

    #[export] Instance Fmapd_Fmapdt: Fmapd W T := fun A B f => fmapdt T (fun A => A) f.
    #[export] Instance Traverse_Fmapdt: Traverse T := fun G _ _ _ A B f => fmapdt T G (f ∘ extract (W ×)).

  End with_kleisli.
End Operations.

Section kcompose_dt_lemmas.

  Context
    (T : Type -> Type)
    `{DecoratedTraversableFunctor W T}
      (G1 G2 : Type -> Type)
      `{Applicative G1}
      `{Applicative G2}
      (A B C : Type).

  Lemma kcompose_dt_22 :
    forall (g : B -> G2 C) (f : A -> G1 B),
      (g ∘ extract (prod W)) ⋆dt (f ∘ extract (prod W)) = fmap G1 g ∘ f ∘ extract (prod W).
  Proof.
    intros. unfold kcompose_dt.
    rewrite <- (fmap_to_cobind (W ×)).
    ext [w a].
    unfold compose; cbn.
    compose near (f a) on left.
    now rewrite (fun_fmap_fmap G1).
  Qed.

  Lemma kcompose_dt_23 :
    forall (g : B -> G2 C) (f : W * A -> G1 B),
      (g ∘ extract (prod W)) ⋆dt f = fmap G1 g ∘ f.
  Proof.
    intros. unfold kcompose_dt.
    ext [w a].
    unfold compose; cbn.
    compose near (f (w, a)) on left.
    now rewrite (fun_fmap_fmap G1).
  Qed.

  Lemma kcompose_dt_03 :
    forall (g : B -> C) (f : W * A -> G1 B),
      kcompose_dt (G2 := fun A => A) (g ∘ extract (W ×)) f = fmap G1 g ∘ f.
  Proof.
    intros. unfold kcompose_dt.
    ext [w a].
    unfold compose; cbn.
    compose near (f (w, a)) on left.
    now rewrite (fun_fmap_fmap G1).
  Qed.

  Lemma kcompose_dt_32 :
    forall (g : W * B -> G2 C) (f : A -> G1 B),
      g ⋆dt (f ∘ extract (prod W)) = fmap G1 g ∘ σ G1 ∘ fmap (prod W) f.
  Proof.
    intros. unfold kcompose_dt.
    ext [w a].
    unfold compose; cbn.
    compose near (f a) on left.
    rewrite (fun_fmap_fmap G1).
    compose near (f a) on right.
    rewrite (fun_fmap_fmap G1).
    reflexivity.
  Qed.

  Lemma kcompose_dt_31 :
    forall (g : W * B -> G2 C)
      (f : W * A -> B),
      g ⋆dt f = g co⋆ f.
  Proof.
    intros. unfold kcompose_dt.
    unfold strength; unfold_ops @Fmap_I.
    ext [w a].
    reflexivity.
  Qed.

  Lemma kcompose_dt_30 :
    forall (g : W * B -> G2 C) (f : A -> B),
      g ⋆dt (f ∘ extract (prod W)) = g ∘ fmap (prod W) f.
  Proof.
    intros. unfold kcompose_dt.
    unfold strength; unfold_ops @Fmap_I.
    ext [w a].
    reflexivity.
  Qed.

  Lemma kcompose_dt_01 :
    forall (g : B -> C) (f : W * A -> B),
      kcompose_dt (G2 := fun A => A) (g ∘ extract (prod W)) f = g ∘ f.
  Proof.
    intros. unfold kcompose_dt.
    unfold strength; unfold_ops @Fmap_I.
    ext [w a].
    reflexivity.
  Qed.

End kcompose_dt_lemmas.

(** ** Composition with lesser Kleisli operations *)
(******************************************************************************)
Section composition.

  Context
    (T : Type -> Type)
    `{DecoratedTraversableFunctor W T}
    (G1 G2 : Type -> Type)
    `{Applicative G1}
    `{Applicative G2}.

  Import Operations.
  Import ToFunctor.Operation.

  (** *** <<fmapdt>> on the right *)
  (******************************************************************************)
  Corollary traverse_fmapdt {A B C} : forall (g : B -> G2 C) (f : W * A -> G1 B),
      fmap G1 (traverse T G2 g) ∘ fmapdt T G1 f = fmapdt T (G1 ∘ G2) (fmap G1 g ∘ f).
  Proof.
    intros. unfold_ops @Traverse_Fmapdt.
    rewrite (kdtfun_fmapdt2 W T).
    fequal. now rewrite kcompose_dt_23.
  Qed.

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
    now rewrite kcompose_dt_03.
  Qed.

  (** *** <<fmapdt>> on the right *)
  (******************************************************************************)
  Corollary fmapdt_traverse {A B C} : forall (g : W * B -> G2 C) (f : A -> G1 B),
      fmap G1 (fmapdt T G2 g) ∘ traverse T G1 f = fmapdt T (G1 ∘ G2) (fmap G1 g ∘ σ G1 ∘ fmap (W ×) f).
  Proof.
    introv. unfold_ops @Traverse_Fmapdt.
    rewrite (kdtfun_fmapdt2 W T).
    rewrite kcompose_dt_32.
    reflexivity.
  Qed.

  Lemma fmapdt_fmapd {A B C} : forall (g : W * B -> G2 C) (f : W * A -> B),
      fmapdt T G2 g ∘ fmapd T f = fmapdt T G2 (g co⋆ f).
  Proof.
    introv. unfold_ops @Fmapd_Fmapdt.
    change (fmapdt T G2 g) with (fmap (fun A => A) (fmapdt T G2 g)).
    rewrite (kdtfun_fmapdt2 W T (G1 := fun A => A)).
    fequal. now rewrite Mult_compose_identity2.
    now rewrite kcompose_dt_31.
  Qed.

  Lemma fmapdt_fmap {A B C} : forall (g : W * B -> G2 C) (f : A -> B),
      fmapdt T G2 g ∘ fmap T f = fmapdt T G2 (g ∘ fmap (prod W) f).
  Proof.
    intros. unfold_ops @Fmap_Fmapdt.
    change (fmapdt T G2 g) with (fmap (fun A => A) (fmapdt T G2 g)).
    rewrite (kdtfun_fmapdt2 W T (G1 := fun A => A)).
    fequal. now rewrite Mult_compose_identity2.
    now rewrite kcompose_dt_30.
  Qed.

  (** *** Mixes *)
  (******************************************************************************)
  Corollary fmap_fmapd {A B C} : forall (g : B -> C) (f : W * A -> B),
      fmap T g ∘ fmapd T f = fmapd T (g ∘ f).
  Proof.
    intros.
    change_left (fmap (fun A => A) (fmap T g) ∘ fmapd T f).
    unfold fmap at 2. unfold Fmap_Fmapdt. unfold_ops @Fmapd_Fmapdt.
    rewrite (kdtfun_fmapdt2 W T (G2 := fun A => A) (G1 := fun A => A)).
    fequal. now rewrite Mult_compose_identity2.
    now rewrite (kcompose_dt_03).
  Qed.

End composition.

Module Instances.
  Section with_functor.

  Context
    (T : Type -> Type)
    `{DecoratedTraversableFunctor W T}.

    Import Operations.
    Import ToFunctor.Operation.
    Import ToFunctor.Instance.

    (** * Lessor Kleisli instances *)
    (******************************************************************************)
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
        fequal. now rewrite kcompose_dt_22.
      - intros. rewrite <- (kdtfun_morph W T).
        reflexivity.
    Qed.

  End with_functor.

End Instances.
