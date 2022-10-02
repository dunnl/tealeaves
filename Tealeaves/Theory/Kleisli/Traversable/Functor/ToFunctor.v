From Tealeaves Require Export
  Classes.Kleisli.Traversable.Functor.

Import Functor.Notations.
#[local] Generalizable Variables T.

(** * Kleisli traversable functor to functor *)
(******************************************************************************)

(** ** <<fmap>> operation *)
(******************************************************************************)
Module Operation.
  Section with_kleisli.

    Context
      (T : Type -> Type)
      `{Traverse T}.

  #[export] Instance Fmap_Traverse : Fmap T :=
      fun (A B : Type) (f : A -> B) => traverse T (fun A => A) f.

  End with_kleisli.
End Operation.

Import Operation.

(** ** <<Functor>> instance *)
(******************************************************************************)
Module Instances.

  Section with_kleisli.

    Context
      (T : Type -> Type)
      `{Kleisli.Traversable.Functor.TraversableFunctor T}.

    Lemma fmap_id : forall (A : Type),
        fmap T (@id A) = @id (T A).
    Proof.
      intros. unfold_ops @Fmap_Traverse.
      now rewrite (trf_traverse_id T).
    Qed.

    Lemma fmap_fmap : forall (A B C : Type) (f : A -> B) (g : B -> C),
        fmap T g ∘ fmap T f = fmap T (g ∘ f).
    Proof.
      intros. unfold_ops @Fmap_Traverse.
      change (traverse T (fun A : Type => A) g)
        with (fmap (fun A => A) (traverse T (fun A => A) g)).
      rewrite (trf_traverse_traverse T (fun A => A));
        try typeclasses eauto.
      fequal. now rewrite Mult_compose_identity1.
    Qed.

    #[export] Instance: Classes.Functor.Functor T :=
      {| fun_fmap_id := fmap_id;
        fun_fmap_fmap := fmap_fmap;
      |}.

  End with_kleisli.

End Instances.

(** ** Other properties *)
(******************************************************************************)
Section with_kleisli.

  Context
    (T : Type -> Type)
    `{Kleisli.Traversable.Functor.TraversableFunctor T}.

  (** *** Specification for <<fmap>> *)
  (******************************************************************************)
  Corollary fmap_to_traverse : forall (A B : Type) (f : A -> B),
      fmap T f = traverse T (fun A => A) f.
  Proof.
    reflexivity.
  Qed.

  (** *** Purity laws *)
  (******************************************************************************)
  Corollary traverse_purity {G1 G2} `{Applicative G2} `{Applicative G1} : forall A B (f : A -> G1 B),
      traverse T (G2 ∘ G1) (pure G2 ∘ f) = pure G2 ∘ traverse T G1 f.
  Proof.
    intros.
    assert (ApplicativeMorphism G1 (G2 ∘ G1) (@pure G2 H2 ○ G1)).
    { constructor; try typeclasses eauto.
      - intros. unfold_ops @Fmap_compose.
        now rewrite (app_pure_natural G2).
      - intros. reflexivity.
      - intros. unfold_ops @Mult_compose. cbn.
        rewrite <- (appmor_mult (fun A => A) G2 (G1 A0) (G1 B0) x y (ϕ := @pure G2 _ )).
        change ((mult (fun A1 : Type => A1) (x, y))) with (x, y).
        now rewrite (app_pure_natural G2). }
    now rewrite (trf_traverse_morphism T f (G1 := G1) (G2 := G2 ∘ G1) (ϕ := (fun A => @pure G2 _ (G1 A)))).
  Qed.

  (** *** Composition between <<traverse>> and <<fmap>> *)
  (******************************************************************************)
  Lemma fmap_traverse : forall (G1 : Type -> Type) (A B C : Type) `{Applicative G1}
                          (g : B -> C)
                          (f : A -> G1 B),
      fmap G1 (fmap T g) ∘ traverse T G1 f =
        traverse T G1 (fmap G1 g ∘ f).
  Proof.
    intros. unfold_ops @Fmap_Traverse.
    rewrite (trf_traverse_traverse T G1 (fun A => A));
      try typeclasses eauto.
    fequal. now rewrite Mult_compose_identity1.
  Qed.

  Lemma traverse_fmap: forall (G2 : Type -> Type) (A B C : Type) `{Applicative G2}
                         (g : B -> G2 C)
                         (f : A -> B),
      traverse T G2 g ∘ fmap T f =
        traverse T G2 (g ∘ f).
  Proof.
    intros. unfold_ops @Fmap_Traverse.
    change (traverse T G2 g)
      with (fmap (fun A => A) (traverse T G2 g)).
    rewrite (trf_traverse_traverse T (fun A => A) G2);
      try typeclasses eauto.
    fequal. now rewrite Mult_compose_identity2.
  Qed.

End with_kleisli.
