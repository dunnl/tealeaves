From Tealeaves Require Export
  Classes.Algebraic.Traversable.Functor.

#[local] Generalizable Variable T U F G ϕ A B.

(** * Basic properties of traversable functors *)
(******************************************************************************)

(** ** <<pure>> is an applicative homomorphism *)
(******************************************************************************)
Section pure_as_applicative_transformation.

  Context
    `{Applicative G}.

  Lemma pure_appmor_1 : forall A B (f : A -> B) (t : A),
      pure G (fmap (fun A : Type => A) f t) = fmap G f (pure G t).
  Proof.
    intros. now rewrite (app_pure_natural G).
  Qed.

  Lemma pure_appmor_2 : forall (A : Type) (a : A),
      pure G (pure (fun A => A) a) = pure G a.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma pure_appmor_3 : forall (A B : Type) (a : A) (b : B),
      pure G (mult (fun A => A) (a, b)) = mult G (pure G a, pure G b).
  Proof.
    unfold transparent tcs. intros. now rewrite (app_mult_pure G).
  Qed.

  #[export] Instance ApplicativeMorphism_pure :
    ApplicativeMorphism (fun A => A) G (@pure G _) :=
    {| appmor_natural := pure_appmor_1;
       appmor_pure := pure_appmor_2;
       appmor_mult := pure_appmor_3;
    |}.

End pure_as_applicative_transformation.

(** ** Other rules for <<pure>> *)
(******************************************************************************)
Section purity_law.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Corollary fmap_purity_1 `{Applicative G} : forall A,
    dist T G ∘ fmap T (pure G) (A := A) = pure G.
  Proof.
    intros. rewrite (dist_morph T (ϕ := @pure G _)).
    now rewrite (dist_unit T).
  Qed.

  Corollary fmap_purity_2 `{Applicative G1} `{Applicative G2} : forall `(f : A -> G1 B),
      dist T (G2 ∘ G1) ∘ fmap T (pure G2 ∘ f) = pure G2 ∘ dist T G1 ∘ fmap T f.
  Proof.
    intros. rewrite <- (fun_fmap_fmap T).
    reassociate <-. rewrite (dist_linear T).
    reassociate -> near (fmap T (pure G2)).
    rewrite fmap_purity_1.
    fequal. ext t. unfold compose.
    now rewrite (app_pure_natural G2).
  Qed.

End purity_law.
