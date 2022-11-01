From Tealeaves.Classes Require Export
  Algebraic.DT.Functor
  Kleisli.DT.Functor.
From Tealeaves.Theory Require Export
  Kleisli.DT.Functor.DerivedInstances.

Import Product.Notations.
Import Comonad.Notations.
Import DT.Functor.Notations.

#[local] Generalizable Variables A B C.

Module Operations.
  Section with_kleisli.

    Context
      (E : Type)
      (T : Type -> Type)
      `{Fmapdt E T}.

    #[export] Instance Fmap_Fmapdt: Fmap T := fun A B f => fmapdt T (fun A => A) (f ∘ extract (E ×)).
    #[export] Instance Dist_Fmapdt: Dist T := fun G _ _ _ A => fmapdt T G (extract (E ×)).
    #[export] Instance Decorate_Fmapdt: Decorate E T := fun A => fmapdt T (fun A => A) (@id ((E ×) A)).

  End with_kleisli.
End Operations.

Import Operations.

Module Instances.

  Section with_functor.

    Context
      (E : Type)
      (T : Type -> Type)
      `{Kleisli.DT.Functor.DecoratedTraversableFunctor E T}.

    Export DerivedInstances.Operations.
    Export DerivedInstances.Instances.

    Lemma dec_dec : forall (A : Type),
        dec T ∘ dec T = fmap T (cojoin (E ×)) ∘ dec T (A := A).
    Proof.
      intros.
      unfold_ops @Decorate_Fmapdt.
      change_left (fmapd T (@id (E * (E * A))) ∘ fmapd T id).
      rewrite (dfun_fmapd2 E T).
      change_right (fmap T (coμ (prod E)) ∘ fmapd T (@id (E * A))).
      rewrite (fmap_fmapd T (fun A => A) (fun A => A)).
      fequal. now ext [e a].
    Qed.

    Lemma dec_extract : forall (A : Type),
        fmap T (extract (E ×)) ∘ dec T = @id (T A).
    Proof.
      intros.
      unfold_ops @Decorate_Fmapdt.
      unfold_ops @Fmap_Fmapdt.
      change_left (fmapd T (extract (prod E) ∘ extract (prod E)) ∘ fmapd T (@id (E * A))).
      rewrite (dfun_fmapd2 E T).
      reassociate ->. rewrite (extract_cobind (E ×)).
      apply (dfun_fmapd1 E T).
    Qed.

    Lemma dec_natural : Natural (@dec E T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros. unfold_ops @Fmap_compose.
        unfold_ops @Fmap_Fmapdt.
        unfold_ops @Decorate_Fmapdt.
        change
          (fmapd T (fmap (prod E) f ∘ extract (prod E)) ∘ fmapd T id =
             fmapd T id ∘ fmapd T (f ∘ extract (prod E))).
        rewrite (dfun_fmapd2 E T).
        rewrite (dfun_fmapd2 E T).
        reassociate ->. rewrite (extract_cobind (E ×)).
        now rewrite <- (fmap_to_cobind (E ×)).
    Qed.

    #[export] Instance: Algebraic.Decorated.Functor.DecoratedFunctor E T :=
      {| dfun_dec_natural := dec_natural;
         dfun_dec_dec := dec_dec;
         dfun_dec_extract := dec_extract;
      |}.

  (** *** Traversable functor instance *)
  (******************************************************************************)
  Lemma dist_natural_T : forall (G : Type -> Type) (H2 : Fmap G) (H3 : Pure G) (H4 : Mult G),
      Applicative G -> Natural (@dist T _ G H2 H3 H4).
  Proof.
    intros. constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros.
      unfold_ops @Fmap_compose @Dist_Fmapdt @Fmap_Fmapdt.
      change (@fmapdt E T _ (fun A0 : Type => A0) _ _ _)
        with (@fmapd E T _).
      rewrite (fmapd_fmapdt T G).
      rewrite (fmapdt_fmapd T G _ _ _).
      rewrite (cokleisli_id_l).
      rewrite (cobind_id (E ×)).
      unfold id. fequal.
      ext [e a]. unfold compose. cbn.
      compose near a on left.
      rewrite (fun_fmap_fmap G).
      reflexivity.
  Qed.

  Lemma dist_morph_T : forall (G1 G2 : Type -> Type) (H2 : Fmap G1) (H3 : Pure G1) (H4 : Mult G1) (H5 : Fmap G2)
                         (H6 : Pure G2) (H7 : Mult G2) (ϕ : forall A : Type, G1 A -> G2 A),
      ApplicativeMorphism G1 G2 ϕ -> forall A : Type, dist T G2 ∘ fmap T (ϕ A) = ϕ (T A) ∘ dist T G1.
  Proof.
    intros. unfold_ops @Dist_Fmapdt @Fmap_Fmapdt.
      change (@fmapdt E T _ (fun A0 : Type => A0) _ _ _)
        with (@fmapd E T _).
      inversion H1.
      rewrite (fmapdt_fmapd T G2 _ _ _).
      rewrite <- (kdtfun_morph E T).
      rewrite (cokleisli_id_l).
      reflexivity.
  Qed.

  Lemma dist_unit_T : forall A : Type,
      dist T (fun A0 : Type => A0) = @id (T A).
  Proof.
    intros. unfold_ops @Dist_Fmapdt.
    now rewrite (kdtfun_fmapdt1 E T).
  Qed.

  Lemma dist_linear_T : forall (G1 : Type -> Type) (H2 : Fmap G1) (H3 : Pure G1) (H4 : Mult G1),
      Applicative G1 ->
      forall (G2 : Type -> Type) (H6 : Fmap G2) (H7 : Pure G2) (H8 : Mult G2),
        Applicative G2 -> forall A : Type, dist T (G1 ∘ G2) (A := A) = fmap G1 (dist T G2) ∘ dist T G1.
  Proof.
    intros. unfold_ops @Dist_Fmapdt.
    rewrite (kdtfun_fmapdt2 E T).
    fequal. admit.
  Admitted.

  #[export] Instance: Algebraic.Traversable.Functor.TraversableFunctor T :=
    {| dist_natural := dist_natural_T;
       dist_morph := dist_morph_T;
       dist_unit := dist_unit_T;
       dist_linear := dist_linear_T;
    |}.

  Print Algebraic.DT.Functor.DecoratedTraversableFunctor.

  Lemma dtfun_compat_T : forall (G : Type -> Type) (H2 : Fmap G) (H3 : Pure G) (H4 : Mult G),
      Applicative G -> forall A : Type,
        dist T G ∘ fmap T (strength G) ∘ dec (A := G A) T = fmap G (dec T) ∘ dist T G.
  Proof.
    intros. unfold_ops @Dist_Fmapdt @Fmap_Fmapdt @Decorate_Fmapdt.
      change (@fmapdt E T _ (fun A0 : Type => A0) _ _ _)
        with (@fmapd E T _).
      rewrite (fmapd_fmapdt T G).
      rewrite (fmapdt_fmapd T G _ _ _).
      rewrite (fmapdt_fmapd T G _ _ _).
      rewrite (cobind_id (E ×)).
      rewrite (fun_fmap_id G).
      fequal. ext [e a].
      reflexivity.
  Qed.

  #[export] Instance: Algebraic.DT.Functor.DecoratedTraversableFunctor E T :=
    {| dtfun_compat := dtfun_compat_T;
    |}.

  End with_functor.

End Instances.

