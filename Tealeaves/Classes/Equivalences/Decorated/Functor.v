From Tealeaves.Classes Require Export
  Algebraic.Decorated.Functor
  Kleisli.Decorated.Functor.
From Tealeaves.Theory Require Export
  Kleisli.Decorated.Functor.ToFunctor.

Import Product.Notations.
Import Comonad.Notations.

#[local] Generalizable Variables A B C.

Module Operations.
  Section with_kleisli.

    Context
      (E : Type)
      (T : Type -> Type)
      `{Fmapd E T}.

    #[export] Instance Fmap_Fmapd: Fmap T := fun A B f => fmapd T (f ∘ extract (E ×)).
    #[export] Instance Decorate_Fmapd: Decorate E T := fun A => fmapd T (@id ((E ×) A)).

  End with_kleisli.
End Operations.

Import Operations.

Module Instances.

  Section with_functor.

    Context
      (E : Type)
      (T : Type -> Type)
      `{Kleisli.Decorated.Functor.DecoratedFunctor E T}.

    Export ToFunctor.Operation.
    Export ToFunctor.Instance.

    Lemma dec_dec : forall (A : Type),
        dec T ∘ dec T = fmap T (cojoin (E ×)) ∘ dec T (A := A).
    Proof.
      intros.
      (* Merge LHS *)
      unfold_ops @Decorate_Fmapd.
      rewrite (dfun_fmapd2 E T).
      (* Merge RHS *)
      unfold_ops @Fmap_Fmapd.
      rewrite (dfun_fmapd2 E T).
      reassociate ->. rewrite (extract_cobind (E ×)).
      fequal. now ext [e a].
    Qed.

    Lemma dec_extract : forall (A : Type),
        fmap T (extract (E ×)) ∘ dec T = @id (T A).
    Proof.
      intros.
      unfold_ops @Decorate_Fmapd.
      unfold_ops @Fmap_Fmapd.
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
        unfold_ops @Fmap_Fmapd.
        unfold_ops @Decorate_Fmapd.
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

  End with_functor.

End Instances.

