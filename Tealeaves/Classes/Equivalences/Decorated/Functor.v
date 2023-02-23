From Tealeaves.Classes Require Export
  Decorated.Functor
  Kleisli.Decorated.Functor.

Import Product.Notations.
Import Comonad.Notations.

#[local] Generalizable Variables T E A B C.

Section operations.

  Context
    (E : Type)
    (T : Type -> Type)
    `{Fmapd E T}.

  #[export] Instance Decorate_Fmapd: Decorate E T := fun A => fmapd T (@id ((E ×) A)).

End operations.

Import Kleisli.Decorated.Functor.ToFunctor.

Section properties.

  Context
    (E : Type)
    (T : Type -> Type)
    `{Kleisli.Decorated.Functor.DecoratedFunctor E T}.

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

  #[export] Instance: Classes.Decorated.Functor.DecoratedFunctor E T :=
    {| dfun_dec_natural := dec_natural;
      dfun_dec_dec := dec_dec;
      dfun_dec_extract := dec_extract;
    |}.

End properties.

Import Kleisli.Decorated.Functor.ToFunctor.

Module Roundtrip1.
  
  Context
    `{fmapT : Fmap T}
    `{decT : Decorate E T}
    `{! Classes.Decorated.Functor.DecoratedFunctor E T}.

  #[local] Instance fmapd' : Fmapd E T := ToKleisli.Fmapd_dec E T.

  Definition fmap' : Fmap T := Fmap_Fmapd T.
  Definition dec' : Decorate E T := Decorate_Fmapd E T.

  Goal fmapT = fmap'.
  Proof.
    unfold fmap'. unfold_ops @Fmap_Fmapd.
    unfold fmapd, fmapd'.
    unfold_ops @ToKleisli.Fmapd_dec.
    ext A B f.
    rewrite <- (fun_fmap_fmap T).
    reassociate ->.
    rewrite (dfun_dec_extract E T).
    reflexivity.
  Qed.

  Goal decT = dec'.
  Proof.
    unfold dec'. unfold_ops @Decorate_Fmapd.
    unfold fmapd, fmapd'.
    unfold_ops @ToKleisli.Fmapd_dec.
    ext A.
    rewrite (fun_fmap_id T).
    reflexivity.
  Qed.

End Roundtrip1.

Module Roundtrip2.

  Context
    `{fmapdT : Fmapd E T}
    `{! Classes.Kleisli.Decorated.Functor.DecoratedFunctor E T}.

  #[local] Instance fmap' : Fmap T := Fmap_Fmapd T.
  #[local] Instance dec' : Decorate E T := Decorate_Fmapd E T.

  Definition fmapd' : Fmapd E T := ToKleisli.Fmapd_dec E T.

  Goal fmapdT = fmapd'.
  Proof.
    unfold fmapd'. unfold_ops @ToKleisli.Fmapd_dec.
    unfold fmap, fmap', dec, dec'.
    unfold_ops @Fmap_Fmapd.
    unfold_ops @Decorate_Fmapd.
    ext A B f.
    unfold_compose_in_compose.
    rewrite (dfun_fmapd2 E T).
    reassociate -> on right.
    rewrite (extract_cobind (E ×)).
    reflexivity.
  Qed.

End Roundtrip2.
