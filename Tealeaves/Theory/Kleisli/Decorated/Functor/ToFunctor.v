From Tealeaves Require Export
  Classes.Kleisli.Decorated.Functor.

Import Functor.Notations.
Import Product.Notations.
#[local] Generalizable Variables E T.

Module Operation.
  Section with_kleisli.

    Context
      (T : Type -> Type)
      `{Fmapd E T}.

  #[export] Instance Fmap_Fmapd : Fmap T :=
      fun (A B : Type) (f : A -> B) => fmapd T (f ∘ extract (E ×)).

  End with_kleisli.
End Operation.

Import Operation.

Module Instance.

  Section with_kleisli.

    Context
      (T : Type -> Type)
        `{Kleisli.Decorated.Functor.DecoratedFunctor E T}.

    Lemma fmap_id : forall (A : Type),
        fmap T (@id A) = @id (T A).
    Proof.
      intros. unfold_ops @Fmap_Fmapd.
      now rewrite (dfun_fmapd1 E T).
    Qed.

    Lemma fmap_fmap : forall (A B C : Type) (f : A -> B) (g : B -> C),
        fmap T g ∘ fmap T f = fmap T (g ∘ f).
    Proof.
      intros. unfold_ops @Fmap_Fmapd.
      rewrite (dfun_fmapd2 E T).
      fequal. reassociate ->.
      now rewrite (extract_cobind (E ×)).
    Qed.

    #[export] Instance: Classes.Functor.Functor T :=
      {| fun_fmap_id := fmap_id;
        fun_fmap_fmap := fmap_fmap;
      |}.

    Lemma fmap_fmapd : forall (A B C : Type)
                         (g : B -> C)
                         (f : E * A -> B),
        fmap T g ∘ fmapd T f =
          fmapd T (g ∘ f).
    Proof.
      intros. unfold_ops @Fmap_Fmapd.
      rewrite (dfun_fmapd2 E T).
      reassociate ->.
      now rewrite (extract_cobind (E ×)).
    Qed.

    Lemma fmapd_fmap: forall (A B C : Type)
                        (g : E * B -> C)
                        (f : A -> B),
        fmapd T g ∘ fmap T f = fmapd T (g ∘ fmap (E ×) f).
    Proof.
      intros. unfold_ops @Fmap_Fmapd.
      rewrite (dfun_fmapd2 E T).
      rewrite <- (fmap_to_cobind (E ×)).
      reflexivity.
    Qed.

  End with_kleisli.

End Instance.
