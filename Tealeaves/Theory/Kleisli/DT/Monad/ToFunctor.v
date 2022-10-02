From Tealeaves Require Import
  Classes.Kleisli.DT.Monad
  Theory.Kleisli.Decorated.Prepromote.

Import Functor.Notations.
Import Product.Notations.
Import DT.Monad.Notations.

#[local] Generalizable Variable W.

Module Operation.
  Section with_kleisli.

    Context
      (T : Type -> Type)
      `{Binddt W T T}
      `{Return T}.

  #[export] Instance Fmap_Binddt : Fmap T :=
      fun (A B : Type) (f : A -> B) => binddt T (fun A => A) (ret T ∘ f ∘ extract (W ×)).

  End with_kleisli.
End Operation.

Import Operation.

Module Instance.

  Section with_monad.

    Context
      (T : Type -> Type)
      `{DT.Monad.Monad W T}.

    Lemma fmap_id : forall (A : Type),
        fmap T (@id A) = @id (T A).
    Proof.
      intros. unfold_ops @Fmap_Binddt.
      change (ret T ∘ id) with (ret T (A := A)).
      now rewrite (kdtm_binddt1 W T).
    Qed.

    Lemma fmap_fmap : forall (A B C : Type) (f : A -> B) (g : B -> C),
        fmap T g ∘ fmap T f = fmap T (g ∘ f).
    Proof.
      intros. unfold_ops @Fmap_Binddt.
      change (binddt T (fun A0 : Type => A0) (ret T ∘ g ∘ extract (prod W)))
        with (fmap (fun A => A) (binddt T (fun A0 : Type => A0) (ret T ∘ g ∘ extract (prod W)))).
      rewrite (kdtm_binddt2 W T _ _ _ (G1 := fun A => A) (G2 := fun A => A)).
      fequal.
      - now rewrite Mult_compose_identity1.
      - admit.
    Admitted.

    #[export] Instance: Classes.Functor.Functor T :=
      {| fun_fmap_id := fmap_id;
        fun_fmap_fmap := fmap_fmap;
      |}.

    Lemma fmap_binddt: forall (G1 : Type -> Type) (A B C : Type) `{Applicative G1}
                         (g : B -> C)
                         (f : W * A -> G1 (T B)),
        fmap G1 (fmap T g) ∘ binddt T G1 f =
          binddt T G1 (fmap G1 (fmap T g) ∘ f).
    Proof.
      intros. unfold_ops @Fmap_Binddt.
    rewrite (kdtm_binddt2 W T A B C (G1 := G1) (G2 := fun A => A)).
    fequal.
    - now rewrite Mult_compose_identity1.
    - ext [w a]. cbn. now rewrite prepromote_extract.
  Qed.


  Lemma binddt_fmap: forall (G2 : Type -> Type) (A B C : Type) `{Applicative G2}
                       (g : W * B -> G2 (T C))
                       (f : A -> B),
      binddt T G2 g ∘ fmap T f =
        binddt T G2 (fun '(w, a) => g (w, f a)).
  Proof.
    intros. unfold_ops @Fmap_Binddt.
    change (binddt T G2 g) with (fmap (fun A => A) (binddt T G2 g)).
    rewrite (kdtm_binddt2 W T A B C (G1 := fun A => A)).
    fequal. now rewrite Mult_compose_identity2.
    unfold kcompose_dtm. ext [w a].
    change (fmap (fun A => A) ?f) with f.
    unfold compose; cbn.
    compose near (f a) on left.
    rewrite (kdtm_binddt0 W T _ _ _ (G := G2)).
    cbv. now simpl_monoid.
  Qed.

  End with_monad.

End Instance.
