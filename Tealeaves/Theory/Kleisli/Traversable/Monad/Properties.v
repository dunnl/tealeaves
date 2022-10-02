From Tealeaves Require Export
  Classes.Kleisli.Traversable.Monad.

Import Monad.Notations.

#[local] Generalizable Variables A B C T G.

Section with_kleisli.

  Context
    (T : Type -> Type)
      `{Monad T}.

  Lemma kcompose_tm_ret : forall `{Applicative G1} `{Applicative G2} `(g : B -> G2 C) `(f : A -> G1 B),
      (fmap G2 (ret T) ∘ g) ⋆tm (fmap G1 (ret T) ∘ f) = fmap (G1 ∘ G2) (ret T) ∘ (fmap G1 g ∘ f).
  Proof.
    intros. unfold_ops @Fmap_compose.
    reassociate <- on right. unfold_compose_in_compose.
    rewrite (fun_fmap_fmap G1).
    unfold kcompose_tm. reassociate <- on left.
    rewrite (fun_fmap_fmap G1).
    rewrite (ktm_bindt0 T); auto.
  Qed.

  Corollary kcompose_tm_ret_I : forall `(g : B -> C) `(f : A -> B),
      (ret T ∘ g) ⋆tm (ret T ∘ f) = ret T ∘ (g ∘ f).
  Proof.
    intros. change (@ret T _ C) with (fmap (fun A => A) (@ret T _ C)).
    change (@ret T _ B) with (fmap (fun A => A) (@ret T _ B)).
    rewrite (kcompose_tm_ret (G2 := fun A => A) (G1 := fun A => A)).
    reflexivity.
  Qed.

  Lemma kcompose_tm_ret2 : forall `{Applicative G2} `(g : B -> G2 (T C)) `(f : A -> B),
      g ⋆tm ret T ∘ f = g ∘ f.
  Proof.
    intros. unfold kcompose_tm.
    reassociate <- on left. change (fmap (fun A => A) ?g) with g.
    now rewrite (ktm_bindt0 T).
  Qed.

End with_kleisli.
