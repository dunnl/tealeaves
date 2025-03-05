From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableMonad
  Classes.Monoid
  Functors.Writer.

Import Applicative.Notations.
Import Monoid.Notations.
Import Product.Notations.

#[local] Generalizable Variables ϕ T W G A B C D F M.

Section dtm_to_dtm.

  Context
    {T: Type -> Type}
    `{DecoratedTraversableMonad W1 T}
    `{Monoid W2}
    (ϕ: W1 -> W2)
    `{! Monoid_Morphism W1 W2 ϕ}.

  #[export] Instance Binddt_Morphism: Binddt W2 T T :=
    fun G Gmap Gpure Gmult V1 V2 σ =>
      binddt (G := G) (T := T) (σ ∘ map_fst ϕ).

  #[export] Instance DTM_of_DTM: DecoratedTraversableMonad W2 T.
  Proof.
    constructor.
    - typeclasses eauto.
    - intros.
      unfold_ops @Binddt_Morphism.
      rewrite kdtm_binddt0.
      reassociate -> on left.
      fequal.
      unfold_ops @Return_Writer.
      unfold map_fst, compose.
      ext a.
      cbn.
      fequal.
      apply monmor_unit.
    - constructor.
      + intros.
        unfold_ops @Binddt_Morphism.
        reassociate -> on left.
        assert (Heq: extract (A := A) ∘ map_fst ϕ = extract (W := prod W1)).
        now ext [w a].
        rewrite Heq.
        apply kdtm_binddt1.
      + intros.
        unfold_ops @Binddt_Morphism.
        rewrite kdtm_binddt2.
        fequal.
        unfold kc7.
        ext [w a].
        unfold compose. cbn.
        fequal.
        fequal.
        unfold binddt at 2.
        fequal.
        unfold preincr, compose, incr.
        ext [w2 b].
        fequal.
        cbn.
        fequal.
        apply monmor_op.
      + intros.
        unfold_ops @Binddt_Morphism.
        apply kdtm_morph; auto.
  Qed.

End dtm_to_dtm.
