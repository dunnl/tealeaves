From Tealeaves Require Export
  Classes.Algebraic.Decorated.Functor.

Import Product.Notations.

#[local] Generalizable Variables E A B.

(** * Miscellaneous properties of decorated functors *)
(******************************************************************************)
Section DecoratedFunctor_misc.

  Context
    (T : Type -> Type)
    `{DecoratedFunctor E T}.

  Theorem cobind_dec : forall `(f : E * A -> B),
      fmap T (cobind (E ×) f) ∘ dec T = dec T ∘ fmap T f ∘ dec T.
  Proof.
    intros. unfold_ops @Cobind_Cojoin. rewrite <- (fun_fmap_fmap T).
    reassociate ->. rewrite <- (dfun_dec_dec E T).
    reassociate <-.
    change (fmap T (fmap (E ×) f)) with (fmap (T ∘ (E ×)) f).
    now rewrite (natural (ϕ := @dec E T _)).
  Qed.

End DecoratedFunctor_misc.

(** * Decorated functor instance for [Environment] *)
(******************************************************************************)
Section DecoratedFunctor_Environment.

  Context
    {E : Type}.

  #[global] Instance Decorate_prod : Decorate E (prod E) := @cojoin (prod E) _.

  #[global, program] Instance DecoratedFunctor_prod : DecoratedFunctor E (prod E).

  Solve Obligations with (intros; now ext [? ?]).

End DecoratedFunctor_Environment.
