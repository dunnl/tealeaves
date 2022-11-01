From Tealeaves Require Export
  Classes.Algebraic.Decorated.Functor
  Classes.Kleisli.Decorated.Functor
  Data.Product.

Import Algebraic.Comonad.Notations.
Import Product.Notations.

#[local] Generalizable Variables E.

(** * Algebraic decorated functor to Kleisli decorated functor *)
(******************************************************************************)

(** ** Derived operation <<fmapd>>  *)
(******************************************************************************)
Module Operation.
  Section operation.

    Context
      (E : Type)
      (F : Type -> Type)
      `{Fmap F} `{Decorate E F}.

    #[export] Instance Fmapd_alg : Fmapd E F :=
      fun A B (f : E * A -> B) => fmap F f ∘ dec F.

    End operation.
End Operation.

Import Operation.

(** ** Kleisli laws for <<fmapd>> *)
(******************************************************************************)
Module Instance.

  Section with_functor.

    Context
      (F : Type -> Type)
        `{Algebraic.Decorated.Functor.DecoratedFunctor E F}.

    Theorem fmapd_id {A} : fmapd F (extract _) = @id (F A).
    Proof.
      introv. unfold_ops @Fmapd_alg.
      apply (dfun_dec_extract E F).
    Qed.

    Theorem fmapd_fmapd (A B C : Type) (g : E * B -> C) (f : E * A -> B) :
      fmapd F g ∘ fmapd F f = fmapd F (g co⋆ f).
    Proof.
      intros. unfold transparent tcs.
      reassociate <- on left.
      reassociate -> near (fmap F f).
      rewrite <- (natural (G := F ○ prod E)).
      reassociate <- on left.
      unfold transparent tcs.
      rewrite (fun_fmap_fmap F).
      reassociate -> on left.
      rewrite (dfun_dec_dec E F).
      reassociate <- on left.
      rewrite (fun_fmap_fmap F).
      reflexivity.
    Qed.

    #[export] Instance DecoratedFunctor: Kleisli.Decorated.Functor.DecoratedFunctor E F :=
      {| dfun_fmapd1 := @fmapd_id;
        dfun_fmapd2 := @fmapd_fmapd
      |}.

  End with_functor.

End Instance.
