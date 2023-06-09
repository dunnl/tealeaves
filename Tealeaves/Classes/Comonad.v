From Tealeaves Require Export
  Classes.Functor
  Functors.Identity
  Functors.Compose.

Import Functor.Notations.

#[local] Generalizable Variables W A B C D.

(** * Derived functor instance *)
(******************************************************************************)
Module ToFunctor.

  Section operation.

    Context
      (W : Type -> Type)
      `{Extract W}
      `{Cobind W}.

    #[export] Instance Fmap_Cobind : Fmap W :=
      fun `(f : A -> B) => cobind W (f ∘ extract W).

  End operation.

  Section to_functor.

    Context
      (W : Type -> Type)
      `{Comonad W}.

    #[export] Instance: Functor W.
    Proof.
      constructor.
      - intros. unfold transparent tcs.
        change (id ∘ ?x) with x.
        now rewrite (kcom_cobind1 W).
      - intros. unfold transparent tcs.
        rewrite (kcom_cobind2 W).
        unfold cokcompose.
        reassociate -> near (cobind W (f ∘ extract W)).
        now rewrite (kcom_cobind0 W).
    Qed.

  End to_functor.

End ToFunctor.
