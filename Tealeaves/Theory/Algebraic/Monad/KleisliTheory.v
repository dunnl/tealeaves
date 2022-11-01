From Tealeaves Require Export
  Classes.Algebraic.Monad
  Theory.Algebraic.Monad.ToKleisli.

Import Kleisli.Monad.Notations.
Import Functor.Notations.

#[local] Generalizable Variables A B C T F.

(** * Kleisli category laws *)
(** An interesting note here is that the left unit law of the monad
corresponds to the right identity law of the Kleisli category and vice versa. *)
(******************************************************************************)
Section Monad_kleisli_category.

  Context
    (T : Type -> Type)
    `{Algebraic.Monad.Monad T}
    {A B C D : Type}.

  Import Theory.Algebraic.Monad.ToKleisli.Operation.
  Import Theory.Algebraic.Monad.ToKleisli.Instance.

  (** ** Left identity law *)
  Theorem kleisli_id_l : forall (f : A -> T B),
      (@ret T _ B) ⋆ f = f.
  Proof.
    intros. unfold kcompose. now rewrite (kmon_bind1 T).
  Qed.

  (** ** Right identity law *)
  Theorem kleisli_id_r : forall (g : B -> T C),
      g ⋆ (@ret T _ B) = g.
  Proof.
    intros. unfold kcompose. now rewrite (kmon_bind0 T).
  Qed.

  (** ** Associativity law *)
  Theorem kleisli_assoc : forall (h : C -> T D) (g : B -> T C) (f : A -> T B),
      h ⋆ (g ⋆ f) = (h ⋆ g) ⋆ f.
  Proof.
    intros. unfold kcompose at 3.
    now rewrite <- (kmon_bind2 T).
  Qed.

End Monad_kleisli_category.
