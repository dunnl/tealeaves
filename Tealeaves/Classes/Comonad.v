From Tealeaves Require Export
  Classes.Functor
  Functors.Identity
  Functors.Compose.

Import Functor.Notations.

#[local] Generalizable Variables W A B C D.

(** * Comonads *)
(******************************************************************************)
Section Comonad_operations.

  Context
    (W : Type -> Type).

  Class Extract :=
    extract : W ⇒ (fun A => A).

  Class Cobind :=
    cobind : forall (A B : Type), (W A -> B) -> W A -> W B.

End Comonad_operations.

Definition cokcompose
  (W : Type -> Type) `{Cobind W}
  `(g : W B -> C) `(f : W A -> B) : (W A -> C) :=
  g ∘ cobind W A B f.

#[local] Notation "g co⋆ f" := (cokcompose _ g f) (at level 60) : tealeaves_scope.

Section Comonad.

  Context
    `(W : Type -> Type)
    `{Fmap W}
    `{Cobind W}
    `{Extract W}.

  Class Comonad :=
    { kcom_cobind0 : forall `(f : W A -> B),
        extract W B ∘ cobind W A B f = f;
      kcom_cobind1 : forall (A : Type),
        cobind W A A (extract W A) = @id (W A);
      kcom_cobind2 : forall `(g : W B -> C) `(f : W A -> B),
        cobind W B C g ∘ cobind W A B f = cobind W A C (g ∘ cobind W A B f);
    }.

End Comonad.

Arguments cobind _%function_scope {Cobind} {A B}%type_scope.
Arguments extract _%function_scope {Extract} {A}%type_scope.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "g 'co⋆' f" := (cokcompose _ g f) (at level 60) : tealeaves_scope.
End Notations.

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
