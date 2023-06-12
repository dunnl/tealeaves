From Tealeaves Require Export
  Classes.Functor
  Functors.Identity
  Functors.Compose.

Import Functor.Notations.

#[local] Generalizable Variables W A B C D.

(** * Operational typeclasses for comonads *)
(******************************************************************************)
Section operations.

  Context
    (W : Type -> Type).

  Class Extract :=
    extract : W ⇒ (fun A => A).

  Class Cobind :=
    cobind : forall (A B : Type), (W A -> B) -> W A -> W B.

End operations.

Section kc4.

  Context
    (W : Type -> Type)
    `{Cobind W}.

  Definition kc4
    {A B C : Type}
    `(g : W B -> C)
    `(f : W A -> B)
    : (W A -> C) :=
    g ∘ cobind W A B f.

End kc4.

#[local] Infix "⋆4" := (kc4 _) (at level 60) : tealeaves_scope.

Section Comonad.

  Context
    `(W : Type -> Type)
    `{Cobind W}
    `{Extract W}.

  Class Comonad :=
    { kcom_cobind0 : forall `(f : W A -> B),
        extract W B ∘ cobind W A B f = f;
      kcom_cobind1 : forall (A : Type),
        cobind W A A (extract W A) = @id (W A);
      kcom_cobind2 : forall (A B C : Type) (g : W B -> C) (f : W A -> B),
        cobind W B C g ∘ cobind W A B f = cobind W A C (g ⋆4 f)
    }.

End Comonad.

(** * Derived functor instance *)
(******************************************************************************)
Module DerivedInstances.

  Section instances.

    Context
      (W : Type -> Type)
      `{Extract W}
      `{Cobind W}.

    #[export] Instance Map_Cobind : Map W :=
      fun `(f : A -> B) => cobind W A B (f ∘ extract W A).

    Context
      `{! Comonad W}.

    #[export] Instance Functor_Comonad : Functor W.
    Proof.
      constructor.
      - intros. unfold transparent tcs.
        change (id ∘ ?x) with x.
        now rewrite (kcom_cobind1 W).
      - intros. unfold transparent tcs.
        rewrite (kcom_cobind2 W).
        unfold kc4.
        reassociate -> near (cobind W A B (f ∘ extract W A)).
        now rewrite (kcom_cobind0 W).
    Qed.

  End instances.

End DerivedInstances.

(** * Notations *)
(******************************************************************************)
Module Notations.

  Infix "⋆4" := (kc4 _) (at level 60) : tealeaves_scope.

End Notations.
