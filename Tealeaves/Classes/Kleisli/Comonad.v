From Tealeaves Require Export
  Classes.Functor
  Functors.Identity
  Functors.Compose.

Import Functor.Notations.

#[local] Generalizable Variables W A B C D.

(** * Comonads *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Class Extract (W : Type -> Type) :=
  extract : W ⇒ (fun A => A).

Class Cobind (W : Type -> Type) :=
  cobind : forall (A B : Type), (W A -> B) -> W A -> W B.

#[global] Arguments extract W%function_scope {Extract} {A}%type_scope.
#[global] Arguments cobind (W)%function_scope {Cobind} {A B}%type_scope _%function_scope _.

(** ** Co-Kleisli composition *)
(******************************************************************************)
Definition kc4 (W : Type -> Type) `{Cobind W}
  {A B C : Type} `(g : W B -> C) `(f : W A -> B) : (W A -> C) :=
  g ∘ @cobind W _ A B f.

#[local] Infix "⋆4" := (kc4 _) (at level 60) : tealeaves_scope.

(** ** Typeclasses *)
(******************************************************************************)
Class Comonad `(W : Type -> Type) `{Cobind W} `{Extract W} :=
    { kcom_cobind0 : forall `(f : W A -> B),
        @extract W _ B ∘ @cobind W _ A B f = f;
      kcom_cobind1 : forall (A : Type),
        @cobind W _ A A (@extract W _ A) = @id (W A);
      kcom_cobind2 : forall (A B C : Type) (g : W B -> C) (f : W A -> B),
        @cobind W _ B C g ∘ @cobind W _ A B f = @cobind W _ A C (g ⋆4 f)
    }.

(** * Derived functor instance *)
(******************************************************************************)
Module DerivedInstances.

  (** ** [map] as a special case of [bind] *)
  (******************************************************************************)
  #[export] Instance Map_Cobind (W : Type -> Type) `{Extract W} `{Cobind W} : Map W :=
  fun `(f : A -> B) => @cobind W _ A B (f ∘ @extract W _ A).

  (** ** Functor instance *)
  (******************************************************************************)
    #[export] Instance Functor_Comonad (W : Type -> Type) `{Comonad W} : Functor W.
    Proof.
      constructor.
      - intros. unfold transparent tcs.
        change (id ∘ ?x) with x.
        now rewrite (kcom_cobind1).
      - intros. unfold transparent tcs.
        rewrite (kcom_cobind2).
        unfold kc4.
        reassociate -> near (@cobind W _ A B (f ∘ @extract W _ A)).
        now rewrite (kcom_cobind0).
    Qed.

    (** ** Kleisli composition laws *)
    (******************************************************************************)
    Section kc4.

      Context
        `{Comonad W}
        (A B C : Type).

      Lemma kc4_40 : forall (g : W B -> C) (f : A -> B),
          g ⋆4 (f ∘ @extract W _ A) = g ∘ map W f.
      Proof.
        reflexivity.
      Qed.

      Lemma kc4_04 : forall (g : B -> C) (f : W A -> B),
          (g ∘ @extract W _ B) ⋆4 f = g ∘ f.
      Proof.
        intros. unfold kc4.
        reassociate ->.
        rewrite (kcom_cobind0).
        reflexivity.
      Qed.

      Lemma kc4_00 : forall (g : B -> C) (f : A -> B),
          (g ∘ @extract W _ B) ⋆4 (f ∘ @extract W _ A) = (g ∘ f) ∘ @extract W _ A.
      Proof.
        intros. unfold kc4.
        reassociate ->.
        rewrite (kcom_cobind0).
        reflexivity.
      Qed.

    End kc4.

End DerivedInstances.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆4" := (kc4 _) (at level 60) : tealeaves_scope.
End Notations.
