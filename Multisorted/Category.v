From Tealeaves Require Export
     Util.Prelude.

From Tealeaves Require Import
     Cats.Classes.

Import Cats.Classes.Notations.
#[local] Open Scope category_scope.

Class Index : Type :=
  { K : Type;
    ix_dec_eq :> EqDec_eq K }.

(** * The category of constant k-families *)
(******************************************************************************)
Section category_kconst.

  Context
    `{Index}.

  Definition kid {A} := fun (k : K) (a : A) => a.

  #[global] Instance kconst_arrows : Arrows Type :=
    fun (a b : Type) => forall k : K, a -> b.

  #[global] Instance kconst_idents : Identities Type :=
    @kid.

  #[global] Instance kconst_comp : Composition Type :=
    fun (a b c : Type) (g : b ⟶ c) (f : a ⟶ b ) =>
      fun k => g k ∘ f k.

  #[global] Instance kconst_cat : Category Type.
  Proof.
    intros. constructor.
    - reflexivity.
    - intros. extensionality i. reflexivity.
    - intros. extensionality i. reflexivity.
  Qed.

End category_kconst.

Lemma compose_assoc `{Index} {a b c d : Type} {f : c ⟶ d} {g : b ⟶ c} {h : a ⟶ b} :
  f ⊙ (g ⊙ h) = (f ⊙ g) ⊙ h.
Proof.
  reflexivity.
Qed.

Lemma compose_const `{Index} {A B C : Type} {f : A -> B} {g : B -> C} :
  const g ⊙ const f = const (g ∘ f).
Proof.
  reflexivity.
Qed.

(** * Notations *)
(******************************************************************************)
Declare Scope tealeaves_multi_scope.
Delimit Scope tealeaves_multi_scope with tea_multi.

Module Notations.

  Infix "-k->" := (homset (Arrows:=kconst_arrows))
                      (at level 90, right associativity) : tealeaves_multi_scope.

  Notation "A ~k~> G B" :=
    (forall k, A -> G k B%type) (at level 70, G at level 5, B at level 5) : tealeaves_multi_scope.

  (** This notation is similar to but more general than <<⊙>> because it works even
  when <<g>> or <<f>> are dependently-typed (and hence not morphisms in the
  category of constant K-families). This is particularly intended for composition with Kleisli morphisms. *)
  Notation "g ◻ f" := (fun k => g k ∘ f k) (at level 50).

  Infix "⊙":= (@comp Type _ kconst_comp _ _ _)
                (at level 40, left associativity) : tealeaves_multi_scope.

  Notation "F ⇒ G" := (forall A : Type, F A -> G A)
                        (at level 50) : tealeaves_multi_scope.
End Notations.
