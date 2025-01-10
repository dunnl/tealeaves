From Tealeaves Require Export
  Classes.Functor.

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

#[global] Arguments extract {W}%function_scope {Extract} {A}%type_scope.
#[global] Arguments cobind {W}%function_scope {Cobind} {A B}%type_scope _%function_scope _.

(** ** Co-Kleisli composition *)
(******************************************************************************)
Definition kc4 {W : Type -> Type} `{Cobind W}
  {A B C : Type} `(g : W B -> C) `(f : W A -> B) : (W A -> C) :=
  g ∘ @cobind W _ A B f.

#[local] Infix "⋆4" := (kc4) (at level 60) : tealeaves_scope.

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

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆4" := (kc4) (at level 60) : tealeaves_scope.
End Notations.
