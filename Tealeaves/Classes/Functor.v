(** This file implements the ordinary endofunctors of functional programming. *)
From Tealeaves Require Export
  Prelude.

#[local] Generalizable Variables F G A B.

#[local] Notation "F ⇒ G" := (forall A : Type, F A -> G A) (at level 50) : tealeaves_scope.

(** * Endofunctors *)
(******************************************************************************)
Section Functor_operations.

  Context
    (F : Type -> Type).

  Class Fmap : Type :=
    fmap : forall (A B : Type) (f : A -> B), F A -> F B.

End Functor_operations.

Section Functor_class.

  Context
    (F : Type -> Type)
    `{Fmap F}.

  Class Functor : Prop :=
    { fun_fmap_id : forall (A : Type),
        fmap F A A (@id A) = @id (F A);
      fun_fmap_fmap : forall (A B C : Type) (f : A -> B) (g : B -> C),
        fmap F B C g ∘ fmap F A B f = fmap F A C (g ∘ f);
    }.

End Functor_class.

Arguments fmap F%function_scope {Fmap} {A B}%type_scope f%function_scope.

(** ** Natural transformations *)
(******************************************************************************)
Section natural_transformation_class.

  Context
    `{Functor F}
    `{Functor G}.

  Class Natural (ϕ : F ⇒ G) :=
    { natural_src : Functor F;
      natural_tgt : Functor G;
      natural : forall `(f : A -> B),
          fmap G f ∘ ϕ A = ϕ B ∘ fmap F f
    }.

End natural_transformation_class.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "F ⇒ G" := (forall A : Type, F A -> G A) (at level 50) : tealeaves_scope.
End Notations.
