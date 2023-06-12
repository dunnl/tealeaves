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

  Class Map : Type :=
    map : forall (A B : Type) (f : A -> B), F A -> F B.

End Functor_operations.

Section Functor_class.

  Context
    (F : Type -> Type)
    `{Map F}.

  Class Functor : Prop :=
    { fun_map_id : forall (A : Type),
        map F A A (@id A) = @id (F A);
      fun_map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
        map F B C g ∘ map F A B f = map F A C (g ∘ f);
    }.

End Functor_class.

#[global] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope.

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
          map G f ∘ ϕ A = ϕ B ∘ map F f
    }.

End natural_transformation_class.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "F ⇒ G" := (forall A : Type, F A -> G A) (at level 50) : tealeaves_scope.
End Notations.
