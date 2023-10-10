(** This file implements the ordinary endofunctors of functional programming. *)
From Tealeaves Require Export
  Tactics.Prelude.

#[local] Generalizable Variables F G A B.

#[local] Notation "F ⇒ G" := (forall A : Type, F A -> G A) (at level 50) : tealeaves_scope.

(** * Endofunctors *)
(******************************************************************************)
Class Map (F : Type -> Type) : Type :=
  map : forall (A B : Type) (f : A -> B), F A -> F B.

Class Functor (F : Type -> Type) `{Map F} : Type :=
  { fun_map_id : forall (A : Type),
      map A A (@id A) = @id (F A);
    fun_map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
      map B C g ∘ map A B f = map A C (g ∘ f);
  }.

#[global] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope.

(** ** Natural transformations *)
(******************************************************************************)
Class Natural `{Functor F} `{Functor G} (ϕ : F ⇒ G) :=
  { natural_src : Functor F;
    natural_tgt : Functor G;
    natural : forall `(f : A -> B),
      map G f ∘ ϕ A = ϕ B ∘ map F f
  }.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "F ⇒ G" := (forall A : Type, F A -> G A) (at level 50) : tealeaves_scope.
End Notations.
