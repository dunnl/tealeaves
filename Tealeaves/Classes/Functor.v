(** This file implements the ordinary endofunctors of functional programming. *)
From Tealeaves Require Export
  Tactics.Prelude.

#[local] Generalizable Variables F G A B.

#[local] Notation "F ⇒ G" := (forall A : Type, F A -> G A) (at level 50) : tealeaves_scope.

(** * Endofunctors *)
(******************************************************************************)
Class Map (F : Type -> Type) : Type :=
  map : forall (A B : Type) (f : A -> B), F A -> F B.

#[global] Arguments map {F}%function_scope {Map} {A B}%type_scope f%function_scope.
#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope.

Class Functor (F : Type -> Type) `{map_instance : Map F} : Type :=
  { fun_map_id : forall (A : Type),
      map F A A (@id A) = @id (F A);
    fun_map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
      map F B C g ∘ map F A B f = map F A C (g ∘ f);
  }.

(** ** Natural transformations *)
(******************************************************************************)
Class Natural `{Map F} `{Map G} (ϕ : F ⇒ G) :=
  { natural_src : Functor F;
    natural_tgt : Functor G;
    natural : forall `(f : A -> B),
      map G A B f ∘ ϕ A = ϕ B ∘ map F A B f
  }.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "F ⇒ G" := (forall A : Type, F A -> G A) (at level 50) : tealeaves_scope.
End Notations.
