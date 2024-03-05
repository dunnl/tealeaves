(** This file implements the ordinary endofunctors of functional programming. *)
From Tealeaves Require Export
  Tactics.Prelude
  Misc.Setoids.

#[local] Open Scope signature_scope.
#[local] Generalizable Variables F G A B C f g.

#[local] Notation "F ⇒ G" := (forall A : Type, F A -> G A) (at level 50) : tealeaves_scope.

(** * Endofunctors *)
(******************************************************************************)
Class Map (F : Type -> Type) : Type :=
  map : forall (A B : Type) (f : A -> B), F A -> F B.

#[global] Arguments map {F}%function_scope {Map} {A B}%type_scope f%function_scope.
#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope.

Class Functor (F : Type -> Type) `{Map F}
              `{forall A, Eq A -> Eq (F A)} :=
  { functor_setoid `{Equiv A}: Equiv (F A);
    functor_proper `{Equiv A} `{Equiv B}
                   :> `(Proper ((equal A ==> equal B) ==> (equal (F A) ==> equal (F B)))
                               (@map F _ A B));
    fmap_id: forall `{Equiv A}, map F A A id == @id (F A);
    fmap_fmap `{Eq A} `{Eq B} `{Eq C}
              `{!Setoid_Morphism (g : B -> C)} `{!Setoid_Morphism (f : A -> B)} :
    map F A C (g ∘ f) == map F B C g ∘ map F A B f;
  }.

(** ** Natural transformations *)
(******************************************************************************)
Class Natural `{Map F} `{Map G}
              `{forall A, Eq A -> Eq (F A)}
              `{forall A, Eq A -> Eq (G A)}
              (ϕ : F ⇒ G) :=
  { natural_src : Functor F;
    natural_tgt : Functor G;
    natural : forall `(f : A -> B) `{Equiv A} `{Equiv B},
      map G A B f ∘ ϕ A == ϕ B ∘ map F A B f
  }.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "F ⇒ G" := (forall A : Type, F A -> G A) (at level 50) : tealeaves_scope.
End Notations.
