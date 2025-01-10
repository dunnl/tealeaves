From Tealeaves Require Export
  Classes.Categorical.Applicative.

#[local] Generalizable Variable T G A B C ϕ M.

(** * Traversable functor *)
(******************************************************************************)

(** ** The [traverse] operation *)
(******************************************************************************)
Class Traverse (T : Type -> Type) := traverse :
    forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
      (A B : Type), (A -> G B) -> T A -> G (T B).

#[global] Arguments traverse {T}%function_scope {Traverse} {G}%function_scope
  {H H0 H1} {A B}%type_scope _%function_scope _.

(** ** "Kleisli" composition *)
(******************************************************************************)
Definition kc2
  {G1 G2 : Type -> Type} `{Map G1} {A B C : Type} :
  (B -> G2 C) ->
  (A -> G1 B) ->
  (A -> (G1 ∘ G2) C) :=
  fun g f => map (F := G1) (A := B) (B := G2 C) g ∘ f.

#[local] Infix "⋆2" := (kc2) (at level 60) : tealeaves_scope.

(** ** Typeclasses *)
(******************************************************************************)
Class TraversableFunctor (T : Type -> Type) `{Traverse T} :=
  { trf_traverse_id : forall (A : Type),
      traverse (G := fun A => A) id = @id (T A);
    trf_traverse_traverse :
    forall `{Applicative G1} `{Applicative G2}
      (A B C : Type) (g : B -> G2 C) (f : A -> G1 B),
      map (traverse g) ∘ traverse f = traverse (T := T) (G := G1 ∘ G2) (g ⋆2 f);
    trf_traverse_morphism :
    forall `{morphism : ApplicativeMorphism G1 G2 ϕ} (A B : Type) (f : A -> G1 B),
      ϕ (T B) ∘ traverse f = traverse (ϕ B ∘ f);
  }.

(** ** Homomorphisms *)
(******************************************************************************)
Class TraversableMorphism
  (T U : Type -> Type)
  `{Traverse T}
  `{Traverse U}
  (ϕ : forall (A : Type), T A -> U A) :=
  { trvmon_hom : forall `{Applicative G}
      `(f : A -> G B),
      map (F := G) (ϕ B) ∘ @traverse T _ G _ _ _ A B f =
        @traverse U _ G _ _ _ A B f ∘ ϕ A;
  }.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆2" := (kc2) (at level 60) : tealeaves_scope.
End Notations.
