From Tealeaves Require Export
  Classes.Categorical.Applicative
  Classes.Kleisli.Comonad
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.TraversableFunctor
  Functors.Early.Reader.

Import Monoid.Notations.
Import Strength.Notations.
Import TraversableFunctor.Notations.
Import Comonad.Notations.
Import Product.Notations.

#[local] Generalizable Variables E T ϕ G A B C M.

(** * Decorated traversable functors *)
(******************************************************************************)

(** ** Operation *)
(******************************************************************************)
Class Mapdt (E : Type) (T : Type -> Type) :=
  mapdt : forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
            (A B : Type), (E * A -> G B) -> T A -> G (T B).

(* Suppress type parameters *)
#[global] Arguments mapdt {E}%type_scope {T}%function_scope {Mapdt}
  {G}%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.

(** ** Kleisli composition *)
(******************************************************************************)
Definition kc6
  {E A B C : Type}
  {G1 G2 : Type -> Type}
  `{Map G1} `{Pure G1} `{Mult G1}
  `{Map G2} `{Pure G2} `{Mult G2}
  (g : E * B -> G2 C)
  (f : E * A -> G1 B) :
  (E * A -> G1 (G2 C)) :=
  map (F := G1) (A := E * B) (B := G2 C) g ∘ strength ∘ cobind f.

#[local] Infix "⋆6" := kc6 (at level 60) : tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Class DecoratedTraversableFunctor
  (E : Type) (T : Type -> Type) `{Mapdt E T} :=
  { kdtfun_mapdt1 : forall (A : Type),
      mapdt (G := fun A => A) extract = @id (T A);
    kdtfun_mapdt2 :
    forall `{Applicative G1} `{Applicative G2}
      {A B C : Type} (g : E * B -> G2 C) (f : E * A -> G1 B),
      map (mapdt g) ∘ mapdt f = mapdt (G := G1 ∘ G2) (g ⋆6 f);
    kdtfun_morph : forall `{ApplicativeMorphism G1 G2 ϕ} {A B : Type} (f : E * A -> G1 B),
      mapdt (ϕ B ∘ f) = ϕ (T B) ∘ mapdt f;
  }.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆6" := kc6 (at level 60) : tealeaves_scope.
End Notations.
