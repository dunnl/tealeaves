From Tealeaves Require Export
  Classes.Categorical.Comonad
  Classes.Categorical.ApplicativeCommutativeIdempotent
  Classes.Kleisli.TraversableFunctor.

#[local] Generalizable Variable T G A B C ϕ M.

Import TraversableFunctor.Notations.

(** * CI-Decorated Traversable functor *)
(******************************************************************************)

(** ** The [mapdt_ci] operation *)
(******************************************************************************)
Class Mapdt_CommIdem (Z : Type -> Type) (T : Type -> Type) :=
  mapdt_ci :
    forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
      (A B : Type), (Z A -> G B) -> T A -> G (T B).

#[global] Arguments mapdt_ci {Z T}%function_scope {Mapdt_CommIdem}
  {G}%function_scope {H H0 H1} {A B}%type_scope _%function_scope.

(** ** "Kleisli" composition *)
(******************************************************************************)
Section kleisli_composition.

  Context
    {Z: Type -> Type}
      `{Cojoin Z}
      `{Traverse Z}.

  Definition kc6_ci
    {G1 G2 : Type -> Type}
    `{Map G1} `{Pure G1} `{Mult G1} {A B C : Type}:
    (Z B -> G2 C) ->
    (Z A -> G1 B) ->
    (Z A -> (G1 ∘ G2) C) :=
    fun g f => map (F := G1) (A := Z B) (B := G2 C) g ∘
              traverse (T := Z) (G := G1) f ∘ cojoin (W := Z).

End kleisli_composition.

#[local] Infix "⋆6_ci" := (kc6_ci) (at level 60) : tealeaves_scope.

(** ** Typeclasses *)
(******************************************************************************)
Class DecoratedTraversableCommIdemFunctor
  (Z: Type -> Type) `{Cojoin Z} `{Extract Z} `{Traverse Z}
  (T : Type -> Type) `{! Mapdt_CommIdem Z T} :=
  { kdtfci_mapdt1 : forall (A : Type),
      mapdt_ci (G := fun A => A) extract = @id (T A);
    kdtfci_mapdt2 :
    forall `{ApplicativeCommutativeIdempotent G1}
      `{ApplicativeCommutativeIdempotent G2}
      {A B C : Type} (g : Z B -> G2 C) (f : Z A -> G1 B),
      map (mapdt_ci g) ∘ mapdt_ci (T := T) f =
        mapdt_ci (G := G1 ∘ G2) (g ⋆6_ci f);
    kdtfci_morph :
    forall `{ApplicativeMorphism G1 G2 ϕ}
      {A B : Type} (f : Z A -> G1 B),
      mapdt_ci (ϕ B ∘ f) = ϕ (T B) ∘ mapdt_ci f;
  }.

(** ** Notations *)
(******************************************************************************)
Module Notations.
  #[global] Infix "⋆6_ci" := (kc6_ci) (at level 60) : tealeaves_scope.
End Notations.
