From Tealeaves Require Export
  Classes.Functor
  Algebraic.Applicative.

Import Functor.Notations.
Import Applicative.Notations.

#[local] Generalizable Variable T U G ϕ A.

(** * Traversable functors *)
(******************************************************************************)
Section TraversableFunctor_operation.

  Context
    (F : Type -> Type).

  Class Dist :=
    dist : forall (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G}, F ○ G ⇒ G ○ F.

End TraversableFunctor_operation.

Section TraversableFunctor.

  Context
    (F : Type -> Type)
    `{Functor F}
    `{Dist F}.

  Class TraversableFunctor :=
    { trav_functor :> Functor F;
      dist_natural :> forall `{Applicative G},
          @Natural (F ∘ G) _ (G ∘ F) _ (dist F G);
      dist_morph : forall `{ApplicativeMorphism G1 G2 ϕ} A,
          dist F G2 A ∘ fmap F (ϕ A) = ϕ (F A) ∘ dist F G1 A;
      dist_unit :
        `(dist F (fun A => A) A = id);
      dist_linear : forall `{Applicative G1} `{Applicative G2},
          `(dist F (G1 ∘ G2) A = fmap G1 (dist F G2 A) ∘ dist F G1 (G2 A));
    }.

End TraversableFunctor.

#[global] Arguments dist F%function_scope {Dist} G%function_scope {H H0 H1} {A}%type_scope.

(** ** Distribution-respecting natural transformations *)
(******************************************************************************)
Section TraversableMorphism.

  Context
    `{TraversableFunctor T}
    `{TraversableFunctor U}.

  Class TraversableMorphism (ϕ : T ⇒ U) :=
    { trvmor_trv_F : TraversableFunctor T;
      trvmor_trv_G : TraversableFunctor U;
      trvmor_nat :> Natural ϕ;
      trvmor_hom : forall `{Applicative G},
          `(fmap G (ϕ A) ∘ dist T G = dist U G ∘ ϕ (G A));
    }.

End TraversableMorphism.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "'δ'" := (dist) : tealeaves_scope.
End Notations.
