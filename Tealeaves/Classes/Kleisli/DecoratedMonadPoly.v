From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableMonad.

Import Product.Notations.
Import Monad.Notations.
Import Comonad.Notations.
Import DecoratedTraversableMonad.Notations.

(** * Polymorphically decorated traversable monads *)
(******************************************************************************)
Section DecoratedFunctorPoly.

  Class BinddP
    (T : Type -> Type -> Type) :=
    binddp :
      forall (WA WB : Type) (A B : Type),
        (list WA * WA -> WB) ->
        (list WA * A -> T WB B) ->
        T WA A -> T WB B.

  Class RetP
    (T : Type -> Type -> Type) :=
    retp : forall WA A, A -> T WA A.

  Section axioms.

    Context (T: Type -> Type -> Type).
    Context (WA WB: Type) (A B: Type).
    Context (ρ : list WA * WA -> WB).
    Context (σ : list WA * A -> T WB B).
    Context (BinddP_T: BinddP T).
    Context (RetP_T: RetP T).

    Definition binddP_axiom1 :=
      @binddp T _ WA WA A A
        (extract (W := ((list WA) ×))) (* discard context on binders *)
        (@retp T _ WA A ∘ extract (W := ((list WA) ×))) (* discard context on leaves and coerce to subterms *)
      = @id (T WA A).

    Definition binddP_axiom2 := forall (a: A),
        @binddp T _ WA WB A B ρ σ (retp WA A a) = σ (nil, a).


    Context (WC: Type) (C: Type).
    Context (ρ2 : list WB * WB -> WC).
    Context (σ3 : list WB * B -> T WC C).

    Definition

End DecoratedFunctorPoly.



      { kmodd_bindd1 : forall (A : Type),
      @bindd W T U _ A A (ret ∘ extract) = @id (U A);
    kmodd_bindd2 : forall (A B C : Type) (g : W * B -> T C) (f : W * A -> T B),
      @bindd W T U _ B C g ∘ @bindd W T U _ A B f = @bindd W T U _ A C (g ⋆5 f);
  }.
