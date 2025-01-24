From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableMonad.

Import Product.Notations.
Import Monad.Notations.
Import Comonad.Notations.
Import DecoratedTraversableMonad.Notations.

(** * Polymorphically Decorated Monads *)
(******************************************************************************)
Section DecoratedMonadPoly.

  (** ** Operations <<retp>> and <<binddp>> *)
  (******************************************************************************)
  Class RetP
    (T : Type -> Type -> Type) :=
    retp : forall WA A, A -> T WA A.

  Class BinddP
    (T : Type -> Type -> Type) :=
    binddp :
      forall (WA WB : Type) (A B : Type),
        (list WA * WA -> WB) ->
        (list WA * A -> T WB B) ->
        T WA A -> T WB B.

  (** ** Axioms *)
  (******************************************************************************)
  Section axioms.

    Context (T: Type -> Type -> Type).
    Context (WA WB: Type) (A B: Type).
    Context (ρ : list WA * WA -> WB).
    Context (σ : list WA * A -> T WB B).
    Context (BinddP_T: BinddP T).
    Context (RetP_T: RetP T).

    Definition binddP_axiom1 :=
      @binddp T _ WA WA A A
        (extract (W := ((list WA) ×)))
        (* discard context on binders *)
        (@retp T _ WA A ∘ extract (W := ((list WA) ×)))
      (* discard context on leaves and coerce to subterms *)
      = @id (T WA A).

    Definition binddP_axiom2 := forall (a: A),
        @binddp T _ WA WB A B ρ σ (retp WA A a) = σ (nil, a).


    Context (WC: Type) (C: Type).
    Context (ρ2 : list WB * WB -> WC).
    Context (σ3 : list WB * B -> T WC C).

  End axioms.

End DecoratedMonadPoly.
