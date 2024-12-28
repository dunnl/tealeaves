From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableMonad.

Import Product.Notations.
Import Monad.Notations.
Import Comonad.Notations.
Import DecoratedTraversableMonad.Notations.

(** * Polymorphically decorated traversable monads *)
(******************************************************************************)
Section PolyDecoratedTraverableMonad.

  Class Map
    (T : Type -> Type -> Type)
    (F : Type -> Type -> Type) :=
    substitute :
      forall (WA WB : Type) (G : Type -> Type)
        `{Map G} `{Pure G} `{Mult G}
        (A B : Type),
        (list WA * WA -> WB) ->
        (list WA * A -> G (T WB B))
        -> F WA A -> G (F WB B).

  #[local] Arguments substitute {T F}%function_scope {Substitute}
    {WA WB}%type_scope {G}%function_scope {H H0 H1} {A B}%type_scope
  (_ _)%function_scope _.


Definition kcompose_rename
  {WA WB WC} :
  (list WB * WB -> WC) ->
  (list WA * WA -> WB) ->
  (list WA * WA -> WC) :=
  fun ρg ρf '(ctx, wa) => ρg (hmap ρf ctx, ρf (ctx, wa)).

Definition kcompose_dtmp
  {A B C WA WB WC}
  `{Map G1} `{Pure G1} `{Mult G1}
  `{Map G2} `{Pure G2} `{Mult G2}
  `{Substitute T T} :
  (list WB * WB -> WC) ->
  (list WB * B -> G2 (T WC C)) ->
  (list WA * WA -> WB) ->
  (list WA * A -> G1 (T WB B)) ->
  (list WA * A -> G1 (G2 (T WC C))) :=
  fun ρg g ρf f '(wa, a) =>
    map (F := G1) (substitute (ρg ⦿ hmap ρf wa) (g ⦿ hmap ρf wa)) (f (wa, a)).


  Context
  (T : Type -> Type -> Type)
  `{forall B, Fmap (T B)} `{forall B, Return (T B)} `{forall B, Join (T B)}
  `{forall B, Decorate (list B) (T B)} `{forall B, Dist (T B)}.

  Class PolyDecoratedTraversableMonad :=
    { pdtmon_dtm :> forall B, DecoratedTraversableMonad (list B) (T B);
    }.

End PolyDecoratedTraverableMonad.

Import DT.Monad.Derived.

(** Now we verify that the sub-classes can be inferred as well. *)
(******************************************************************************)
Section test_typeclasses.

  Context
    (T : Type -> Type -> Type)
    `{PolyDecoratedTraversableMonad T}.

  Goal forall B, Functor (T B). typeclasses eauto. Qed.
  Goal forall B, DecoratedFunctor (list B) (T B). typeclasses eauto. Qed.
  Goal forall B, Functor (T B). typeclasses eauto. Qed.
  Goal forall B, SetlikeFunctor (T B). typeclasses eauto. Qed.
  Goal forall B, ListableFunctor (T B). typeclasses eauto. Qed.
  Goal forall B, TraversableFunctor (T B). typeclasses eauto. Qed.
  Goal forall B, DecoratedTraversableFunctor (list B) (T B). typeclasses eauto. Qed.
  Goal forall B, Monad (T B). typeclasses eauto. Qed.
  Goal forall B, DecoratedMonad (list B) (T B). typeclasses eauto. Qed.
  Goal forall B, SetlikeMonad (T B). typeclasses eauto. Qed.
  Goal forall B, ListableMonad (T B). typeclasses eauto. Qed.
  Goal forall B, TraversableMonad (T B). typeclasses eauto. Qed.

End test_typeclasses.
