From Tealeaves Require Export
  Classes.Categorical.DecoratedFunctorPoly
  Classes.Categorical.TraversableFunctor2
  Classes.Categorical.ApplicativeCommutativeIdempotent
  Classes.Categorical.Monad
  Classes.Categorical.DecoratedTraversableFunctorPoly
  Functors.List
  Functors.Writer.

#[local] Generalizable Variables T F G W A B C.

Section laws.

  Context (T: Type -> Type -> Type).

  Context
    `{Map2 T} `{DecoratePoly T} `{ApplicativeDist2 T}
    `{forall B, Return (T B)}
    `{forall B, Join (T B)}.

  Definition decpoly_ret: Prop :=
    forall (B V: Type),
      decp ∘ ret (T := T B) (A := V) =
        ret (T := T (Z B)) (A := Z2 B V) ∘ ret (T := prod (list B)).

  Definition decpoly_join: Prop :=
    forall (B V: Type),
      decp ∘ join (T := T B) (A := V) =
        join (T := T (Z B)) ∘ map2 id (shift2 ∘ map_snd decp)
          ∘ decp (B := B) (V := T B V).

  Definition dist2_join `{Applicative G}: Prop :=
    forall (B V: Type),
      dist2 ∘ join (T := T (G B)) (A := (G V)) =
        map (F := G) (join (T := T B)) ∘
          dist2 (T := T) (G := G) ∘
          map2 (F := T) id (dist2).

  Definition dist2_ret `{Applicative G}: Prop :=
    forall (B V: Type),
      dist2 ∘ ret (T := T (G B)) (A := G V) =
        map (F := G) (ret (T := T B) (A := V)).


  Definition dist2_decpoly_ci
     `{ApplicativeCommutativeIdempotent G}: Prop :=
    forall (B V: Type),
      dist2 (G := G) ∘ map2 (dist Z G) (dist2 (T := Z2)) ∘ (decp (B := G B) (V := G V)) =
        map (F := G) (decp (B := B) (V := V)) ∘ dist2 (T := T) (G := G).

End laws.

(** * Decorated-traversable monads *)
(**********************************************************************)
Class DecoratedTraversableMonadPoly
  (T: Type -> Type -> Type)
  `{Map2 T} `{DecoratePoly T} `{ApplicativeDist2 T}
  `{forall B, Return (T B)}
  `{forall B, Join (T B)} :=
  {
    xxx_functor :> Functor2 T;
    xxx_decorated :> DecoratedFunctorPoly T;
    xxx_traversable :> TraversableFunctor2 T;
    xxx_decoratedtraversable :> DecoratedTraversableFunctorPoly T;
    xxx_monad :> forall B, Monad (T B);
    xxx_map_ret: forall B B' V V' (g: B -> B') (f: V -> V'),
      map2 g f ∘ ret (T := T B) (A := V) =
        ret (T := T B') (A := V') ∘ f;
    xxx_dec_ret: forall B V,
      decp ∘ ret (T := T B) (A := V) =
        ret (T := T (Z B)) (A := Z2 B V) ∘ ret (T := prod (list B));
    xxx_dec_join:
    forall (B V: Type),
      decp ∘ join (T := T B) (A := V) =
        join (T := T (Z B)) ∘ map2 id (shift2 ∘ map_snd decp)
          ∘ decp (B := B) (V := T B V);
    xxx_dist2_ret:
    forall (B V: Type) `{Applicative G},
      dist2 ∘ ret (T := T (G B)) (A := G V) =
        map (F := G) (ret (T := T B) (A := V));
    xxx_dist2_join:
    forall (B V: Type) `{Applicative G},
      dist2 ∘ join (T := T (G B)) (A := (G V)) =
        map (F := G) (join (T := T B)) ∘
          dist2 (T := T) (G := G) ∘
          map2 (F := T) id (dist2);
  }.

