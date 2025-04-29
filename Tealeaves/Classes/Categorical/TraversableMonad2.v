From Tealeaves Require Export
  Classes.Categorical.Monad2
  Classes.Categorical.TraversableFunctor2.

#[local] Generalizable Variables G.

(** * Traversable Monadic Bifunctors *)
(**********************************************************************)
Class TraversableMonad2
  (T: Type -> Type -> Type)
  `{Map2 T} `{ApplicativeDist2 T}
  `{forall B, Return (T B)}
  `{forall B, Join (T B)} :=
  {
    xxx_functor :: Functor2 T;
    xxx_traversable :: TraversableFunctor2 T;
    xxx_decoratedmonad :: Monad2 T;
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

