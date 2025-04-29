From Tealeaves Require Export
  Classes.Functor2
  Classes.Categorical.Monad.

#[local] Generalizable Variables T F W A B C.

(** * Monadic Bifunctors *)
(**********************************************************************)
Class Monad2
  (T: Type -> Type -> Type)
  `{Map2 T}
  `{forall B, Return (T B)}
  `{forall B, Join (T B)} :=
  {
    dmp_functor :: Functor2 T;
    dmp_monad :: forall B, Monad (T B);
    dmp_map_ret: forall B B' V V' (g: B -> B') (f: V -> V'),
      map2 g f ∘ ret (T := T B) (A := V) =
        ret (T := T B') (A := V') ∘ f;
    dmp_map_join: forall B B' V V' (g: B -> B') (f: V -> V'),
      map2 g f ∘ join (T := T B) (A := V) =
        join (T := T B') (A := V') ∘ map2 g (map2 g f);
  }.
