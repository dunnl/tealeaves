From Tealeaves Require Export
  Classes.Categorical.DecoratedFunctorPoly
  Classes.Categorical.Monad
  Functors.List
  Functors.Writer.

#[local] Generalizable Variables T F W A B C.

(** * Decorated Monads (Poly) *)
(**********************************************************************)
Class DecoratedMonadPoly
  (T: Type -> Type -> Type)
  `{Map2 T} `{DecoratePoly T}
  `{forall B, Return (T B)}
  `{forall B, Join (T B)} :=
  {
    dmp_functor :> Functor2 T;
    dmp_decorated :> DecoratedFunctorPoly T;
    dmp_monad :> forall B, Monad (T B);
    dmp_map_ret: forall B B' V V' (g: B -> B') (f: V -> V'),
      map2 g f ∘ ret (T := T B) (A := V) =
        ret (T := T B') (A := V') ∘ f;
    dmp_map_join: forall B B' V V' (g: B -> B') (f: V -> V'),
      map2 g f ∘ join (T := T B) (A := V) =
        join (T := T B') (A := V') ∘ map2 g (map2 g f);
    dmp_dec_ret: forall B V,
      decp ∘ ret (T := T B) (A := V) =
        ret (T := T (Z B)) (A := Z2 B V) ∘ ret (T := prod (list B));
    dmp_dec_join:
    forall (B V: Type),
      decp ∘ join (T := T B) (A := V) =
        join (T := T (Z B)) ∘ map2 id (shift2 ∘ map_snd decp)
          ∘ decp (B := B) (V := T B V);
  }.
