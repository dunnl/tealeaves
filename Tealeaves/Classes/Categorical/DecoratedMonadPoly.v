From Tealeaves Require Export
  Classes.Categorical.DecoratedFunctorPoly
  Classes.Categorical.Monad2
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
    dmp_monad :> Monad2 T;
    dmp_dec_ret: forall B V,
      decp ∘ ret (T := T B) (A := V) =
        ret (T := T (Z B)) (A := Z2 B V) ∘ ret (T := prod (list B));
    dmp_dec_join:
    forall (B V: Type),
      decp ∘ join (T := T B) (A := V) =
        join (T := T (Z B)) ∘ map2 id (shift2 ∘ map_snd decp)
          ∘ decp (B := B) (V := T B V);
  }.
