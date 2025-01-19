From Tealeaves Require Export
  Functors.List_Telescoping_General
  Functors.Z2.

Import Product.Notations.

(** * Polymorphically decorated traversable monads *)
(******************************************************************************)
Section DecoratedFunctorPoly.

  Class MapdPoly
    (T : Type -> Type -> Type) :=
    mapdp :
      forall (WA WB : Type) (A B : Type),
        (list WA * WA -> WB) ->
        (list WA * A -> B) ->
        T WA A -> T WB B.

End DecoratedFunctorPoly.


(*
Definition kcompose_rename
  {B1 B2 B3: Type}
  (ρ2: Z B2 -> B3)
  (ρ1: Z B1 -> B2):
  (Z B1 -> B3) := kc_Z _ _ _ _ _ _ _ _ _ _ _ ρ2 ρ1.

  fun ρg ρf '(ctx, wa) => ρg (hmap ρf ctx, ρf (ctx, wa)).
*)
