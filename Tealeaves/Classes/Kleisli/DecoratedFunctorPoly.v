From Tealeaves Require Export
  Functors.List_Telescoping_General
  Functors.Z2.

Import Product.Notations.

(** * Polymorphically Decorated Functors *)
(******************************************************************************)
Section DecoratedFunctorPoly.

  (** ** Operation <<mapdp>> *)
  (******************************************************************************)
  Class MapdPoly
    (T: Type -> Type -> Type) :=
    mapdp:
      forall (WA WB: Type) (A B: Type),
        (list WA * WA -> WB) ->
        (list WA * A -> B) ->
        T WA A -> T WB B.

End DecoratedFunctorPoly.
