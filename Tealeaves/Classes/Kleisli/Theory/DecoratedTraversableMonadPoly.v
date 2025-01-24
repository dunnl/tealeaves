From Tealeaves Require Export
  Classes.Kleisli.TraversableFunctorPoly
  Classes.Kleisli.DecoratedTraversableFunctorPoly
  Classes.Kleisli.DecoratedTraversableMonadPoly
  Functors.Constant
  Functors.Subset.

Import Subset.Notations.

Import DecoratedTraversableMonadPoly.DerivedOperations.

(** * "Element of" relations *)
(******************************************************************************)
Section element_of.

  Context
    `{T: Type -> Type -> Type}
      `{DecoratedTraversableMonadPoly T}.

  Definition binder_of_ctx {A B: Type}:
    T B A -> list B * B -> Prop :=
    mapdtp (B2 := False) (A2 := False)
      (G := const (subset (list B * B)))
      (Gpure := Pure_const) (Gmult := Mult_const)
      (@eq (list B * B))
      (const (const False)).

  Definition leaf_of_ctx {A B: Type}:
    T B A -> list B * A -> Prop :=
    mapdtp (B2 := False) (A2 := False)
      (G := const (subset (list B * A)))
      (Gpure := Pure_const) (Gmult := Mult_const)
      (const (const False))
      (@eq (list B * A)).

  Definition binder_of {A B: Type}:
    T B A -> B -> Prop :=
    traversep (B2 := False) (A2 := False)
      (G := const (subset B))
      (Gpure := Pure_const) (Gmult := Mult_const)
      (@eq B)
      (const (const False)).

  Definition leaf_of {A B: Type}:
    T B A -> A -> Prop :=
    traversep (B2 := False) (A2 := False)
      (G := const (subset A))
      (Gpure := Pure_const) (Gmult := Mult_const)
      (const (const False))
      (@eq A).

End element_of.

(** * Properties of element relation *)
(******************************************************************************)
Section leaf_of.

  Context
    `{T: Type -> Type -> Type}
      `{DecoratedTraversableMonadPoly T}.

  Lemma leaf_of_ctx1:
    forall (B A: Type) (t: T B A)
      (ctx: list B) (leaf: A),
      leaf_of_ctx t (ctx, leaf) -> False.
  Abort.

End leaf_of.

