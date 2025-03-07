From Tealeaves Require Import
  Classes.EqDec_eq
  Classes.Categorical.DecoratedTraversableFunctor
  Classes.Kleisli.DecoratedTraversableFunctor
  CategoricalToKleisli.DecoratedFunctor
  CategoricalToKleisli.DecoratedTraversableFunctor
  Functors.List_Telescoping_General
  Backends.Common.Names
  Backends.Named.Common
  Functors.Constant
  Functors.Subset
  Kleisli.Theory.DecoratedTraversableFunctor
  Theory.DecoratedTraversableFunctor.

Import Subset.Notations.
Import Monoid.Notations.

Section alpha_equiv_local.

  Context
    `{T: Type -> Type}
    `{DecoratedTraversableFunctor (list name) T}.


  Definition alpha_equiv_local:
    list name * name -> list name * name -> Prop :=
    fun '(ctx0, nm0) '(ctx1, nm1) =>
      match (get_binding ctx0 nm0, get_binding ctx1 nm1) with
      | (Bound prefix0 _ _, Bound prefix1 _ _) =>
          if length prefix0 == length prefix1
          then True
          else False
      | _ => False
      end.

End alpha_equiv_local.

Section named_local_operations.

  Context
    (T: Type -> Type)
    `{Categorical.DecoratedTraversableFunctor.DecoratedTraversableFunctor (list name) T}.

  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.
  Import Kleisli.DecoratedTraversableFunctor.DerivedOperations.

  Definition alpha:
    T name -> T name -> Prop :=
    lift_relation_ctx alpha_equiv_local.

End named_local_operations.

(** Alpha on polymorphic terms *)
From Tealeaves Require Import
  Classes.Categorical.DecoratedTraversableFunctorPoly.

Section named_local_operations.

  Context
    (T: Type -> Type -> Type)
    `{Categorical.DecoratedTraversableFunctorPoly.DecoratedTraversableFunctorPoly T}.

  Import Theory.TraversableFunctor.

  Definition delete_binders {B V}:
    T B V -> T unit V :=
    map (F := fun B => T B V) (Map := Map2_2) (const tt).

  Require Import CategoricalToKleisli.TraversableFunctor.
  Import CategoricalToKleisli.TraversableFunctor.DerivedOperations.
  Require Import Classes.Categorical.TraversableFunctor2.
  Import TraversableFunctor2.ToMono.

  Definition related_except_binders {B1 B2 X Y: Type}
    (R: X -> Y -> Prop): T B1 X -> T B2 Y -> Prop :=
    fun t1 t2 => lift_relation R (delete_binders t1) (delete_binders t2).

End named_local_operations.

Section alpha_properties.

  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.

  Context
    (T: Type -> Type)
      `{Categorical.DecoratedTraversableFunctor.DecoratedTraversableFunctor (list name) T}
      `{ToCtxset_inst: ToCtxset (list name) T}
      `{! Compat_ToCtxset_Mapdt (list name) T}.

  Import CategoricalToKleisli.DecoratedFunctor.DerivedOperations.
  Import Theory.DecoratedTraversableFunctor.

  Lemma alpha_principle:
    forall (f: list name * name -> name)
      (t: T name),
      (forall (ctx: list name) (v: name),
          element_ctx_of (T := T) (ctx, v) t ->
          alpha_equiv_local (ctx, v) (ctx, f (ctx, v)))
      -> alpha T t (mapd (T := T) f t).
  Proof.
    introv Hrel.
    unfold alpha.
    unfold lift_relation_ctx.
    unfold compose.
    unfold precompose.
    assert (cut: dec T (mapd f t) = (map (cobind (W := prod (list name)) f) (dec T t))).
    { (* categorical identity. *)
      admit.
    }
    assert (cut2:
        (@dec (list atom) T
       (@DecoratedTraversableFunctor.DerivedOperations.Decorate_Mapdt (list atom) T
          (@Mapdt_Categorical (list atom) T H H0 H1)) atom
       (@mapd (list atom) T (@Mapd_Categorical (list atom) T H H0) atom atom f t)) =
          (map (cobind (W := prod (list name)) f) (dec T t))).
    { unfold lift_relation_ctx.
      unfold mapd, Mapd_Categorical.
      unfold compose.
      compose near t on right.
      Search cobind dec.
      rewrite cobind_dec.
      unfold compose.
      fequal.
      admit.
      typeclasses eauto.
    }
    rewrite cut2.
  Abort.

End alpha_properties.
