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
  Theory.DecoratedTraversableFunctor
  Theory.LiftRel.DecoratedTraversableFunctor.

Import Subset.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables T.

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
      | (Unbound ctx0' nm0', Unbound ctx1' nm1') =>
          if nm0' == nm1'
          then True
          else False
      | (_, _) => False
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

  Lemma alpha_to_lift:
    alpha = lift_relation_ctx alpha_equiv_local.
  Proof.
    reflexivity.
  Qed.

End named_local_operations.

(** Alpha on polymorphic terms *)
From Tealeaves Require Import
  Classes.Categorical.DecoratedTraversableFunctorPoly
  Classes.Categorical.TraversableFunctor2
  CategoricalToKleisli.TraversableFunctor
  CategoricalToKleisli.TraversableFunctor.

Section delete_binders.

  Context
      `{Functor2.Functor2 T}.

  Definition delete_binders {B V}:
    T B V -> T unit V :=
    map (F := fun B => T B V) (Map := Map2_2) (const tt).

  Lemma delete_binders_map {B V1 V2} {f: V1 -> V2} (t: T B V1):
    delete_binders (map (Map := Map2_1) f t) =
      map f (delete_binders t).
  Proof.
    unfold delete_binders.
    compose near t.
    rewrite <- fun2_map22_map21_commute.
    reflexivity.
  Qed.

End delete_binders.

Section named_local_operations.

  Context
    (T: Type -> Type -> Type)
      `{Categorical.DecoratedTraversableFunctorPoly.DecoratedTraversableFunctorPoly T}.

  Import Theory.TraversableFunctor.

  Import DecoratedFunctorPoly.ToMono.
  Import CategoricalToKleisli.TraversableFunctor.DerivedOperations.
  Import TraversableFunctor2.ToMono.

  Definition lift_relation_poly {B1 B2 X Y: Type}
    (R: X -> Y -> Prop): T B1 X -> T B2 Y -> Prop :=
    fun t1 t2 => lift_relation R (delete_binders t1) (delete_binders t2).

  Definition lift_relation_ctx_poly {B1 B2 X Y: Type}
    (R: list B1 * X -> list B2 * Y -> Prop): T B1 X -> T B2 Y -> Prop :=
    fun t1 t2 => lift_relation R
                (delete_binders (dec (T B1) t1))
                (delete_binders (dec (T B2) t2)).


  Definition polymorphic_alpha:
    T name name -> T name name -> Prop :=
    lift_relation_ctx_poly (alpha_equiv_local).

End named_local_operations.

Section alpha_properties.

  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.
  Import CategoricalToKleisli.TraversableFunctor.DerivedOperations.

  Context
    (T: Type -> Type)
      `{Categorical.DecoratedTraversableFunctor.DecoratedTraversableFunctor (list name) T}
      `{ToCtxset_inst: ToCtxset (list name) T}
      `{! Compat_ToCtxset_Mapdt (list name) T}
      `{ToSubset T}
      `{! Compat_ToSubset_Traverse T}.

  Import CategoricalToKleisli.DecoratedFunctor.DerivedOperations.
  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.
  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedInstances.
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
    { unfold mapd, Mapd_Categorical.
      unfold compose.
      compose near (dec T t) on left.
      rewrite <- (natural (ϕ := @dec (list atom) T _ )).
      unfold compose.
      unfold_ops @Map_compose.
      compose near t.
      rewrite dfun_dec_dec.
      unfold compose.
      compose near (dec T t) on left.
      rewrite (fun_map_map).
      unfold cobind, Cobind_reader.
      fequal.
      now ext [e a].
    }
    rewrite cut.
    change (mapdt alpha_equiv_local t) with (traverse (T := T) (G := subset) alpha_equiv_local (dec T t)).
    rewrite <- lift_relation_rw.
    rewrite relation_natural2.
    rewrite <- lift_relation_ctx_spec.
    rewrite lift_relation_ctx_diagonal.
    rewrite forall_ctx_iff.
    unfold compose in *.
    intros.
    apply Hrel.
    assumption.
  Qed.

End alpha_properties.
