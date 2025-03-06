From Tealeaves Require Import
  Classes.EqDec_eq
  Classes.Categorical.DecoratedTraversableFunctor
  Classes.Kleisli.DecoratedTraversableFunctor
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

Section alpha_properties.

  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.

  Context
    (T: Type -> Type)
      `{Categorical.DecoratedTraversableFunctor.DecoratedTraversableFunctor (list name) T}
      `{ToCtxset_inst: ToCtxset (list name) T}
      `{! Compat_ToCtxset_Mapdt (list name) T}.

  Import Classes.Kleisli.DecoratedTraversableFunctor.DerivedOperations.
  Import Theory.DecoratedTraversableFunctor.
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
    unfold mapd.
    unfold Mapd_Mapdt.
  Abort.

End alpha_properties.
