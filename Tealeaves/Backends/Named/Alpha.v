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

  Context
    (T: Type -> Type)
    `{Categorical.DecoratedTraversableFunctor.DecoratedTraversableFunctor (list name) T}.

  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.
  Import Classes.Kleisli.DecoratedTraversableFunctor.DerivedOperations.
  Import Theory.DecoratedTraversableFunctor.

  Print Instances ToCtxset.

  (*
  Lemma alpha_principle:
    forall (f: list name * name -> name)
      (t: T name),
      (forall (ctx: list name) (v: name),
          element_ctx_of (T := T) (ctx, v) t ->
          alpha_equiv_local (ctx, v) (ctx, f (ctx, v)))
      -> False.
  Proof.
    intros.
    Print Instances MapdPoly.
    Check alpha (T name) (mapdp (T := T) extract f t) t.
  Proof.
    intros.
    unfold alpha.
    replace ((traversep (T := T) (G := fun A => A -> Prop)
                (fun _ _: Z name => True) alpha_equiv_local) (decp t))
      with (mapdtp (G := fun A => A -> Prop)
              (B2 := Z name) (A2 := Z name) (fun _ _: Z name => True) alpha_equiv_local t).
    2:{  admit. }

    change (
    rewrite kdtfp_mapdtp2.
              with
  Qed.
  *)

End alpha_properties.
