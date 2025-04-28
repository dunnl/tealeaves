From Tealeaves Require Import
  Classes.Kleisli.DecoratedTraversableFunctor
  Kleisli.Theory.DecoratedTraversableFunctor
  Backends.Nominal.Common.Binding.

Import List.ListNotations.

(** * Nominal Free Variables *)
(**********************************************************************)
Section FV.

  Context
    {T: Type -> Type}
    `{Mapdt (list name) T}
    `{! DecoratedTraversableFunctor (list name) T}.

  Definition FV_loc: list name * name -> list name :=
    fun '(ctx, x) => if get_binding ctx x then @nil name else [x].

  Definition FV: T name -> list name :=
    mapdReduce FV_loc.

  Import ContainerFunctor.Notations.
  Import DecoratedContainerFunctor.Notations.

  Context
    `{ToCtxset (list atom) T}
    `{! Compat_ToCtxset_Mapdt (list atom) T}
    `{Traverse T}.

  Import Theory.TraversableFunctor.
  Existing Instance ToSubset_Traverse.
  Import Theory.DecoratedTraversableFunctor.
  Existing Instance ToCtxset_Mapdt.

  Lemma FV_lift_local: forall (t: T name) (ctx: list atom) (a: atom),
      (ctx, a) ∈d t -> ~ a ∈ ctx -> a ∈ FV t.
  Proof.
    intros.
    unfold FV.
    compose near t.
    rewrite
      (mapdReduce_morphism (M1 := list atom) (M2 := Prop)
         (A := atom) (T := T) (E := list atom) (ϕ := @element_of list _ _ a)
         (morphism := Monoid_Morphism_element_list atom a)).
    change (Forany_ctx (T := T) (element_of a ∘ FV_loc) t).
    rewrite forany_ctx_iff.
    exists ctx. exists a. split.
    - assumption.
    - unfold compose, FV_loc.
      destruct (get_binding_spec_proof ctx a) as
        [[H_is_Unbound H_notin] | [prefix [postfix [H_is_Bound [ctxspec Hnin]]]]].
      { rewrite H_is_Unbound.
        rewrite element_of_list_one.
        reflexivity.
      }
      { rewrite H_is_Bound.
        exfalso.
        assert (a ∈ ctx).
        { subst.
          autorewrite with tea_list.
          tauto. }
        contradiction.
      }
  Qed.

End FV.
