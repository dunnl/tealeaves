
(** ** Lifting Relations *)
(**********************************************************************)
Section lift_relation.


  Context
    `{ret_inst: Return T}
    `{Map_T_inst: Map T}
    `{Traverse_T_inst: Traverse T}
    `{Bind_T_inst: Bind T T}
    `{Bindt_T_inst: Bindt T T}
    `{ToSubset_T_inst: ToSubset T}
    `{ToBatch_T_inst: ToBatch T}
    `{ToBatch6_T_inst: ToBatch6 T T}
    `{! Compat_Map_Bindt T T}
    `{! Compat_Traverse_Bindt T T}
    `{! Compat_Bind_Bindt T T}
    `{! Compat_ToSubset_Traverse T}
    `{! Compat_ToBatch_Traverse T}
    `{! Compat_ToBatch6_Bindt T T}.

  Context
    `{Monad_inst: ! TraversableMonad T}.

  Context
    {A B: Type}
      (R: A -> B -> Prop).

  Context (t: T (T A)) (u: (T (T B))).

  Instance Traverse_compose_T: Traverse (T ∘ T) :=
    fun G Gpure Gmap Gmult A B f t =>
      (traverse (T := T) (traverse (T := T) f) t).

  Lemma lift_relation_join1:
    lift_relation (X := T ∘ T) R =
      lift_relation (X := T) (lift_relation R (X := T)).
  Proof.
    unfold lift_relation.
    unfold_ops @Traverse_compose_T.
    reflexivity.
  Qed.

  Require Import KleisliToCategorical.Monad.
  Import KleisliToCategorical.Monad.DerivedOperations.

  (* Not equivalent  in general, only an implication *)
  Lemma lift_relation_join2:
    lift_relation (X := T ∘ T) R t u ->
      lift_relation (X := T) R (join t) (join u).
  Proof.
    unfold lift_relation.
    unfold_ops @Traverse_compose_T.
    unfold join, Join_Bind.
    pose (traverse_bind (G2 := subset) (U := T) (T := T) (T A) A B R id).
    compose near t.
    rewrite e.
    rewrite traverse_through_runBatch6.
    rewrite (bindt_through_runBatch6 (T := T)).
    unfold compose.
    (*
    enough (cut:
        @runBatch (T A) (T (T B)) subset Map_subset Mult_subset Pure_subset
    (@map subset Map_subset (T B) (T (T B)) (@ret T ret_inst (T B))
     ○ @traverse T Traverse_T_inst subset Map_subset Pure_subset Mult_subset A B R) (T (T B))
    (@toBatch6 T T ToBatch6_T_inst (T A) (T B) t) =
  @precompose (T (T B)) (T B) Prop (@bind T T Bind_T_inst (T B) B (@id (T B)))
    (@runBatch (T A) (T B) subset Map_subset Mult_subset Pure_subset
       (@traverse T Traverse_T_inst subset Map_subset Pure_subset Mult_subset A B R) (T B)
       (@toBatch6 T T ToBatch6_T_inst (T A) B t))).
    now rewrite cut.
    *)
    assert (tolist (@toBatch6 T T ToBatch6_T_inst (T A) (T B) t) =
              tolist (@toBatch6 T T ToBatch6_T_inst (T A) B t)).
  Abort.

  Corollary relation_respectful:
    forall (A B1 B2: Type) (R: B1 -> B2 -> Prop) (t: T A) (f: A -> T B1) (g: A -> T B2),
      (forall (a: A), a ∈ t -> lift_relation R (f a) (g a)) -> lift_relation R (bind f t) (bind g t).
  Proof.
    intros.
  Abort.

End lift_relation.
