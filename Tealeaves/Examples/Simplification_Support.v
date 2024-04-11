(*|
############################################################
Formalizing STLC with Tealeaves
############################################################
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Kleisli presentation
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This file gives a tutorial on proving the decorated traversable monad
laws the for the syntax of the simply-typed lambda calculus (STLC).

.. contents:: Table of Contents
   :depth: 2

============================
Imports and setup
============================

Since we are using the Kleisli typeclass hierarchy, we import modules under
the namespaces ``Classes.Kleisli`` and ``Theory.Kleisli.``
|*)
From Tealeaves Require Export
  Backends.LN
  Misc.NaturalNumbers
  Functors.List
  Theory.DecoratedTraversableMonad
  Tactics.Debug.

Export Monoid.Notations. (* Ƶ and ● *)
Export Kleisli.DecoratedTraversableMonad.Notations. (* ∈d *)
Export Misc.Subset.Notations. (* ∪ *)
Export Applicative.Notations. (* <⋆> *)
Export List.ListNotations. (* [] :: *)
(*
Export LN.Notations. (* operations *)
*)
Export LN.AtomSet.Notations.
Export LN.AssocList.Notations. (* one, ~ *)
Export Product.Notations. (* × *)
Export ContainerFunctor.Notations. (* ∈ *)
Export DecoratedContainerFunctor.Notations. (* ∈d *)

#[local] Generalizable Variables G A B C.
#[local] Set Implicit Arguments.

Open Scope set_scope.



(*|
========================================
Simplification support
========================================
|*)
Lemma pure_const_rw: forall {A} {a:A} {M} {unit:Monoid_unit M},
    pure (F := const M) (Pure := @Pure_const _ unit) a = Ƶ.
  reflexivity.
Qed.

Lemma ap_const_rw: forall {M} `{Monoid_op M} {A B} (x: const M (A -> B)) (y: const M A),
    ap (const M) x y = (x ● y).
  reflexivity.
Qed.

Lemma map_const_rw: forall A B (f: A -> B) X,
    map (F := const X) f = @id X.
Proof.
  reflexivity.
Qed.

Lemma free_loc_Bd: forall b,
    free_loc (Bd b) = [].
Proof.
  reflexivity.
Qed.

Lemma free_loc_Fr: forall x,
    free_loc (Fr x) = [x].
Proof.
  reflexivity.
Qed.

Lemma free_to_foldMap {T} `{Traverse T}: forall (t: T LN),
    free t = foldMap free_loc t.
Proof.
  reflexivity.
Qed.

Lemma eq_pair_preincr: forall (n: nat) {A} (a: A),
    eq (S n, a) ⦿ 1 = eq (n, a).
Proof.
  intros.
  ext [n' a'].
  unfold preincr, compose, incr.
  apply propositional_extensionality.
  rewrite pair_equal_spec.
  rewrite pair_equal_spec.
  intuition.
Qed.

Ltac rewrite_core_ops_to_binddt :=
  match goal with
  | |- context[bind ?f ?t] =>
      debug "bind_to_binddt";
      progress (rewrite bind_to_binddt)
  | |- context[bindd ?f ?t] =>
      debug "bindd_to_binddt";
      progress (rewrite bindd_to_binddt)
  end.

Ltac simplify_monoid_units :=
  match goal with
  | |- context[Ƶ ● ?m] =>
      debug "monoid_id_r";
      rewrite (monoid_id_r m)
  | |- context[?m ● Ƶ] =>
      debug "monoid_id_l";
      rewrite (monoid_id_l m)
  end.

Ltac simplify_const_functor :=
  match goal with
  | |- context [pure (F := const ?W) ?x] =>
      debug "pure_const";
      rewrite pure_const_rw
  | |- context[(ap (const ?W) ?x ?y)] =>
      debug "ap_const";
      rewrite ap_const_rw
  | |- context[map (F := const ?X) ?f] =>
      debug "map_const";
      rewrite map_const_rw

  end.

Ltac simplify_I_functor :=
  match goal with
  | |- context[pure (F := fun A => A) ?x] =>
      debug "pure_I";
      change (pure (F := fun A => A) x) with x
  | |- context[ap (fun A => A) ?x ?y] =>
      debug "ap_I";
      change (ap (fun A => A) x y) with (x y)
  end.

Ltac simplify_extract :=
  match goal with
  | |- context[(?f ∘ extract) ⦿ ?w] =>
      debug "extract_preincr2";
      rewrite extract_preincr2
  | |- context[(?f ∘ extract) (?w, ?a)] =>
      debug "extract_pair";
      change ((f ∘ extract) (w, a)) with
      ((f ∘ (extract ∘ pair w)) a);
      rewrite extract_pair
  | |- context[(?f ⦿ Ƶ)] =>
      rewrite (preincr_zero f)
  | |- context[(?f ⦿ ?x)] =>
      let T := type of x in
      change x with (Ƶ:T);
      rewrite preincr_zero
  end.

Ltac simplify_fn_composition :=
  match goal with
  | |- context [id ∘ ?f] =>
      debug "id ∘ f";
      change (id ∘ f) with f
  | |- context [?f ∘ id] =>
      debug "f ∘ id";
      change (f ∘ id) with f
  | |- context [id ?x] =>
      debug "unfold_id";
      change (id x) with x
  end.

Ltac simplify_distribute_list_ops :=
  match goal with
  | |- context[?f (monoid_op (Monoid_op := Monoid_op_list) ?l1 ?l2)] =>
      unfold_ops @Monoid_op_list;
      progress (autorewrite with tea_list)
  | |- context[?f (monoid_op (Monoid_op := Monoid_op_subset) ?l1 ?l2)] =>
      unfold_ops @Monoid_op_subset;
      progress (autorewrite with tea_set)
  end.

Ltac rewrite_derived_ops_to_binddt T :=
  match goal with
  (* tolist *)
  | |- context[tolist (F := T) ?t] =>
      debug "tolist_to_binddt";
      rewrite (tolist_to_binddt (T := T))
  (* elements *)
  | |- context[element_of (F := T) ?x ?t] =>
      debug "element_of_to_binddt";
      rewrite (element_of_to_binddt (T := T))
  | |- context[element_ctx_of (T := T) (?n, ?l) ?t] =>
      debug "element_ctx_of_to_binddt";
      rewrite (element_ctx_of_to_binddt (T := T))
  (* tosubset *)
  | |- context[tosubset (F := T) ?t] =>
      debug "tosubset_to_binddt";
      rewrite (tosubset_to_binddt (T := T))
  | |- context[toctxset (F := T) ?t] =>
      debug "toctxset_to_binddt";
      rewrite (toctxset_to_binddt (T := T))
  (* foldMap *)
  | |- context[foldMap (T := T) ?t] =>
      debug "foldMap_to_binddt";
      rewrite foldMap_to_traverse1, traverse_to_binddt
  | |- context[foldMapd (T := T) ?t] =>
      debug "foldMap_to_binddt";
      rewrite (foldMapd_to_mapdt1 (T := T)),
        (mapdt_to_binddt (T := T))
  (* quantifiers *)
  | |- context[Forall_ctx (T := T)  ?P] =>
      debug "Forall_to_foldMapd";
      unfold Forall_ctx
  end.

Ltac simplify_locally_nameless_leaves :=
  match goal with
  | |- context[free_loc (Fr ?x)] =>
      rewrite free_loc_Fr
  | |- context[free_loc (Bd ?b)] =>
      rewrite free_loc_Bd
  | |- context[?x ∈ [?y]] =>
      rewrite element_of_list_one
  | |- context[Forall_ctx ?P] =>
      unfold Forall_ctx
  | |- context[is_bound_or_free] =>
      simplify_is_bound_or_free
  end.

Ltac simplify_locally_nameless_top_level :=
  match goal with
  | |- context[free ?t] =>
      debug "free_to_foldMap";
      rewrite free_to_foldMap
  | |- context[freeset ?t] =>
      debug "unfold_freeset";
      unfold freeset;
      rewrite free_to_foldMap
  | |- context[locally_closed] =>
      debug "locally_closed_spec";
      rewrite locally_closed_spec
  | |- context[locally_closed_gap] =>
      debug "locally_closed_gap_spec";
      rewrite locally_closed_gap_spec
  | |- context[is_bound_or_free] =>
      debug "simplify_bound_or_free";
      simplify_is_bound_or_free
  | |- context[subst] =>
      unfold subst
  | |- context[open] =>
      unfold open
  end.


Ltac simplify_pass1_with_simplify_binddt T simplify_binddt :=
  first [ simplify_locally_nameless_top_level
        | rewrite_core_ops_to_binddt
        | rewrite_derived_ops_to_binddt constr:(T)
        | simplify_binddt ()
    ].


Ltac simplify_pass2 :=
  first [ simplify_locally_nameless_leaves
        | simplify_const_functor
        | simplify_monoid_units
        (* ^ monoid_units should be after const_functor,
           before distribute_list_ops *)
        | simplify_I_functor
        | simplify_fn_composition
        | simplify_extract
        | simplify_distribute_list_ops
    ].


Ltac dtm_law_pass :=
  match goal with
  | |- context[kc7 ?g ?f] =>
      unfold kc7
  end.

Ltac handle_atoms :=
  debug "handle_atoms";
  match goal with
  | |- context[atoms] =>
      debug "autorewrite_atoms";
      progress (autorewrite with tea_rw_atoms)
  | |- context[atoms (?l1 ● ?l2)] =>
      unfold_ops @Monoid_op_list;
      debug "autorewrite_list";
      progress (autorewrite with tea_rw_atoms)
  end.

Ltac introduce_induction :=
  let t := fresh "t" in
  ext t; induction t.

Ltac introduce_induction_with IH :=
  let t := fresh "t" in
  ext t; induction t using IH.

Ltac derive_dtm4_law_case :=
  repeat rewrite ap_morphism_1;
  rewrite appmor_pure.

Ltac derive_dtm_law_case_with_simplify_binddt simplify_binddt :=
  repeat (simplify_binddt ());
  repeat (simplify_pass2);
  repeat derive_dtm4_law_case;
  (fequal; try (trivial || reflexivity || auto)).

Ltac derive_dtm_law_with_simplify_binddt simplify_binddt :=
  intros;
  try introduce_induction;
  try solve [ derive_dtm_law_case_with_simplify_binddt
                simplify_binddt ].

Ltac derive_dtm_law_with_simplify_binddt_IH IH simplify_binddt :=
  intros;
  try introduce_induction_with IH;
  try solve [ derive_dtm_law_case_with_simplify_binddt
                simplify_binddt ].

Ltac simplify_subset_reasoning_leaves :=
  debug "handle_subset_reasoning_leaves";
  match goal with
  | |- context[(?a, ?b) = (?c, ?d)] =>
      (* This form occurs when reasoning about ∈d at <<ret>> *)
      rewrite pair_equal_spec
  | |- context[eq (S ?n, ?a) ⦿ 1] =>
      rewrite eq_pair_preincr
  end.


Ltac autosimplify_final_pass :=
  first [ simpl_subset
        | simpl_list
    ].

Ltac autosimplify_final_cleanup :=
  debug "autosimplify_final_cleanup";
  solve [ reflexivity
        | trivial
        | now handle_atoms
        | now simplify_subset_reasoning_leaves
        | debug "restoring to intuition";
          intuition
    ].

Ltac simplify_with_simplify_binddt T simplify_binddt :=
  intros;
  repeat simplify_pass1_with_simplify_binddt T simplify_binddt;
  repeat simplify_pass2;
  repeat autosimplify_final_pass;
  autosimplify_final_cleanup.
