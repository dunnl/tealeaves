
(*


(** ** Basic simplifications *)
(******************************************************************************)
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

(** ** Misc *)
(******************************************************************************)
Ltac simplify_distribute_list_ops :=
  match goal with
  | |- context[?f (monoid_op (Monoid_op := Monoid_op_list) ?l1 ?l2)] =>
      unfold_ops @Monoid_op_list;
      progress (autorewrite with tea_list)
  | |- context[?f (monoid_op (Monoid_op := Monoid_op_subset) ?l1 ?l2)] =>
      unfold_ops @Monoid_op_subset;
      progress (autorewrite with tea_set)
  end.

(** ** Locally nameless *)
(******************************************************************************)
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
  | |- context[lc_loc] =>
      simplify_lc_loc
  end.

Ltac simplify_locally_nameless_top_level :=
  match goal with
  | |- context[free ?t] =>
      debug "free_to_foldMap";
      rewrite free_to_foldMap
  | |- context[FV ?t] =>
      debug "unfold_FV";
      unfold FV;
      rewrite free_to_foldMap
  | |- context[LC] =>
      debug "LC_spec";
      rewrite LC_spec
  | |- context[LCn] =>
      debug "LC_gap_spec";
      rewrite LCn_spec
  | |- context[lc_loc] =>
      debug "simplify_bound_or_free";
      simplify_lc_loc
  | |- context[subst] =>
      unfold subst
  | |- context[open] =>
      unfold open
  end.
*)

(*
(** * Autosimplifying expressions *)
(******************************************************************************)
(* Attempt to simplify an expression involving binddt, or core operations derived from binddt, by rewriting operations to binddt, calling the provided "simplify_binddt" tactic, then attempting to refold any definitions we started with *)
Ltac simplify_core_binddt_expression_with simplify_binddt :=
  first [ rewrite_core_ops_to_binddt
        | simplify_binddt ()
        | rewrite_binddt_to_core_ops
    ].
Ltac simplify_core_binddt_expression :=
  first [ rewrite_core_ops_to_binddt
        | cbn
        | rewrite_binddt_to_core_ops
    ].

Ltac simplify_pass1_with_simplify_binddt T simplify_binddt :=
  first [ simplify_locally_nameless_top_level
        | rewrite_core_ops_to_binddt
        | rewrite_derived_ops_to_binddt constr:(T)
        | simplify_binddt ()
    ].

Ltac simplify_pass2 :=
  first [ simplify_locally_nameless_leaves
        | simplify_applicative_const
        | simplify_monoid_units
        (* ^ monoid_units should be after const_functor,
           before distribute_list_ops *)
        | simplify_applicative_I
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
*)



Ltac simplify_extract :=
  match goal with
  | |- context[(?f ∘ extract) ⦿ ?w] =>
      debug "simpl_extract_preincr2";
      rewrite (extract_preincr2 f w)
  | |- context[(?f ∘ extract) (?w, ?a)] =>
      debug "simpl_extract_pair";
      change ((f ∘ extract) (w, a)) with (f a)
      (*
      change ((f ∘ extract) (w, a)) with
        ((f ∘ (extract ∘ pair w)) a);
      rewrite extract_pair
       *)
  | |- context[(?f ⦿ Ƶ)] =>
      debug "simpl_preincr_zero";
      rewrite (preincr_zero f)
  | |- context[(?f ⦿ ?x)] =>
      (* test whether x can be resolved as some Ƶ *)
      let T := type of x in
      change x with (Ƶ:T);
      debug "simpl_preincr_zero";
      rewrite preincr_zero
  end.



(*
Ltac simplify_binddt := cbn.

Ltac simplify_mapdt T :=
  rewrite (mapdt_to_binddt (T := T));
  simplify_binddt;
  rewrite <- (mapdt_to_binddt (T := T)).

Ltac simplify_foldMapd T :=
  match goal with
  | |- context[foldMapd (T := T) (M := ?M) (op := ?op) (unit := ?unit)] =>
      rewrite foldMapd_to_mapdt1;
      simplify_mapdt;
      rewrite <- foldMapd_to_mapdt1
  end.

Ltac simplify_LC T :=
  rewrite LCn_spec;
  unfold Forall_ctx;
  simplify_foldMapd T;
  fold Forall_ctx.

*)
