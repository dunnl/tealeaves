From Tealeaves Require Export
  Backends.LN
  Theory.DecoratedTraversableMonad
  Tactics.Debug.

Import LN.Notations.

#[local] Generalizable Variables G A B C.
#[local] Set Implicit Arguments.

(* Open Scope set_scope. *)

(*|
========================================
Extra lemmas for simplification support
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

(** ** Rewriting with binddt *)
(******************************************************************************)
Ltac rewrite_core_ops_to_binddt :=
  match goal with
  | |- context[map ?f ?t] =>
      debug "map_to_binddt";
      progress (rewrite bind_to_binddt)
  (* mapd/bind/traverse *)
  | |- context[bind ?f ?t] =>
      debug "bind_to_binddt";
      progress (rewrite bind_to_binddt)
  | |- context[mapd ?f ?t] =>
      debug "mapd_to_binddt";
      progress (rewrite mapd_to_binddt)
  | |- context[traverse ?f ?t] =>
      debug "traverse_to_binddt";
      progress (rewrite traverse_to_binddt)
  (* mapdt/bindd/bindt *)
  | |- context[mapdt ?f ?t] =>
      debug "mapdt_to_binddt";
      progress (rewrite mapdt_to_binddt)
  | |- context[bindd ?f ?t] =>
      debug "bindd_to_binddt";
      progress (rewrite bindd_to_binddt)
  | |- context[bindt ?f ?t] =>
      debug "bindt_to_binddt";
      progress (rewrite bindt_to_binddt)
  end.

Ltac rewrite_binddt_to_core_ops :=
  match goal with
  | |- context[binddt (G := fun A => A) (ret ∘ ?f ∘ extract)] =>
      debug "binddt_to_map";
      progress (rewrite <- map_to_binddt)
  | |- context[binddt (G := fun A => A) (ret (T := ?T) (A := ?A) ∘ extract)] =>
      change (ret (T := T) (A := A)) with (ret (T := T) (A := A) ∘ id);
      debug "binddt_to_map";
      progress (rewrite <- map_to_binddt)
  | |- context[binddt (G := fun A => A) (?f ∘ extract)] =>
      debug "binddt_to_bind";
      progress (rewrite <- bind_to_binddt)
  | |- context[binddt (G := fun A => A) (ret ∘ ?f)] =>
      debug "binddt_to_mapd";
      progress (rewrite <- mapd_to_binddt)
  | |- context[binddt (G := fun A => A)] =>
      debug "binddt_to_bindd";
      progress (rewrite <- bindd_to_binddt)
  | |- context[binddt (G := ?G) (map (F := ?G) ret ∘ ?f ∘ extract)] =>
      debug "binddt_to_traverse";
      progress (rewrite <- traverse_to_binddt)
  | |- context[binddt (G := ?G) (map (F := ?G) ret ∘ ?f)] =>
      debug "binddt_to_mapdt";
      progress (rewrite <- mapdt_to_binddt)
  | |- context[binddt (G := ?G) (?f ∘ extract)] =>
      debug "binddt_to_bindt";
      progress (rewrite <- bindt_to_binddt)
  end.

About tolist_to_binddt.
About tolist_to_foldMap.

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

(** ** Simplifying monoid ops *)
(******************************************************************************)
Ltac simplify_monoid_units :=
  match goal with
  | |- context[Ƶ ● ?m] =>
      debug "monoid_id_r";
      rewrite (monoid_id_r m)
  | |- context[?m ● Ƶ] =>
      debug "monoid_id_l";
      rewrite (monoid_id_l m)
  end.

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

(** ** Simplifying applicative functors *)
(******************************************************************************)

(** *** Constant functors *)
(******************************************************************************)
Ltac simplify_applicative_const :=
  match goal with
  | |- context [pure (F := const ?W) ?x] =>
      debug "pure_const";
      rewrite pure_const_rw
  | |- context[(ap (const ?W) ?x ?y)] =>
      debug "ap_const";
      rewrite ap_const_rw
  end.

Ltac simplify_map_const :=
  match goal with
  | |- context[map (F := const ?X) ?f] =>
      debug "map_const";
      rewrite map_const_rw
  end.

(** *** Identity functor *)
(******************************************************************************)
Ltac simplify_applicative_I :=
  match goal with
  | |- context[pure (F := fun A => A) ?x] =>
      debug "pure_I";
      change (pure (F := fun A => A) x) with x
  | |- context[ap (fun A => A) ?x ?y] =>
      debug "ap_I";
      change (ap (fun A => A) x y) with (x y)
  end.

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

(** * Deriving DTM laws expressions *)
(******************************************************************************)
Ltac rewrite_with_any :=
  match goal with
  | [H : _ = _ |- _] => rewrite H
  | [H : forall _, _ |- _] => progress rewrite H by now trivial
  end.

Ltac derive_dtm1 :=
  first [ reflexivity |
          let v := fresh "var" in
          now ext v].

Ltac derive_dtm2_with simplify_binddt :=
  repeat simplify_applicative_I; (* get rid of pure/ap *)
  try simplify_extract; (* account for any binders gone under *)
  try reflexivity; (* should solve <<ret>> case *)
  repeat rewrite_with_any; (* try to use IH wherever possible *)
  try easy. (* hopefully this solves it, otherwise let the user take over *)

Ltac derive_dtm2 := derive_dtm2_with ltac:(fun unit => cbn).

(* map f (pure x) ~~~> pure (f x)
   map f (x <⋆> y) ~~~> ((map f ∘ x) <⋆> y)
   map f ((x <⋆> y) <⋆> z) ~~~> ((map f ∘) ∘ x <⋆> y) <⋆> z
 *)
Ltac push_outer_map_into_pure :=
  repeat rewrite map_ap;
  (* Distribute outer <<map>> into the constructor *)
  rewrite app_pure_natural.
(* Fuse <<map f>> and the <<pure C>> into <<pure (f ∘ C)>> *)

Ltac dtm3_lhs :=
  push_outer_map_into_pure.

(* First pass on the RHS where we invoke the IH as much as possible *)
Ltac dtm3_rhs_kc7_preincr :=
  try match goal with
    | |- context[@preincr _ _ _ ((?G1 ∘ ?G2) ?x)] =>
        change ((G1 ∘ G2) x) with (G1 (G2 x))
    (* this step deals with composition blocking
           rewrite kc7_preincr *) end;
  repeat rewrite <- kc7_preincr.

Ltac dtm3_rhs_invoke_IH :=
  repeat match goal with
    | IH: context[binddt (_ ⋆7 _) ?t] |- _ =>
        rewrite <- IH
    end.

Ltac dtm3_rhs_step1 :=
  dtm3_rhs_kc7_preincr;
  dtm3_rhs_invoke_IH.

(* Second pass on the RHS where we invoke applicative laws *)
Ltac dtm3_rhs_unfold_ap_compose :=
  match goal with
  | |- context[ap (?G1 ∘ ?G2)] =>
      (rewrite_strat innermost
         (terms (ap_compose2 G2 G1)))
  end.

Ltac dtm3_rhs_one_constructor :=
  dtm3_rhs_unfold_ap_compose;
  push_outer_map_into_pure;
  rewrite <- ap_map;
  push_outer_map_into_pure.

Ltac dtm3_rhs_step2 :=
  unfold_ops @Pure_compose;
  repeat dtm3_rhs_one_constructor.

Ltac dtm3_rhs :=
  dtm3_rhs_step1;
  dtm3_rhs_step2.

Ltac dtm3_ret_case :=
  simplify_extract; (* deal with (g ⦿ Ƶ) *)
  reflexivity.

Ltac derive_dtm3 :=
  try solve [dtm3_ret_case];
  dtm3_lhs;
  dtm3_rhs;
  try easy.

Ltac derive_dtm4_simplify_hom :=
  repeat rewrite ap_morphism_1;
  rewrite appmor_pure.

Ltac derive_dtm4 :=
  try reflexivity; (* should solve <<ret>> case *)
  (* if not the <<ret>> case, push the homomorphism and use the IH *)
  derive_dtm4_simplify_hom;
  repeat rewrite_with_any; (* try to use IH wherever possible *)
  try easy. (* hopefully this solves it, otherwise let the user take over *)

Ltac setup_dtm_proof :=
  match goal with
  | |- context[(binddt (T := ?T) (U := ?U) ?f ∘ ret)] =>
      debug "setup_dtm_proof_guess_law1";
      derive_dtm1
  | |- context[binddt (T := ?T) (U := ?U) (ret ∘ extract) = id] =>
      debug "setup_dtm_proof_guess_law2";
      let t := fresh "t" in
      ext t;
      change (id ?t) with t;
      induction t;
      cbn;
      derive_dtm2
  | |- context[map (binddt (T := ?T) (U := ?U) ?g) ∘
                binddt (T := ?T) (U := ?U) ?f] =>
      debug "setup_dtm_proof_guess_law3";
      let t := fresh "t" in
      ext t;
      generalize dependent f;
      generalize dependent g;
      change ((?g ∘ ?f) t) with (g (f t));
      induction t; intros g f;
      cbn;
      derive_dtm3
  | H: ApplicativeMorphism ?G1 ?G2 ?ϕ
    |- context[(?ϕ ?B ∘ binddt ?f) = binddt (?ϕ ?B ∘ ?f)] =>
      debug "setup_dtm_proof_guess_law4";
      (assert (Applicative G1) by now inversion H);
      (assert (Applicative G2) by now inversion H);
      let t := fresh "t" in
      ext t;
      generalize dependent f;
      change ((?g ∘ ?f) t) with (g (f t));
      induction t; intro f;
      cbn;
      derive_dtm4
  end.

Ltac derive_dtm_law :=
  intros;
  setup_dtm_proof.

Ltac derive_dtm :=
  match goal with
  | |- DecoratedTraversableMonad ?W ?T =>
      constructor;
      try (timeout 1 typeclasses eauto);
      try (match goal with
           | |- DecoratedTraversableRightPreModule ?W ?T ?U =>
               constructor
           end);
      derive_dtm_law
  end.
