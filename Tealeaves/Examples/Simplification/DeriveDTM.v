From Tealeaves Require Export
  Theory.DecoratedTraversableMonad
  Examples.Simplification.Support
  Examples.Simplification.Binddt.

Import DecoratedTraversableMonad.Notations.

(** * Deriving DTM laws expressions *)
(******************************************************************************)
Ltac derive_dtm_custom_IH := constr:(tt).

Ltac induction_term t :=
  let custIH := derive_dtm_custom_IH in
  let T := type of custIH in
  match T with
  | unit =>
      debug "derive_dtm|Using standard induction";
      induction t
  | _ =>
      debug "derive_dtm|Using custom induction principle";
      induction t using custIH
  end.

Ltac derive_dtm_solve_ret_case :=
  solve [repeat simplify_post_binddt_ret; reflexivity ].

(** ** Proving the first law *)
(******************************************************************************)
Ltac derive_dtm1 :=
  first [ reflexivity |
          let v := fresh "var" in
          now ext v].

(** ** Proving the second law *)
(******************************************************************************)
Ltac derive_dtm2_ret_case :=
  debug "derive_dtm2_ret_case";
  cbn_binddt;
  derive_dtm_solve_ret_case;
  debug "derive_dtm2_ret_case_finished".

Ltac derive_dtm2_IH_step :=
  debug "derive_dtm2_IH_step";
  simplify_binddt_core;
  repeat simplify_applicative_I;
  repeat rewrite_with_any; (* try to use IH wherever possible *)
  try easy; (* hopefully this solves it, otherwise let the user take over *)
  repeat fequal;
  debug "derive_dtm2_IH_step_finished".

Ltac assert_match_dtm2 :=
  match goal with
  | |- context[binddt (T := ?T) (U := ?U) (ret ∘ extract) = id] =>
      debug "assert_match_dtm2|match"
  | |- _ => fail "assert_match_setup|no match"
  end.

Ltac derive_dtm2_setup :=
  intros;
  let t := fresh "t" in
  ext t;
  change (id ?t) with t;
  induction_term t.

Ltac derive_dtm2 :=
  assert_match_dtm2;
  derive_dtm2_setup;
  if_goal_match_binddt_ret
    derive_dtm2_ret_case
    derive_dtm2_IH_step.

(** ** Proving the third law *)
(******************************************************************************)

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

Ltac dtm3_push_map_right_to_left :=
  rewrite <- ap_map;
  push_outer_map_into_pure.

Ltac dtm3_rhs_one_constructor :=
  dtm3_rhs_unfold_ap_compose;
  push_outer_map_into_pure;
  dtm3_push_map_right_to_left.

Ltac dtm3_rhs_step2 :=
  unfold_ops @Pure_compose;
  repeat dtm3_rhs_one_constructor.

Ltac dtm3_rhs :=
  dtm3_rhs_step1;
  dtm3_rhs_step2.

Ltac derive_dtm3_ret_case :=
  debug "derive_dtm3|ret case setup";
  unfold kc7;
  do 2 simplify_binddt_core;
  try simplify_preincr_zero;
  reflexivity;
  debug "derive_dtm3|ret case end".

Ltac derive_dtm3_IH_step :=
  debug "derive_dtm3|IH step start";
  do 2 simplify_binddt_core;
  dtm3_lhs;
  dtm3_rhs;
  try easy;
  debug "derive_dtm3|IH step finished".

Ltac assert_match_dtm3 :=
  match goal with
  | |- context[map (binddt (T := ?T) (U := ?U) ?g) ∘
                binddt (T := ?T) (U := ?U) ?f] =>
      debug "setup_dtm_proof_guess_law3";
      infer_applicative_functors
  | |- _ => fail "derive_dtm3_setup: no match"
  end.

Ltac derive_dtm3_setup :=
  debug "derive_dtm3|setup";
  assert_match_dtm3;
  let t := fresh "t" in
  ext t;
  match goal with
  | |- context[map (binddt (T := ?T) (U := ?U) ?g) ∘
                binddt (T := ?T) (U := ?U) ?f] =>
      generalize dependent f;
      generalize dependent g;
      change ((?g ∘ ?f) t) with (g (f t));
      induction_term t; intros g f
  end.

Ltac derive_dtm3 :=
  intros;
  derive_dtm3_setup;
  if_goal_match_binddt_ret
    derive_dtm3_ret_case
    derive_dtm3_IH_step.

(** ** Proving the fourt law *)
(******************************************************************************)
Ltac derive_dtm4_ret_case :=
  debug "derive_dtm4|ret case start";
  reflexivity; (* should solve <<ret>> case *)
  debug "derive_dtm4|ret case end".

Ltac derive_dtm4_simplify_hom :=
  repeat rewrite ap_morphism_1;
  rewrite appmor_pure.

Ltac derive_dtm4_IH_step :=
  debug "derive_dtm4|IH step start";
  repeat simplify_binddt_core;
  derive_dtm4_simplify_hom;
  repeat rewrite_with_any; (* try to use IH wherever possible *)
  try easy; (* hopefully this solves it, otherwise let the user take over *)
  repeat fequal;
  debug "derive_dtm4|IH step end".

Ltac derive_dtm4_setup :=
  match goal with
    |- context[(?ϕ ?B ∘ binddt ?f) = binddt (?ϕ ?B ∘ ?f)] =>
      debug "setup_dtm_proof_guess_law4";
      infer_applicative_functors;
      let t := fresh "t" in
      ext t;
      generalize dependent f;
      change ((?g ∘ ?f) t) with (g (f t));
      induction_term t; intro f
  | |- _ => fail "derive_dtm4_setup: no match"
  end.

Ltac derive_dtm4 :=
  intros;
  derive_dtm4_setup;
  if_goal_match_binddt_ret
    derive_dtm4_ret_case
    derive_dtm4_IH_step.

(** ** Putting it together *)
(******************************************************************************)
Ltac setup_dtm_proof :=
  match goal with
  | |- context[(binddt (T := ?T) (U := ?U) ?f ∘ ret)] =>
      derive_dtm1
  | |- context[binddt (T := ?T) (U := ?U) (ret ∘ extract) = id] =>
      derive_dtm2
  | |- context[map (binddt (T := ?T) (U := ?U) ?g) ∘
                binddt (T := ?T) (U := ?U) ?f] =>
      derive_dtm3
  | |- context[(?ϕ ?B ∘ binddt ?f) = binddt (?ϕ ?B ∘ ?f)] =>
      derive_dtm4
  end.

Ltac derive_dtm_law :=
  intros; setup_dtm_proof.

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
