From Tealeaves Require Export
  Backends.LN.LN
  Simplification.Support
  Simplification.Binddt.

Import Monoid.Notations List.ListNotations.

#[local] Notation "'P'" := pure.
#[local]  Notation "'BD'" := binddt.

Create HintDb tea_ret_coercions.

(** * Simplifying LCn *)
(******************************************************************************)

(** ** Simplifying LCn at the leaves *)
(******************************************************************************)
Ltac simplify_arithmetic :=
  match goal with
  | |- context[(?x + 0)%nat] =>
      replace (x + 0)%nat with x by lia
  | |- context[(0 + ?x)%nat] =>
      replace (0 + x)%nat with x by lia
  end.

Ltac simplify_lc_loc_under_binder :=
  match goal with
  | |- context[lc_loc ?n ⦿ 1] =>
      rewrite lc_loc_S
  | |- context[lc_loc ?n ⦿ ?m] =>
      rewrite lc_loc_preincr
  end.

Ltac simplify_lc_loc_leaf :=
  match goal with
  | |- context[lc_loc ?n (?w, Fr ?x)] =>
      rewrite lc_loc_Fr
  | |- context[lc_loc 0 (0, Bd ?b)] =>
      rewrite lc_loc_00Bd
  | |- context[lc_loc 0 (?w, Bd ?b)] =>
      rewrite lc_loc_0Bd
  | |- context[lc_loc ?n (?w, Bd ?b)] =>
      rewrite lc_loc_nBd
  end.

(** ** Simplifying LCn *)
(******************************************************************************)
Ltac simplify_LC_local :=
  ltac_trace "simplify_LC_local";
  repeat simplify_lc_loc_under_binder;
  ( unfold_ops @Monoid_op_plus @Monoid_unit_zero;
    try simplify_lc_loc_leaf;
    repeat simplify_arithmetic).

Ltac simplify_LC :=
  ltac_trace "simplify_ln_LC_start";
  repeat change (LC ?t) with (LCn 0 t);
  rewrite LCn_spec;
  simplify_Forall_ctx;
  (* IF bottomed out *)
  simplify_LC_local;
  (* ELSE IF refolding *)
  repeat rewrite <- LCn_spec;
  repeat change (LCn 0 ?t) with (LC t);
  ltac_trace "simplify_ln_LC_end".

Ltac simplify_LC_in H :=
  repeat change (LC ?t) with (LCn 0 t) in H;
  rewrite LCn_spec in H;
  simplify_Forall_ctx_in H;
  repeat rewrite <- LCn_spec in H;
  repeat change (LCn 0 ?t) with (LC t) in H.

(** * Simplifying free and FV *)
(******************************************************************************)
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

Ltac simplify_free_loc :=
  repeat match goal with
  | |- context[free_loc ?v] =>
      let e := constr:(free_loc v)in
      let e' := eval cbn in e in
        change e with e' in *
  end.

Ltac simplify_free_post :=
  (* simplifying foldmap exposes ● with lists *)
  repeat simplify_monoid_append.

Ltac simplify_free :=
  ltac_trace "simplify_free";
  unfold free;
  simplify_foldMap;
  (* ^^ this exposes ● with lists *)
  repeat simplify_monoid_append;
  (* IF bottomed out *)
  ltac_trace "simplify_free_loc";
  simplify_free_loc;
  ltac_trace "simplify_free";
  (* ELSE IF refolding *)
  repeat change (foldMap free_loc ?t) with (free t).

Ltac refold_FV :=
  repeat match goal with
    | |- context[atoms ○ free (U := ?T)] =>
        change (atoms ○ free (U := T))
        with (FV (U := T))
    | |- context[atoms (free (U := ?T) ?t)] =>
        change (atoms (free (U := T) t))
        with (FV (U := T) t)
    end.

Ltac simplify_FV :=
  ltac_trace "simplify_ln_FV_start";
  unfold FV;
  simplify_free;
  autorewrite with tea_rw_atoms;
  refold_FV;
  ltac_trace "simplify_ln_FV_end".

(** * Simplifying open *)
(******************************************************************************)
Ltac refold_open :=
  repeat match goal with
  | |- context[bindd (open_loc ?u) ?t] =>
      try change (bindd (open_loc u) t) with (open u t)
    end.

Ltac simplify_open :=
  ltac_trace "simplify_ln_open_start";
  unfold open;
  simplify_bindd;
  refold_open;
  ltac_trace "simplify_ln_open_end".


(** * Simplifying subst *)
(******************************************************************************)
Ltac refold_subst :=
  repeat match goal with
  | |- context[bind (subst_loc ?x ?u) ?t] =>
      try change (bind (subst_loc x u) t) with (subst x u t)
    end.

Lemma subst_to_bind {T U}
  `{Return T} `{Bind T U}: forall x (u: T LN) (t: U LN),
    subst x u t = bind (subst_loc x u) t.
Proof.
  reflexivity.
Qed.

(* mret is some expression being tested for matching
   (ret x) for some x *)
Ltac try_change_to_ret T exp :=
  match exp with
  | context[?mret ?t] =>
      change (mret t) with (ret (T := T) t)
  end.

Ltac simplify_subst :=
  ltac_trace "simplify_ln_subst| start";
  match goal with
  | |- context[subst (U := ?T) ?x ?u ?t] =>
      ltac_trace "simplify_ln_subst| test for ret";
      try_change_to_ret T t;
      rewrite subst_ret;
      ltac_trace "simplify_ln_subst| changed to ret";
      simplify_subst_local
  | |- context[subst (U := ?T) ?x ?u ?t] =>
      ltac_trace "simplify_ln_subst| not ret";
      rewrite (subst_to_bind x u t);
      simplify_bind;
      refold_subst
  | |- _ => fail
  end;
  ltac_trace "simplify_ln_subst_end".


(** * Simplifying everything *)
(******************************************************************************)
Ltac simplify_LN :=
  autounfold with tea_ret_coercions;
  ltac_trace "simplify_LN";
  match goal with
  | |- context[LCn ?t] =>
      simplify_LC
  | |- context[LC ?t] =>
      simplify_LC
  | |- context[free ?t] =>
      simplify_free
  | |- context[FV ?t] =>
      simplify_FV
  | |- context[open ?t] =>
      simplify_open
  | |- context[subst ?x ?u ?t] =>
      simplify_subst
  end.

Ltac simplify :=
  repeat simplify_LN;
  repeat simplify_derived_operations;
  simpl_list.
