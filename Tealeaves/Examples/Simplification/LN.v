From Tealeaves Require Export
  Backends.LN
  Examples.Simplification.Support
  Examples.Simplification.Binddt.

Import LN.Notations.

#[local] Notation "'P'" := pure.
#[local]  Notation "'BD'" := binddt.

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

Ltac simplify_arithmetic :=
  match goal with
  | |- context[(?x + 0)%nat] =>
      replace (x + 0)%nat with x by lia
  | |- context[(0 + ?x)%nat] =>
      replace (0 + x)%nat with x by lia
  end.

Ltac simplify_LC :=
  repeat change (LC ?t) with (LCn 0 t);
  rewrite LCn_spec;
  simplify_Forall_ctx;
  repeat simplify_lc_loc_under_binder;
  ( unfold_ops @Monoid_op_plus @Monoid_unit_zero;
    try simplify_lc_loc_leaf;
    repeat simplify_arithmetic);
  (* ^ This should really only apply at (ret) *)
  repeat rewrite <- LCn_spec;
  repeat change (LCn 0 ?t) with (LC t).


Ltac simplify_LC_in H :=
  repeat change (LC ?t) with (LCn 0 t) in H;
  rewrite LCn_spec in H;
  simplify_Forall_ctx_in H;
  repeat rewrite <- LCn_spec in H;
  repeat change (LCn 0 ?t) with (LC t) in H.


Ltac simplify_free_loc :=
  match goal with
  | |- context[free_loc ?v] =>
      let e := constr:(free_loc v)in
      let e' := eval cbn in e in
        change e with e' in *
  end.

Ltac simplify_free :=
  unfold free;
  simplify_foldMap;
  (* ^^ this exposes ● with lists *)
  repeat simplify_monoid_append;
  repeat change (foldMap free_loc ?t) with (free t);
  repeat simplify_free_loc.

Ltac simplify_FV :=
  unfold FV;
  simplify_free;
  autorewrite with tea_rw_atoms;
  repeat match goal with
    | |- context[atoms ○ free (T := ?T)] =>
        change (atoms ○ free (T := T))
        with (FV (T := T))
    | |- context[atoms (free (T := ?T) ?t)] =>
        change (atoms (free (T := T) t))
        with (FV (T := T) t)
    end.

Ltac simplify_open :=
  unfold open;
  simplify_bindd;
  repeat match goal with
  | |- context[bindd (open_loc ?u) ?t] =>
      try change (bindd (open_loc u) t) with (open u t)
    end.

Ltac simplify_subst :=
  unfold subst;
  simplify_bind;
  repeat match goal with
  | |- context[bind (subst_loc ?x ?u) ?t] =>
      try change (bind (subst_loc x u) t) with (subst x u t)
  end.

Ltac simplify_LN :=
  match goal with
  | |- context[LCn ?t] =>
      debug "";
      simplify_LC
  | |- context[LC ?t] =>
      debug "";
      simplify_LC
  | |- context[free ?t] =>
      debug "";
      simplify_free
  | |- context[FV ?t] =>
      debug "";
      simplify_FV
  | |- context[open ?t] =>
      debug "";
      simplify_open
  | |- context[subst ?x ?u ?t] =>
      debug "";
      simplify_subst
  end.

Ltac simplify :=
  repeat simplify_LN;
  repeat simplify_derived_operations;
  simpl_list.
