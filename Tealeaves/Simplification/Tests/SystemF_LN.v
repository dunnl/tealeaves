From Tealeaves Require Export
  Examples.SystemF.Syntax
  Simplification.Tests.Support
  Simplification.MBinddt
  Simplification.Tests.SystemF_Binddt
  Simplification.Tests.SystemF_Targeted
  Classes.Multisorted.Theory.Foldmap.

#[local] Generalizable Variables G.
#[local] Arguments mbinddt {ix} {W}%type_scope {T} U%function_scope
  {MBind} {F}%function_scope {H H0 H1 A B} _ _.

#[local] Generalizable Variables A B C F W T U K.

Section local_lemmas_needed.

  Context
    (U : Type -> Type)
      `{MultiDecoratedTraversablePreModule (list K) T U
          (mn_op := Monoid_op_list)
          (mn_unit := Monoid_unit_list)}
      `{! MultiDecoratedTraversableMonad (list K) T
          (mn_op := Monoid_op_list)
          (mn_unit := Monoid_unit_list)}.

  Lemma subst_to_kbind : forall (k: K) (x: atom) (u: T k LN),
      subst U k x u = kbind U k (subst_loc k x u).
  Proof.
    reflexivity.
  Qed.

  Lemma open_to_kbindd : forall (k: K) (u: T k LN),
      open U k u = kbindd U k (open_loc k u).
  Proof.
    reflexivity.
  Qed.

  Lemma free_to_foldMapk : forall (k: K),
      free U (T := T) k = foldMapk U k free_loc.
  Proof.
    intros.
    unfold free. ext t.
    unfold toklist, compose.
    unfold foldMapk.
    rewrite foldMapm_to_foldMapmd.
    rewrite (foldMapmd_through_tolist U).
    unfold toklistd.
    unfold compose.
    induction (tolistmd U t).
    - reflexivity.
    - destruct a as [w [j l']].
      cbn.
      unfold tgt_def.
      unfold_ops @Monoid_op_list.
      unfold vec_compose, compose.
      cbn. destruct_eq_args k j.
      cbn. rewrite IHl. fequal.
  Qed.

  Lemma FV_to_free : forall (k: K) (t: U LN),
      FV U k t = atoms (free U (T := T) k t).
  Proof.
    reflexivity.
  Qed.

  Lemma LCn_to_Forallkd:
    forall (n: nat) (t: U LN) k,
      LCn U k n t = Forallkd U k (lc_loc k n) t.
  Proof.
    intros.
    apply propositional_extensionality.
    rewrite <- (Forallkd_spec U (lc_loc k n)).
    reflexivity.
  Qed.

  Lemma LC_to_Forallkd:
    forall (n: nat) (t: U LN) k,
      LC U k t = Forallkd U k (lc_loc k 0) t.
  Proof.
    intros.
    apply propositional_extensionality.
    rewrite <- (Forallkd_spec U (lc_loc k 0)).
    reflexivity.
  Qed.

  Lemma lc_loc_preincr_eq :
    forall k n j,
      k = j ->
      (lc_loc k n ⦿ [j]) =
        lc_loc k (S n).
  Proof.
    intros.
    unfold preincr, compose, incr.
    ext [w l].
    unfold lc_loc.
    destruct l as [x | m].
    - reflexivity.
    - cbn. destruct_eq_args k j.
      propext; lia.
  Qed.

  Lemma lc_loc_preincr_neq :
    forall k n j,
      k <> j ->
      (lc_loc k n ⦿ [j]) =
        lc_loc k n.
  Proof.
    intros.
    unfold preincr, compose, incr.
    ext [w l].
    unfold lc_loc.
    destruct l as [x | m].
    - reflexivity.
    - cbn. destruct_eq_args k j.
  Qed.

End local_lemmas_needed.

Create HintDb lc_loc_db.
#[global] Hint Rewrite lc_loc_preincr_eq: lc_loc_db.
#[global] Hint Rewrite lc_loc_preincr_neq: lc_loc_db.

(*
Ltac handle_lc_loc :=
  autorewrite* with lc_loc_db using (auto; try discriminate).
 *)

Ltac handle_lc_loc :=
  match goal with
  | |- context[lc_loc (ix := ?ix)] =>
      first [ rewrite (lc_loc_preincr_eq (ix := ix)) by auto
            | rewrite (lc_loc_preincr_neq (ix := ix)) by
              (solve [auto || discriminate])
        ]
  end.

Ltac simplify_open_pre_refold_hook :=
  idtac.

Ltac simplify_open_post_refold_hook :=
  idtac.

Ltac simplify_open :=
  rewrite ?open_to_kbindd;
  simplify_kbindd;
  simplify_open_pre_refold_hook;
  rewrite <- ?open_to_kbindd;
  simplify_open_post_refold_hook.

(** ** <<open>> *)
(******************************************************************************)
Section rw_open.

  Context
    (A : Type)
      (k : K2)
      (x: atom)
      (u: SystemF k LN).

  Ltac tactic_being_tested ::= simplify_open.

  Lemma open_type_rw1 : forall c,
      open typ k u (ty_c c) = ty_c c.
  Proof.
    test_simplification.
  Qed.

  (*
  Lemma open_type_rw2_neq : forall (a : A),
      k <> ktyp ->
      open typ k f (ty_v a) = ty_v a.
  Proof.
    intros.
    simplify_open.
    rewrite btgd_neq; auto.
  Qed.*)

  Lemma open_type_rw3 : forall (t1 t2 : typ LN),
      open typ k u (ty_ar t1 t2) =
        ty_ar (open typ k u t1) (open typ k u t2).
  Proof.
    test_simplification.
  Qed.

  Lemma open_type_rw4 : forall (body : typ LN),
      open typ k u (ty_univ body) =
        ty_univ (kbindd typ k (preincr (W := list K) (open_loc k u) [ktyp]) body).
  Proof.
    intros.
    test_simplification.
  Qed.

  Lemma open_term_rw1_neq : forall (a : LN),
      k <> ktrm ->
      open term k u (tm_var a) = tm_var a.
  Proof.
    intros.
    unfold open.
    simplify_kbindd.
    normalize_K.
  Abort.

  Lemma open_term_rw2 : forall (τ : typ LN) (t : term LN),
      open term k u (tm_abs τ t) =
        tm_abs (open typ k u τ)
          (kbindd term k (preincr (W := list K) (open_loc k u) [ktrm]) t).
  Proof.
    test_simplification.
  Qed.

  Lemma open_term_rw3 : forall (t1 t2 : term LN),
      open term k u (tm_app t1 t2) =
        tm_app (open term k u t1) (open term k u t2).
  Proof.
    test_simplification.
  Qed.

  Lemma open_term_rw4 : forall (t : term LN),
      open term k u (tm_tab t) =
        tm_tab (kbindd term k (preincr (W := list K) (open_loc k u) [ktyp]) t).
  Proof.
    test_simplification.
  Qed.

  Lemma open_term_rw5 : forall (t: term LN) (τ : typ LN),
      open term k u (tm_tap t τ) =
        tm_tap (open term k u t) (open typ k u τ).
  Proof.
    test_simplification.
  Qed.

End rw_open.

Ltac simplify_LCn_pre_refold_hook :=
  repeat handle_lc_loc.

Ltac simplify_LCn_post_refold_hook :=
  idtac.

Ltac simplify_LCn :=
  match goal with
  | |- context[LCn (T := ?T) (ix := ?ix)
                ?U ?k ?n ?t] =>
      rewrite ?(LCn_to_Forallkd _(*U*) (ix := ix));
      simplify_Forallkd;
      simplify_LCn_pre_refold_hook;
      rewrite <- ?(LCn_to_Forallkd _ (ix := ix));
      simplify_LCn_post_refold_hook
  end.

(** ** <<LCn>> *)
(******************************************************************************)
Section rw_LCn.

  Context
    (A : Type)
      (k : K2)
      (n: nat)
      (x: atom)
      (u: SystemF k LN).

  Ltac tactic_being_tested ::= simplify_LCn.

  Lemma LCn_type_rw1 : forall c,
      LCn typ k n (ty_c c) = True.
  Proof.
    test_simplification.
  Qed.

  (*
  Lemma LCn_type_rw2_neq : forall (a : A),
      k <> ktyp ->
      LC typ k f (ty_v a) = ty_v a.
  Proof.
    intros.
    simplify_LC.
    rewrite btgd_neq; auto.
  Qed.*)

  Lemma LCn_type_rw3 : forall (t1 t2 : typ LN),
      LCn typ k n (ty_ar t1 t2) =
        (LCn typ k n t1 /\ LCn typ k n t2).
  Proof.
    test_simplification.
  Qed.

  Lemma LCn_type_rw4_eq : forall (body : typ LN),
      k = ktyp ->
      LCn typ k n (ty_univ body) =
        LCn typ k (S n) body.
  Proof.
    test_simplification.
  Qed.

  Lemma LCn_type_rw4_neq : forall (body : typ LN),
      k <> ktyp ->
      LCn typ k n (ty_univ body) =
        LCn typ k n body.
  Proof.
    test_simplification.
  Qed.

  (*
  Lemma LCn_term_rw1_neq : forall (a : LN),
      k <> ktrm ->
      LC term (tm_var a) = tm_var a.
  Proof.
    intros.
    unfold LC.
    simplify_kbindd.
    normalize_K.
  Abort.
  *)

  Lemma LCn_term_rw2_eq : forall (τ : typ LN) (t : term LN),
      k = ktrm ->
      LCn term k n (tm_abs τ t) =
        (LCn typ k n τ /\ LCn term k (S n) t).
  Proof.
    test_simplification.
  Qed.

  Lemma LCn_term_rw2_neq : forall (τ : typ LN) (t : term LN),
      k <> ktrm ->
      LCn term k n (tm_abs τ t) =
        (LCn typ k n τ /\ LCn term k n t).
  Proof.
    test_simplification.
  Qed.

  Lemma LCn_term_rw3 : forall (t1 t2 : term LN),
      LCn term k n (tm_app t1 t2) =
        (LCn term k n t1 /\ LCn term k n t2).
  Proof.
    test_simplification.
  Qed.

  Lemma LCn_term_rw4_neq : forall (t : term LN),
      k <> ktyp ->
      LCn term k n (tm_tab t) =
        LCn term k n t.
  Proof.
    test_simplification.
  Qed.

  Lemma LCn_term_rw4_eq : forall (t : term LN),
      k = ktyp ->
      LCn term k n (tm_tab t) =
        LCn term k (S n) t.
  Proof.
    test_simplification.
  Qed.

  Lemma LCn_term_rw5 : forall (t: term LN) (τ : typ LN),
      LCn term k n (tm_tap t τ) =
        (LCn term k n t /\ LCn typ k n τ).
  Proof.
    test_simplification.
  Qed.

End rw_LCn.

Ltac simplify_LC_pre_refold_hook :=
  idtac.

Ltac simplify_LC_post_refold_hook :=
  idtac.

Ltac simplify_LC :=
  match goal with
  | |- context[LC (T := ?T) (ix := ?ix)
                ?U ?k ?t] =>
      unfold LC;
      simplify_LCn;
      repeat (change (LCn ?U ?k 0) with (LC U k))
  end.

(** ** <<LC>> *)
(******************************************************************************)
Section rw_LC.

  Context
    (A : Type)
      (k : K2)
      (n: nat)
      (x: atom)
      (u: SystemF k LN).

  Ltac tactic_being_tested ::= simplify_LC.

  Lemma LC_type_rw1 : forall c,
      LC typ k (ty_c c) = True.
  Proof.
    test_simplification.
  Qed.

  Lemma LC_type_rw3 : forall (t1 t2 : typ LN),
      LC typ k (ty_ar t1 t2) =
        (LC typ k t1 /\ LC typ k t2).
  Proof.
    test_simplification.
  Qed.

  Lemma LC_type_rw4_eq : forall (body : typ LN),
      k = ktyp ->
      LC typ k (ty_univ body) =
        LCn typ k 1 body.
  Proof.
    test_simplification.
  Qed.

  Lemma LC_type_rw4_neq : forall (body : typ LN),
      k <> ktyp ->
      LC typ k (ty_univ body) =
        LC typ k body.
  Proof.
    test_simplification.
  Qed.

  Lemma LC_term_rw2_eq : forall (τ : typ LN) (t : term LN),
      k = ktrm ->
      LC term k (tm_abs τ t) =
        (LC typ k τ /\ LCn term k 1 t).
  Proof.
    test_simplification.
  Qed.

  Lemma LC_term_rw2_neq : forall (τ : typ LN) (t : term LN),
      k <> ktrm ->
      LC term k (tm_abs τ t) =
        (LC typ k τ /\ LC term k t).
  Proof.
    test_simplification.
  Qed.

  Lemma LC_term_rw3 : forall (t1 t2 : term LN),
      LC term k (tm_app t1 t2) =
        (LC term k t1 /\ LC term k t2).
  Proof.
    test_simplification.
  Qed.

  Lemma LC_term_rw4_neq : forall (t : term LN),
      k <> ktyp ->
      LC term k (tm_tab t) =
        LC term k t.
  Proof.
    test_simplification.
  Qed.

  Lemma LC_term_rw4_eq : forall (t : term LN),
      k = ktyp ->
      LC term k (tm_tab t) =
        LCn term k 1 t.
  Proof.
    test_simplification.
  Qed.

  Lemma LC_term_rw5 : forall (t: term LN) (τ : typ LN),
      LC term k (tm_tap t τ) =
        (LC term k t /\ LC typ k τ).
  Proof.
    test_simplification.
  Qed.

End rw_LC.

Ltac simplify_subst_pre_refold_hook :=
  idtac.

Ltac simplify_subst_post_refold_hook :=
  idtac.

Ltac simplify_subst :=
  match goal with
  | |- context[subst (T := ?T) (ix := ?ix)
                ?U ?k ?t] =>
      rewrite ?(subst_to_kbind);
      simplify_kbind;
      rewrite <- ?(subst_to_kbind)
  end.

(** ** <<subst>> *)
(******************************************************************************)
Section rw_subst.

  Context
    (A : Type)
      (k : K2)
      (n: nat)
      (x: atom)
      (u: SystemF k LN).

  Ltac tactic_being_tested ::= simplify_subst.

  Lemma subst_type_rw1 : forall c,
      subst typ k x u (ty_c c) = ty_c c.
  Proof.
    test_simplification.
  Qed.

  Lemma subst_type_rw3 : forall (t1 t2 : typ LN),
      subst typ k x u (ty_ar t1 t2) =
        ty_ar (subst typ k x u t1) (subst typ k x u t2).
  Proof.
    test_simplification.
  Qed.

  Lemma subst_type_rw4 : forall (body : typ LN),
      subst typ k x u (ty_univ body) =
        ty_univ (subst typ k x u body).
  Proof.
    test_simplification.
  Qed.

  Lemma subst_term_rw2_eq : forall (τ : typ LN) (t : term LN),
      subst term k x u (tm_abs τ t) =
        tm_abs (subst typ k x u τ) (subst term k x u t).
  Proof.
    test_simplification.
  Qed.

  Lemma subst_term_rw2 : forall (τ : typ LN) (t : term LN),
      subst term k x u (tm_abs τ t) =
        tm_abs (subst typ k x u τ) (subst term k x u t).
  Proof.
    test_simplification.
  Qed.

  Lemma subst_term_rw3 : forall (t1 t2 : term LN),
      subst term k x u (tm_app t1 t2) =
        tm_app (subst term k x u t1) (subst term k x u t2).
  Proof.
    test_simplification.
  Qed.

  Lemma subst_term_rw4 : forall (t : term LN),
      subst term k x u (tm_tab t) =
        tm_tab (subst term k x u t).
  Proof.
    test_simplification.
  Qed.

  Lemma subst_term_rw5 : forall (t: term LN) (τ : typ LN),
      subst term k x u (tm_tap t τ) =
        tm_tap (subst term k x u t) (subst typ k x u τ).
  Proof.
    test_simplification.
  Qed.

End rw_subst.

Ltac simplify_free_pre_refold_hook :=
  idtac.

Ltac simplify_free_post_refold_hook :=
  unfold_ops @Monoid_op_list;
  unfold_ops @Monoid_unit_list.

Ltac handle_free_at_leaf :=
  (match goal with
   | |- context[EqDec_eq_of_EqDec ?Keq ?k1 ?k2] =>
       destruct (EqDec_eq_of_EqDec Keq k1 k2);
       try easy
   end).

Ltac simplify_free :=
  match goal with
  | |- context[free (T := ?T) (ix := ?ix)
                ?U ?k ?t] =>
      rewrite ?(free_to_foldMapk _ (ix := ix));
      simplify_foldMapk;
      simplify_free_pre_refold_hook;
      rewrite <- ?(free_to_foldMapk _ (ix := ix));
      simplify_free_post_refold_hook;
      try solve [handle_free_at_leaf]
  end.

(** ** <<free>> *)
(******************************************************************************)
Section rw_free.

  Context
    (A : Type)
      (k : K2)
      (n: nat)
      (x: atom)
      (u: SystemF k LN).

  Ltac tactic_being_tested ::= simplify_free.

  Lemma free_type_rw1 : forall c,
      free typ k (ty_c c) = nil.
  Proof.
    test_simplification.
  Qed.

  Lemma free_type_rw2_atom_eq : forall (x: atom),
      k = ktyp ->
      free typ k (ty_v (Fr x)) = [ x ].
  Proof.
    test_simplification.
  Qed.

  Lemma free_type_rw2_atom : forall (x: atom),
      k <> ktyp ->
      free typ k (ty_v (Fr x)) = [ ].
  Proof.
    test_simplification.
  Qed.

  Lemma free_type_rw2_bound : forall n,
      free typ k (ty_v (Bd n)) = [ ].
  Proof.
    test_simplification.
  Qed.

  Lemma free_type_rw3 : forall (t1 t2 : typ LN),
      free typ k (ty_ar t1 t2) =
        free typ k t1 ++ free typ k t2.
  Proof.
    test_simplification.
  Qed.

  Lemma free_type_rw4 : forall (body : typ LN),
      free typ k (ty_univ body) =
        free typ k body.
  Proof.
    test_simplification.
  Qed.

  Lemma free_term_rw2_eq : forall (τ : typ LN) (t : term LN),
      free term k (tm_abs τ t) =
        free typ k τ ++ free term k t.
  Proof.
    test_simplification.
  Qed.

  Lemma free_term_rw2 : forall (τ : typ LN) (t : term LN),
      free term k (tm_abs τ t) =
        free typ k τ ++ free term k t.
  Proof.
    test_simplification.
  Qed.

  Lemma free_term_rw3 : forall (t1 t2 : term LN),
      free term k (tm_app t1 t2) =
        free term k t1 ++ free term k t2.
  Proof.
    test_simplification.
  Qed.

  Lemma free_term_rw4 : forall (t : term LN),
      free term k (tm_tab t) =
        free term k t.
  Proof.
    test_simplification.
  Qed.

  Lemma free_term_rw5 : forall (t: term LN) (τ : typ LN),
      free term k (tm_tap t τ) =
        free term k t ++ free typ k τ.
  Proof.
    test_simplification.
  Qed.

End rw_free.

Ltac assert_identical_with_atoms :=
    match goal with
    | |- ?x [=] ?x =>
        ltac_trace "Both sides identical:";
        print_goal
    end.

Ltac test_simplification_with_atoms :=
  intros;
  tactic_being_tested;
  try normalize_K;
  now assert_identical_with_atoms.

Ltac simplify_FV_pre_refold_hook :=
  autorewrite with tea_rw_atoms.

Ltac simplify_FV_post_refold_hook :=
  idtac.

Ltac simplify_FV :=
  match goal with
  | |- context[FV (T := ?T) (ix := ?ix)
                ?U ?k ?t] =>
      rewrite ?(FV_to_free _ (ix := ix));
      simplify_free;
      simplify_FV_pre_refold_hook;
      rewrite <- ?(FV_to_free _ (ix := ix));
      simplify_FV_post_refold_hook
  end.

(** ** <<FV>> *)
(******************************************************************************)
Section rw_FV.

  Context
    (A : Type)
      (k : K2)
      (n: nat)
      (x: atom)
      (u: SystemF k LN).

  Ltac tactic_being_tested ::= simplify_FV.

  #[local] Open Scope set_scope.

  Lemma FV_type_rw1 : forall c,
      FV typ k (ty_c c) [=] ∅.
  Proof.
    test_simplification_with_atoms.
  Qed.

  Lemma FV_type_rw2_atom : forall (x: atom),
      k = ktyp ->
      FV typ k (ty_v (Fr x)) [=] {{ x }}.
  Proof.
    test_simplification_with_atoms.
  Qed.

  Lemma FV_type_rw3 : forall (t1 t2 : typ LN),
      FV typ k (ty_ar t1 t2) [=]
        FV typ k t1 ∪ FV typ k t2.
  Proof.
    test_simplification_with_atoms.
  Qed.

  Lemma FV_type_rw4 : forall (body : typ LN),
      FV typ k (ty_univ body) [=]
        FV typ k body.
  Proof.
    test_simplification_with_atoms.
  Qed.

  Lemma FV_term_rw2_eq : forall (τ : typ LN) (t : term LN),
      FV term k (tm_abs τ t) [=]
        FV typ k τ ∪ FV term k t.
  Proof.
    test_simplification_with_atoms.
  Qed.

  Lemma FV_term_rw2 : forall (τ : typ LN) (t : term LN),
      FV term k (tm_abs τ t) [=]
        FV typ k τ ∪ FV term k t.
  Proof.
    test_simplification_with_atoms.
  Qed.

  Lemma FV_term_rw3 : forall (t1 t2 : term LN),
      FV term k (tm_app t1 t2) [=]
        FV term k t1 ∪ FV term k t2.
  Proof.
    test_simplification_with_atoms.
  Qed.

  Lemma FV_term_rw4 : forall (t : term LN),
      FV term k (tm_tab t) [=]
        FV term k t.
  Proof.
    test_simplification_with_atoms.
  Qed.

  Lemma FV_term_rw5 : forall (t: term LN) (τ : typ LN),
      FV term k (tm_tap t τ) [=]
        FV term k t ∪ FV typ k τ.
  Proof.
    test_simplification_with_atoms.
  Qed.

End rw_FV.

Ltac simplify_scoped_pre_refold_hook :=
  idtac.

Ltac simplify_scoped_post_refold_hook :=
  idtac.

Ltac simplify_scoped :=
  match goal with
  | |- context[scoped (T := ?T) (ix := ?ix)
                ?U ?k ?n ?t] =>
      idtac
  end.
(*
      rewrite ?(scoped_to_Forallkd _(*U*) (ix := ix));
      simplify_Forallkd;
      simplify_scoped_pre_refold_hook;
      rewrite <- ?(scoped_to_Forallkd _ (ix := ix));
      simplify_scoped_post_refold_hook
*)

(** ** <<scoped>> *)
(******************************************************************************)
Section rw_scoped.

  Context
    (A : Type)
      (k : K2)
      (Γ : AtomSet.t)
      (u: SystemF k LN).

  Ltac tactic_being_tested ::= simplify_scoped.

  Lemma scoped_type_rw1 : forall c,
      scoped typ k (ty_c c) Γ <-> True.
  Proof.
    intros.
    unfold scoped.
    simplify_FV.
    split; fsetdec.
  Qed.

  (*
  Lemma scoped_type_rw2_neq : forall (a : A),
      k <> ktyp ->
      LC typ k f (ty_v a) = ty_v a.
  Proof.
    intros.
    simplify_LC.
    rewrite btgd_neq; auto.
  Qed.*)

  Lemma scoped_type_rw3 : forall (t1 t2 : typ LN),
      scoped typ k (ty_ar t1 t2) Γ <->
        (scoped typ k t1 Γ /\ scoped typ k t2 Γ).
  Proof.
    intros.
    unfold scoped.
    simplify_FV.
    intuition fsetdec.
  Qed.

  Lemma scoped_type_rw4_eq : forall (body : typ LN),
      scoped typ k (ty_univ body) Γ <->
        scoped typ k body Γ.
  Proof.
    intros.
    unfold scoped.
    simplify_FV.
    intuition fsetdec.
  Qed.

  Lemma scoped_type_rw4_neq : forall (body : typ LN),
      scoped typ k (ty_univ body) =
        scoped typ k body.
  Proof.
    intros.
    unfold scoped.
    simplify_FV.
    conclude.
  Qed.

  #[local] Open Scope set_scope.

  Lemma scoped_term_rw1_eq : forall (x : atom),
      k = ktrm ->
      scoped term k (tm_var (Fr x)) Γ = ({{x}} ⊆ Γ).
  Proof.
    intros.
    unfold scoped.
    simplify_FV.
  Qed.

  Lemma scoped_term_rw1_neq : forall (x : atom),
      k <> ktrm ->
      scoped term k (tm_var (Fr x)) Γ = True.
  Proof.
    intros.
    unfold scoped.
    propext; simplify_FV.
  Qed.

  Lemma scoped_term_rw2: forall (τ : typ LN) (t : term LN),
      scoped term k (tm_abs τ t) Γ <->
        (scoped typ k τ Γ /\ scoped term k t Γ).
  Proof.
    intros.
    unfold scoped.
    simplify_FV.
    intuition fsetdec.
  Qed.

  Lemma scoped_term_rw3 : forall (t1 t2 : term LN),
      scoped term k (tm_app t1 t2) Γ <->
        (scoped term k t1 Γ /\ scoped term k t2 Γ).
  Proof.
    intros.
    unfold scoped.
    simplify_FV.
    intuition fsetdec.
  Qed.

  Lemma scoped_term_rw4_neq : forall (t : term LN),
      scoped term k (tm_tab t) Γ <->
        scoped term k t Γ.
  Proof.
    intros.
    unfold scoped.
    simplify_FV.
    intuition fsetdec.
  Qed.

  Lemma scoped_term_rw4_eq : forall (t : term LN),
      scoped term k (tm_tab t) Γ <->
        scoped term k t Γ.
  Proof.
    intros.
    unfold scoped.
    simplify_FV.
    intuition fsetdec.
  Qed.

  Lemma scoped_term_rw5 : forall (t: term LN) (τ : typ LN),
      scoped term k (tm_tap t τ) Γ <->
        (scoped term k t Γ /\ scoped typ k τ Γ).
  Proof.
    intros.
    unfold scoped.
    simplify_FV.
    intuition fsetdec.
  Qed.

End rw_scoped.
