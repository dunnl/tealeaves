From Tealeaves Require Export
  Examples.SystemF.Syntax
  Examples.SystemF.Contexts.

From Coq Require Import
  Sorting.Permutation.

Implicit Types (x : atom).
Open Scope set_scope.

Lemma rw_subst_type_var_neq {x y} τ':
  x <> y ->
  subst typ ktyp x τ' (ty_v (Fr y)) = ty_v (Fr y).
Proof.
Admitted.

Lemma rw_subst_term_var_neq {x y} {τ} :
  x <> y ->
  subst term ktyp x τ (tm_var (Fr y)) = tm_var (Fr y).
Proof.
Admitted.

(** * Properties of the typing judgment <<Δ ; Γ ⊢ t : τ>> *)
(******************************************************************************)

(** ** Structural properties <<Δ ; Γ ⊢ t : τ>> in <<Δ>> *)
(******************************************************************************)

(** *** <<Δ>> is always well-formed *)
(******************************************************************************)
Lemma j_kind_ctx_wf : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    ok_kind_ctx Δ.
Proof.
  unfold ok_kind_ctx; induction 1; cleanup_cofinite.
  all: (autorewrite with tea_rw_uniq in *; intuition).
Qed.

(** *** Permutation *)
(******************************************************************************)
Theorem j_kind_ctx_perm : forall Δ1 Δ2 Γ t τ,
    Permutation Δ1 Δ2 ->
    (Δ1 ; Γ ⊢ t : τ) ->
    (Δ2 ; Γ ⊢ t : τ).
Proof.
  introv perm j. generalize dependent Δ2.
  induction j; introv Hperm.
  - eauto using Judgment, Permutation_sym with sysf_ctx.
  - eauto using Judgment.
  - eauto using Judgment.
  - eapply j_univ.
    eauto using Permutation_app_tail.
  - eauto using Judgment, ok_type_perm1.
Qed.

Corollary j_kind_ctx_perm1 : forall Δ1 Δ2 x Γ t τ,
    ((Δ1 ++ x ~ tt) ++ Δ2 ; Γ ⊢ t : τ) ->
    ((Δ1 ++ Δ2) ++ x ~ tt ; Γ ⊢ t : τ).
Proof.
  intros. eapply j_kind_ctx_perm. 2:{ eassumption. }
  simpl_alist. apply Permutation_app.
  all: auto using Permutation_refl, Permutation_app_comm.
Qed.

(** *** Weakening *)
(******************************************************************************)
Theorem j_kind_ctx_weak : forall Δ1 Δ2 Γ t τ,
    ok_kind_ctx Δ2 ->
    disjoint Δ1 Δ2 ->
    Δ1 ; Γ ⊢ t : τ ->
    Δ1 ++ Δ2 ; Γ ⊢ t : τ.
Proof.
  introv ok disj j. induction j.
  - apply j_var; auto with sysf_ctx.
  - apply j_abs with (L := L); auto with sysf_ctx.
  - apply j_app with (τ1 := τ1); auto.
  - rename H0 into IH.
    apply j_univ with (L := L ∪ (domset Δ2)).
    intros_cof IH. apply j_kind_ctx_perm1.
    autorewrite with tea_rw_disj in *.
    intuition fsetdec.
  - apply j_inst; auto with sysf_ctx.
Qed.

(** *** Substitution *)
(******************************************************************************)
Theorem j_kind_ctx_subst : forall Δ1 x Δ2 Γ t τ τ',
    ok_type (Δ1 ++ Δ2) τ' ->
    (Δ1 ++ x ~ tt ++ Δ2 ; Γ ⊢ t : τ) ->
    (Δ1 ++ Δ2 ; envmap (subst typ ktyp x τ') Γ ⊢ subst term ktyp x τ' t : subst typ ktyp x τ' τ).
Proof.
  introv Hok j. remember (Δ1 ++ x ~ tt ++ Δ2) as rem.
  generalize dependent Δ2. induction j; intros; subst.
  - cbn. constructor.
    + eauto with sysf_ctx.
    + apply ok_type_ctx_sub.
      * eauto.
      * eauto.
      * eapply ok_type_lc; eauto.
    + rewrite in_envmap_iff. eauto.
  - rename H0 into IH.
    replace (subst (ix := I2) term ktyp x τ' (tm_abs τ1 t))
      with (tm_abs (subst typ ktyp x τ' τ1) (subst term ktyp x τ' t)).
    2:{ admit. }
    replace (subst (ix := I2) typ ktyp x τ' (ty_ar τ1 τ2))
      with (ty_ar (subst typ ktyp x τ' τ1) (subst typ ktyp x τ' τ2)).
    2:{ admit. }
    apply j_abs with (L := L ∪ {{ x }}).
    intros_cof IH.
    rewrite (subst_open_neq term) in IH.
    2:{ discriminate. }
    2:{ admit. }
    rewrite rw_subst_term_var_neq in IH; [ |fsetdec].
    rewrite envmap_app in IH. auto.
  - replace (subst (ix := I2) term ktyp x τ' (tm_app t1 t2))
      with (tm_app (subst (ix := I2) term ktyp x τ' t1) (subst (ix := I2) term ktyp x τ' t2)).
    2:{ admit. }
    replace (subst (ix := I2) typ ktyp x τ' (ty_ar τ1 τ2))
      with (ty_ar (subst typ ktyp x τ' τ1) (subst typ ktyp x τ' τ2)) in IHj1.
    2:{ admit. }
    apply j_app with (τ1 := (subst (ix := I2) typ ktyp x τ' τ1)).
    + apply IHj1. assumption. reflexivity.
    + apply IHj2. assumption. reflexivity.
  - rename H0 into IH.
    replace (subst (ix := I2) term ktyp x τ' (tm_tab t))
      with (tm_tab (subst (ix := I2) term ktyp x τ' t)).
    2:{ admit. }
    replace (subst (ix := I2) typ ktyp x τ' (ty_univ τ)) with
      (ty_univ (subst typ ktyp x τ' τ)).
    2:{ admit. }
    apply j_univ with (L := L ∪ {{x}}).
    intros_cof IH. simpl_alist in *.
    assert (x <> e) by fsetdec.
    rewrite (subst_open_eq term) in IH.
    2:{ now inverts Hok. }
    rewrite (subst_open_eq typ) in IH.
    2:{ now inverts Hok. }
    rewrite rw_subst_type_var_neq in IH; auto.
    apply IH.
    + change_alist ((Δ1 ++ Δ2) ++ e ~ tt).
      auto using ok_type_weak_r.
    + reflexivity.
  - replace (subst (ix := I2) term ktyp x τ' (tm_tap t τ1))
      with (tm_tap (subst (ix := I2) term ktyp x τ' t)
              (subst (ix := I2) typ ktyp x τ' τ1)).
    2:{ admit. }
    rewrite (subst_open_eq typ); auto.
    2:{ clear IHj j. eapply ok_type_lc; eauto. }
    auto using j_inst with sysf_ctx.
Admitted.

Theorem j_kind_ctx_subst1 : forall Δ x Γ t τ τ2,
    ok_type Δ τ2 ->
    (Δ ++ x ~ tt ; Γ ⊢ t : τ) ->
    (Δ ; envmap (subst typ ktyp x τ2) Γ ⊢ subst term ktyp x τ2 t : subst typ ktyp x τ2 τ).
Proof.
  introv jτ jt. change_alist (Δ ++ x ~ tt ++ []) in jt.
  change_alist (Δ ++ []) in jτ. change_alist (Δ ++ []).
  auto using j_kind_ctx_subst.
Qed.

(** ** Properties of <<Δ ; Γ ⊢ t : τ>> in <<Γ>> *)
(******************************************************************************)

(** *** <<Γ>> is always well-formed *)
(******************************************************************************)
Lemma j_type_ctx_wf : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    ok_type_ctx Δ Γ.
Proof.
  introv j. induction j; try assumption.
  - cleanup_cofinite. eauto using ok_type_ctx_inv_app_l.
  - rename H0 into IH.
    pick fresh e for (L ∪ atoms (bind (T := list) (fun '(x, t) => free typ ktyp t) Γ)).
    specialize_cof IH e.
    apply (ok_type_ctx_stren1) with (x := e).
    + assumption.
    + introv Hin.
      enough (lemma : ~ element_of (F := list) e (bind (T := list) (fun '(x, t) => free typ ktyp t) Γ)).
      { rewrite (in_bind_iff) in lemma.
        rewrite in_range_iff in Hin. destruct Hin as [x Hin].
        contradict lemma. exists (x, t0). split; [assumption|].
        now apply free_iff_FV. }
      { rewrite in_atoms_iff. fsetdec. }
Qed.

(** *** Tactical corollaries *)
(******************************************************************************)
Corollary j_type_ctx1 : forall Δ Γ t τ x τ2,
    (Δ ; Γ ⊢ t : τ) ->
    (x, τ2) ∈ (Γ : list (atom * _)) ->
    ok_type Δ τ2.
Proof.
  eauto using ok_type_ctx_binds, j_type_ctx_wf.
Qed.

Corollary j_type_ctx2 : forall Δ Γ t τ1 τ2 x,
    (Δ ; Γ ++ x ~ τ2 ⊢ t : τ1) ->
    ok_type Δ τ2.
Proof.
  intros. eapply j_type_ctx1. eauto.
  autorewrite with tea_list. eauto.
Qed.

(** *** Permutation *)
(******************************************************************************)
Theorem j_type_ctx_perm : forall Δ Γ1 Γ2 t τ,
    (Δ ; Γ1 ⊢ t : τ) ->
    Permutation Γ1 Γ2 ->
    (Δ ; Γ2 ⊢ t : τ).
Proof.
  introv j perm. generalize dependent Γ2.
  induction j; intros ? Hperm; try eauto using Judgment.
  - constructor.
    + eauto using ok_kind_ctx_perm.
    + rewrite ok_type_ctx_perm_gamma;
        eauto using Permutation_sym.
    + symmetry in Hperm.
      erewrite List.permutation_spec; eauto.
  - econstructor; eauto using Permutation_app_tail.
Qed.

Corollary j_type_ctx_perm_iff : forall Δ Γ1 Γ2 t τ,
    Permutation Γ1 Γ2 ->
    (Δ ; Γ1 ⊢ t : τ) <->
    (Δ ; Γ2 ⊢ t : τ).
Proof.
  introv Hperm. assert (Permutation Γ2 Γ1) by now symmetry.
  split; eauto using j_type_ctx_perm.
Qed.

Corollary j_type_ctx_perm1 : forall Δ Γ1 Γ2 x τ2 t τ1,
    (Δ ; (Γ1 ++ x ~ τ2) ++ Γ2 ⊢ t : τ1) <->
    (Δ ; (Γ1 ++ Γ2) ++ x ~ τ2 ⊢ t : τ1).
Proof.
  intros. apply j_type_ctx_perm_iff.
  simpl_alist. apply Permutation_app; auto using Permutation_app_comm.
Qed.

(** *** Weakening *)
(******************************************************************************)
Theorem j_type_ctx_weak : forall Δ Γ1 Γ2 t τ,
    ok_type_ctx Δ Γ2 ->
    disjoint Γ1 Γ2 ->
    (Δ ; Γ1 ⊢ t : τ) ->
    (Δ ; Γ1 ++ Γ2 ⊢ t : τ).
Proof.
  introv ok disj j.
  (* save knowledge that Δ is uniq for [j_inst] case *)
  pose proof (okΔ := j); apply j_kind_ctx_wf in okΔ.
  induction j.
  - apply j_var.
    + assumption.
    + now rewrite ok_type_ctx_app.
    + autorewrite with tea_list. auto.
  - apply j_abs with (L := L ∪ domset Γ2).
    +  (* todo need better automation here *)
      rename H0 into IH.
      intros_cof IH; auto. rewrite <- j_type_ctx_perm1.
      apply IH; auto. autorewrite with tea_rw_disj. intuition fsetdec.
  - apply j_app with (τ1 := τ1); auto.
  - apply j_univ with (L := L ∪ domset Δ). intros_cof H0.
    apply H0; auto.
    + auto using ok_type_ctx_weak_r.
    + rewrite ok_kind_ctx_app. autorewrite with tea_rw_disj.
      splits; intuition (auto using ok_kind_ctx_one; fsetdec).
  - apply j_inst.
    + auto.
    + apply IHj; auto.
Qed.

(** *** Substitution *)
(******************************************************************************)

(** ** Properties in τ of <<(Δ ; Γ ⊢ t : τ>> *)
(******************************************************************************)

(** *** <<τ>> is always locally closed *)
(******************************************************************************)
Lemma j_lc_type : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    LC typ ktyp τ.
Proof.
  introv j. induction j.
  - eapply ok_type_ctx_binds; eauto.
  - cc.
    replace (LC (ix := I2) typ ktyp (ty_ar τ1 τ2))
      with (LC typ ktyp τ1 /\ LC typ ktyp τ2).
    2:{ admit. }
    split.
    + eapply j_type_ctx2 in H.
      eapply ok_type_lc; eauto.
    + auto.
  - replace (LC (ix := I2) typ ktyp (ty_ar τ1 τ2))
      with (LC typ ktyp τ1 /\ LC typ ktyp τ2) in IHj1.
    2:{ admit. }
    easy.
  - cc.
    replace (LC (ix := I2) typ ktyp (ty_univ τ))
      with (LCn typ ktyp 1 τ).
    2:{ admit. }
    rewrite (open_lc_gap_eq_var typ); eauto.
  - rewrite <- (open_lc_gap_eq_iff_1 typ).
    + replace (LC (ix := I2) typ ktyp (ty_univ τ2))
        with (LCn typ ktyp 1 τ2) in IHj.
      2:{ admit. }
      assumption.
    + eapply ok_type_lc. eassumption.
Admitted.

(** *** <<τ>> is always well-formed *)
(******************************************************************************)
Lemma j_ok_type : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    ok_type Δ τ.
Proof.
  introv j. induction j.
  - eauto using ok_type_ctx_binds.
  - cc. replace (ok_type Δ (ty_ar τ1 τ2))
      with (ok_type Δ τ1 /\ ok_type Δ τ2).
    2:{ admit. }
    split.
    + eapply j_type_ctx2; eauto.
    + auto.
  - replace (ok_type Δ (ty_ar τ1 τ2))
      with (ok_type Δ τ1 /\ ok_type Δ τ2) in IHj1.
    2:{admit.}
    tauto.
  - replace (ok_type Δ (ty_univ τ)) with
      (scoped typ ktyp (ty_univ τ) (domset Δ) /\ LCn typ ktyp 1 τ).
    2:{admit.}
      rename H0 into IH.
    pick fresh e for (L ∪ FV typ ktyp τ).
    specialize_cof IH e. destruct IH as [IHsc IHlc]. split.
    + unfold ok_type, scoped in *.
      enough (cut: FV typ ktyp τ ⊆ domset (Δ ++ e ~ tt)).
      { autorewrite with tea_rw_dom in cut.
        replace (FV (ix := I2) typ ktyp (ty_univ τ)) with (FV typ ktyp τ).
        fsetdec. admit. }
      rewrite FV_open_lower; eauto; typeclasses eauto.
    + rewrite (open_lc_gap_eq_iff typ); eauto.
      replace (open (ix := I2) typ ktyp (ty_v (Fr e)) τ)
        with (ty_v (Fr e)) in IHlc.
      2:{ admit. }
      assumption.
  -
    (*
      rewrite ok_type_univ in IHj.
    destruct IHj.
    unfold ok_type in *; split.
    + unfold scoped in *.
      rewrite (freeset_open_upper typ). fsetdec.
    + unfold locally_closed.
      rewrite (open_lc_gap_eq_iff typ) in H1;
        eauto. tauto.
*)
Admitted.

(** ** Properties in t of <<(Δ ; Γ ⊢ t : τ>> *)
(******************************************************************************)

(** *** <<t>> is always locally closed w.r.t. term variables *)
(******************************************************************************)
Lemma j_lc_KTerm_term : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    LC term ktrm t.
Proof.
  introv j. induction j; try rename H0 into IH.
  - admit.
  - cc.
    replace (LC (ix := I2) term ktrm (tm_abs τ1 t))
      with (LCn term ktrm 1 t).
    2:{admit.}
      rewrite (open_lc_gap_eq_iff_1 term).
    + eassumption.
    + admit.
  - replace (LC (ix := I2) term ktrm (tm_app t1 t2))
      with (LC term ktrm t1 /\ LC term ktrm t2).
    2:{ admit. }
    tauto.
  - cc.
    replace (LC (ix := I2) term ktrm (tm_tab t))
      with (LC term ktrm t).
    2:{ admit. }
    rewrite (open_lc_gap_neq_var term).
    + exact IH.
    + discriminate.
  - replace (LC (ix := I2) term ktrm (tm_tap t τ1))
      with (LC term ktrm t).
    2:{ admit. }
    intuition (auto using lc_term_type).
Admitted.

(** *** <<t>> is always locally closed w.r.t. type variables *)
(******************************************************************************)
Lemma j_lc_ktyp_term : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    LC term ktyp t.
Proof.
  introv j. induction j.
  - admit.
  - cc.
    rename H0 into IH.
    replace (LC (ix := I2) term ktyp (tm_abs τ1 t))
      with (LC (ix := I2) typ ktyp τ1 /\ LC (ix := I2) term ktyp t).
    2:{ admit. }
    split.
    + apply j_type_ctx2 in H.
      eapply ok_type_lc. eassumption.
    + change (tm_var (Fr e)) with (mret SystemF ktrm (Fr e)) in IH.
      rewrite <- (open_lc_gap_neq_var term) in IH.
      * assumption.
      * discriminate.
  - replace (LC (ix := I2) term ktyp (tm_app t1 t2))
      with (LC term ktyp t1 /\ LC term ktyp t2).
    2:{admit.}
    tauto.
  - rename H0 into IH. cc.
    replace (LC (ix := I2) term ktyp (tm_tab t)) with
      (LCn term ktyp 1 t).
    2:{admit.}
      rewrite (open_lc_gap_eq_var term).
    + exact IH.
    + lia.
  - replace (LC (ix := I2) term ktyp (tm_tap t τ1))
      with (LC term ktyp t).
    2:{admit.} (* questionable *)
    Search LC "type".
    intuition (auto using lc_ktrm_type).
    (*
    eapply ok_type_lc; eauto.
    *)
Admitted.

(** *** <<t>> is always well-scoped w.r.t. type variables *)
(******************************************************************************)
Lemma j_sc_ktyp_term : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    scoped term ktyp t (domset Δ).
Proof.
  introv j. induction j; try rename H0 into IH.
  - unfold scoped. fsetdec.
  - unfold scoped. cc.
    replace (FV (ix := I2) term ktyp (tm_abs τ1 t))
      with (FV term ktyp t ∪ FV typ ktyp τ1).
    2:{admit.}
      assert (FV typ ktyp τ1 ⊆ domset Δ).
    { eapply j_type_ctx2 in H. apply H. }
    unfold scoped in IH.
    rewrite <- (FV_open_lower term) in IH.
    fsetdec.
  - unfold scoped in *.
    replace (FV (ix := I2) term ktyp (tm_app t1 t2))
      with (FV term ktyp t1 ∪ FV term ktyp t2).
    2:{admit.}
    fsetdec.
  - unfold scoped.
    replace (FV (ix := I2) term ktyp (tm_tab t))
      with (FV term ktyp t).
    2:{ admit. }
    pick fresh x for (L ∪ FV term ktyp t).
    specialize_cof IH x.
    unfold scoped in IH.
    rewrite <- (FV_open_lower term) in IH.
    eapply (scoped_stren_r term).
    + eauto.
    + fsetdec.
  - unfold scoped in *.
    replace (FV (ix := I2) term ktyp (tm_tap t τ1))
      with (FV (ix := I2) typ ktyp τ1 ∪ FV term ktyp t).
    2: {admit.}
    assert (FV typ ktyp τ1 ⊆ domset Δ) by apply H.
    fsetdec.
Admitted.

(** *** <<t>> is always well-scoped w.r.t. term variables *)
(******************************************************************************)
Lemma j_sc_KTerm_term : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    scoped term ktrm t (domset Γ).
Proof.
  introv j. induction j; try rename H0 into IH; unfold scoped in *.
  - rename H1 into Hin.
    replace (FV (ix := I2) term ktrm (tm_var (Fr x))) with {{x}}.
    2:{ admit. }
    apply in_in_domset in Hin. fsetdec.
  - replace (FV (ix := I2) term ktrm (tm_abs τ1 t))
      with (FV (ix := I2) term ktrm t).
    2:{ admit. }
    pick fresh x for (L ∪ FV term ktrm t).
    specialize_cof IH x.
    rewrite <- (FV_open_lower term) in IH.
    eapply (scoped_stren_r term).
    + eauto.
    + fsetdec.
  - replace (FV (ix := I2) term ktrm (tm_app t1 t2)) with
      (FV (ix := I2) term ktrm t1 ∪ FV term ktrm t2).
    2:{admit.}
    fsetdec.
  - replace (FV (ix := I2) term ktrm (tm_tab t))
      with (FV term ktrm t).
    2:{admit.}
    cc. etransitivity.
    pose (lemma := FV_open_lower term t (ktyp : K) (ktrm : K)).
    apply lemma. eauto.
  - replace (FV (ix := I2) term ktrm (tm_tap t τ1))
      with (FV term ktrm t).
    2:{admit.}
    assumption.
Admitted.

(** *** <<t>> is always well-formed *)
(******************************************************************************)
Lemma j_ok_term : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    ok_term Δ Γ t.
Proof.
  intros. unfold ok_term.
  intuition (eauto using j_sc_KTerm_term, j_sc_ktyp_term, j_lc_KTerm_term, j_lc_ktyp_term).
Qed.

(** *** Substitution *)
(******************************************************************************)
Theorem j_type_ctx_subst : forall Δ Γ1 Γ2 x τ2 t u τ1,
    (Δ ; Γ1 ++ x ~ τ2 ++ Γ2 ⊢ t : τ1) ->
    (Δ ; Γ1 ++ Γ2 ⊢ u : τ2) ->
    (Δ ; Γ1 ++ Γ2 ⊢ subst term ktrm x u t : τ1).
Proof.
  introv jt ju. remember (Γ1 ++ x ~ τ2 ++ Γ2) as Γ.
  generalize dependent Γ2. induction jt; intros; subst.
  - rename H0 into Hok. rename H1 into Hvar.
    compare values x and x0.
    + replace (subst (ix := I2) term ktrm x0 u (tm_var (Fr x0))) with u.
      2:{admit.}
      enough (τ = τ2) by congruence.
      eapply binds_mid_eq. apply Hvar. apply Hok.
    + replace (subst (ix := I2) term ktrm x u (tm_var (Fr x0)))
        with (tm_var (Fr x0)).
      2:{ admit. }
      apply j_var.
      { assumption. }
      { eauto with sysf_ctx. }
      { eauto using binds_remove_mid. }
  - rename H0 into IH.
    replace (subst (ix := I2) term ktrm x u (tm_abs τ1 t))
      with (tm_abs τ1 (subst term ktrm x u t)).
    2:{admit.}
    apply j_abs with (L := L ∪ {{ x }} ∪ domset Γ1 ∪ domset Γ2).
    intros_cof IH.
    rewrite (subst_open_eq term) in IH.
    2:{ eapply j_lc_KTerm_term; eauto. }
    rewrite (subst_fresh term) in IH.
    2:{ replace (free (ix := I2) term ktrm (tm_var (Fr e))) with [ e ].
        2:{admit.}
        autorewrite with tea_list. fsetdec. }
    simpl_alist in *. apply IH; auto.
    change_alist ((Γ1 ++ Γ2) ++ e ~ τ1).
    apply j_type_ctx_weak.
    + apply ok_type_ctx_one.
      specialize_cof H e. eapply j_type_ctx2; eassumption.
    + autorewrite with tea_rw_disj in *. intuition fsetdec.
    + assumption.
  - replace (subst (ix := I2) term ktrm x u (tm_app t1 t2))
      with (tm_app (subst term ktrm x u t1) (subst term ktrm x u t2)).
    2:{ admit. }
    eapply j_app; eauto.
  - rename H0 into IH.
    replace (subst (ix := I2) term ktrm x u (tm_tab t))
      with (tm_tab (subst term ktrm x u t)).
    2:{admit.}
    apply j_univ with (L := L ∪ domset Δ).
    intros_cof IH. rewrite (subst_open_neq term) in IH.
    2:{ discriminate. }
    2:{ eapply j_ok_term; eassumption. }
    apply IH; [reflexivity|].
    eapply j_kind_ctx_weak.
    + apply ok_kind_ctx_one.
    + autorewrite with tea_rw_disj. fsetdec.
    + assumption.
  - replace (subst (ix := I2) term ktrm x u (tm_tap t τ1))
      with (tm_tap (subst term ktrm x u t) τ1).
    2:{admit.}
    apply j_inst.
    + assumption.
    + auto.
Admitted.

Corollary j_type_ctx_subst1 : forall Δ Γ x τ2 t u τ1,
    (Δ ; Γ ++ x ~ τ2 ⊢ t : τ1) ->
    (Δ ; Γ ⊢ u : τ2) ->
    (Δ ; Γ ⊢ subst term ktrm x u t : τ1).
Proof.
  introv jt ju. change_alist (Γ ++ x ~ τ2 ++ []) in jt.
  change_alist (Γ ++ []) in ju. change_alist (Γ ++ []).
  eauto using j_type_ctx_subst.
Qed.

(** * Progress and preservation *)
(******************************************************************************)
Theorem preservation_theorem : preservation.
Proof.
  introv j. generalize dependent t'.
  remember (@nil (atom * unit)) as Delta.
  remember (@nil (atom * typ LN)) as Gamma.
  induction j; subst.
  - inversion 1.
  - inversion 1.
  - inversion 1; subst.
    + eauto using Judgment.
    + eauto using Judgment.
    + inverts j1. rename H4 into hyp.
      pick fresh e for (L ∪ FV term ktrm t0).
      rewrite (open_spec_eq term) with (x := e); [| fsetdec].
      eapply j_type_ctx_subst1; eauto.
      apply hyp. fsetdec.
  - inversion 1.
  - inversion 1; subst.
    + eauto using Judgment.
    + inverts j.
      pick fresh e for (L ∪ FV term ktyp t0 ∪ FV typ ktyp τ2).
      rewrite (open_spec_eq term) with (x := e); [|fsetdec].
      rewrite (open_spec_eq typ) with (x := e); [|fsetdec].
      change (@nil (atom * typ LN))
        with (envmap (subst typ ktyp e τ1) []).
      eapply j_kind_ctx_subst1.
      { assumption. }
      { apply H5. fsetdec. }
Qed.

Theorem  progress_theorem : progress.
Proof.
  introv j. remember (@nil (atom * unit)) as Delta.
  remember (@nil (atom * typ LN)) as Gamma.
  induction j; subst.
  - inversion H1.
  - left; auto using value.
  - right. specialize (IHj1 ltac:(trivial) ltac:(trivial)).
    specialize (IHj2 ltac:(trivial) ltac:(trivial)).
    intuition.
    + inverts H.
      { eauto using red. }
      { false. inverts j1. }
    + inverts H.
      { destruct_all_existentials.
        eauto using red, value. }
      { inverts j1. }
    + destruct_all_existentials.
      eauto using red.
    + destruct_all_existentials.
      eauto using red.
  - left; auto using value.
  - right. specialize (IHj ltac:(trivial) ltac:(trivial)).
    intuition.
    + inverts H0.
      { inverts j. }
      { eauto using red. }
    + destruct_all_existentials.
      eauto using red.
Qed.
