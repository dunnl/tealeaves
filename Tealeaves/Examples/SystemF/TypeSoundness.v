From Tealeaves Require Export
  Examples.SystemF.Syntax
  Examples.SystemF.Rewriting
  Examples.SystemF.Contexts.

From Coq Require Import
  Sorting.Permutation.

Implicit Types (x : atom).

Lemma rw_subst_type_var_neq {x y} {τ'} :
  x <> y ->
  subst typ KType x τ' (ty_v (Fr y)) = ty_v (Fr y).
Proof.
  autorewrite with sysf_rw. cbn. compare values x and y.
Qed.

Lemma rw_subst_term_var_neq {x y} {τ} :
  x <> y ->
  subst term KType x τ (tm_var (Fr y)) = tm_var (Fr y).
Proof.
  autorewrite with sysf_rw. cbn. compare values x and y.
Qed.

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
    apply j_univ with (L := L ∪ domset Δ2).
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
    (Δ1 ++ Δ2 ; envmap (subst typ KType x τ') Γ ⊢ subst term KType x τ' t : subst typ KType x τ' τ).
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
  - rename H0 into IH. simpl_F.
    apply j_abs with (L := L ∪ {{ x }}).
    intros_cof IH.
    rewrite (subst_open_neq term) in IH
      by (discriminate + apply lc_KTerm_type).
    rewrite rw_subst_term_var_neq in IH; [ |fsetdec].
    rewrite envmap_app in IH. auto.
  - simpl_F. eapply j_app.
    + autorewrite with sysf_rw in IHj1; eauto.
    + eauto.
  - rename H0 into IH. simpl_F.
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
  - autorewrite with sysf_rw in *.
    rewrite (subst_open_eq typ); auto.
    2:{ clear IHj j. eapply ok_type_lc; eauto. }
    auto using j_inst with sysf_ctx.
Qed.

Theorem j_kind_ctx_subst1 : forall Δ x Γ t τ τ2,
    ok_type Δ τ2 ->
    (Δ ++ x ~ tt ; Γ ⊢ t : τ) ->
    (Δ ; envmap (subst typ KType x τ2) Γ ⊢ subst term KType x τ2 t : subst typ KType x τ2 τ).
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
    pick fresh e for (L ∪ atoms (bind (T := list) (fun '(x, t) => free typ KType t) Γ)).
    specialize_cof IH e.
    apply (ok_type_ctx_stren1) with (x := e).
    + assumption.
    + introv Hin.
      enough (lemma : ~ element_of (F := list) e (bind (T := list) (fun '(x, t) => free typ KType t) Γ)).
      { rewrite (in_bind_iff) in lemma.
        rewrite in_range_iff in Hin. destruct Hin as [x Hin].
        contradict lemma. exists (x, t0). split; [assumption|].
        now apply free_iff_freeset. }
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
    locally_closed typ KType τ.
Proof.
  introv j. induction j.
  - eapply ok_type_ctx_binds; eauto.
  - cc. autorewrite with sysf_rw. split.
    + eapply j_type_ctx2 in H. eapply ok_type_lc; eauto.
    + auto.
  - now autorewrite with sysf_rw in IHj1.
  - cc. autorewrite with sysf_rw.
    rewrite (open_lc_gap_eq_var typ); eauto.
  - autorewrite with sysf_rw in IHj.
    rewrite <- (open_lc_gap_eq_iff_1 typ); eauto.
    eapply ok_type_lc; eauto.
Qed.

(** *** <<τ>> is always well-formed *)
(******************************************************************************)
Lemma j_ok_type : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    ok_type Δ τ.
Proof.
  introv j. induction j.
  - eauto using ok_type_ctx_binds.
  - cc. rewrite ok_type_ar. split.
    + eapply j_type_ctx2; eauto.
    + auto.
  - rewrite ok_type_ar in IHj1. tauto.
  - rewrite ok_type_univ. rename H0 into IH.
    pick fresh e for (L ∪ freeset typ KType τ).
    specialize_cof IH e. destruct IH as [IHsc IHlc]. split.
    + unfold ok_type, scoped in *.
      enough (freeset typ KType τ ⊆ domset (Δ ++ e ~ tt)).
      autorewrite with tea_rw_dom in H0. fsetdec.
      rewrite (freeset_open_lower typ); eauto.
    + rewrite (open_lc_gap_eq_iff typ); eauto.
      autorewrite with sysf_rw. eauto.
  - rewrite ok_type_univ in IHj. destruct IHj.
    unfold ok_type in *; split.
    + unfold scoped in *.
      rewrite (freeset_open_upper typ). fsetdec.
    + unfold locally_closed.
      rewrite (open_lc_gap_eq_iff typ) in H1;
        eauto. tauto.
Qed.

(** ** Properties in t of <<(Δ ; Γ ⊢ t : τ>> *)
(******************************************************************************)

(** *** <<t>> is always locally closed w.r.t. term variables *)
(******************************************************************************)
Lemma j_lc_KTerm_term : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    locally_closed term KTerm t.
Proof.
  introv j. induction j; try rename H0 into IH.
  - apply rw_lc_KTerm_term11.
  - cc. simpl_F.
    rewrite (open_lc_gap_eq_iff_1 term); eauto.
    apply rw_lc_KTerm_term11.
  - now simpl_F.
  - cc.
    autorewrite with sysf_rw.
    rewrite (open_lc_gap_neq_var term).
    + exact IH.
    + discriminate.
  - simpl_F. intuition (auto using lc_term_type).
Qed.

(** *** <<t>> is always locally closed w.r.t. type variables *)
(******************************************************************************)
Lemma j_lc_KType_term : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    locally_closed term KType t.
Proof.
  introv j. induction j.
  - apply rw_lc_KType_term1.
  - cc. simpl_F. split.
    + apply j_type_ctx2 in H. eapply ok_type_lc; eauto.
    + rename H0 into IH.
      change (tm_var (Fr e)) with (mret SystemF KTerm (Fr e)) in IH.
      rewrite <- (open_lc_gap_neq_var term) in IH; [auto|discriminate].
  - now simpl_F.
  - rename H0 into IH. cc.
    autorewrite with sysf_rw.
    rewrite (open_lc_gap_eq_var term).
    + exact IH.
    + lia.
  - simpl_F. intuition (auto using lc_KTerm_type).
    eapply ok_type_lc; eauto.
Qed.

(** *** <<t>> is always well-scoped w.r.t. type variables *)
(******************************************************************************)
Lemma j_sc_KType_term : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    scoped term KType t (domset Δ).
Proof.
  introv j. induction j; try rename H0 into IH.
  - unfold scoped. fsetdec.
  - unfold scoped. simpl_F. cc.
    assert (freeset typ KType τ1 ⊆ domset Δ).
    { apply j_type_ctx2 in H. apply H. }
    unfold scoped in IH.
    rewrite <- (freeset_open_lower term) in IH.
    fsetdec.
  - unfold scoped in *. simpl_F. fsetdec.
  - unfold scoped. simpl_F.
    pick fresh x for (L ∪ freeset term KType t).
    specialize_cof IH x.
    unfold scoped in IH.
    rewrite <- (freeset_open_lower term) in IH.
    eapply (scoped_stren_r term).
    + eauto.
    + fsetdec.
  - unfold scoped in *. simpl_F.
    assert (freeset typ KType τ1 ⊆ domset Δ) by apply H.
    fsetdec.
Qed.

(** *** <<t>> is always well-scoped w.r.t. term variables *)
(******************************************************************************)
Lemma j_sc_KTerm_term : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    scoped term KTerm t (domset Γ).
Proof.
  introv j. induction j; try rename H0 into IH; unfold scoped in *.
  - rename H1 into Hin. simpl_F.
    apply in_in_domset in Hin. fsetdec.
  - simpl_F. pick fresh x for (L ∪ freeset term KTerm t).
    specialize_cof IH x.
    rewrite <- (freeset_open_lower term) in IH.
    eapply (scoped_stren_r term).
    + eauto.
    + fsetdec.
  - simpl_F. fsetdec.
  - simpl_F. cc. etransitivity.
    pose (lemma := freeset_open_lower term t (KType : K) (KTerm : K)).
    apply lemma. eauto.
  - simpl_F. fsetdec.
Qed.

(** *** <<t>> is always well-formed *)
(******************************************************************************)
Lemma j_ok_term : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    ok_term Δ Γ t.
Proof.
  intros. unfold ok_term.
  intuition (eauto using j_sc_KTerm_term, j_sc_KType_term, j_lc_KTerm_term, j_lc_KType_term).
Qed.

(** *** Substitution *)
(******************************************************************************)
Theorem j_type_ctx_subst : forall Δ Γ1 Γ2 x τ2 t u τ1,
    (Δ ; Γ1 ++ x ~ τ2 ++ Γ2 ⊢ t : τ1) ->
    (Δ ; Γ1 ++ Γ2 ⊢ u : τ2) ->
    (Δ ; Γ1 ++ Γ2 ⊢ subst term KTerm x u t : τ1).
Proof.
  introv jt ju. remember (Γ1 ++ x ~ τ2 ++ Γ2) as Γ.
  generalize dependent Γ2. induction jt; intros; subst.
  - rename H0 into Hok. rename H1 into Hvar.
    compare values x and x0.
    + rewrite rw_subst_KTerm_term11.
      enough (τ = τ2) by congruence.
      eapply binds_mid_eq. apply Hvar. apply Hok.
    + rewrite rw_subst_KTerm_term12; [|assumption].
      apply j_var.
      { assumption. }
      { eauto with sysf_ctx. }
      { eauto using binds_remove_mid. }
  - rename H0 into IH. simpl_F.
    apply j_abs with (L := L ∪ {{ x }} ∪ domset Γ1 ∪ domset Γ2).
    intros_cof IH.
    rewrite (subst_open_eq term) in IH.
    2:{ eapply j_lc_KTerm_term; eauto. }
    rewrite (subst_fresh term) in IH.
    2:{ simpl_F. autorewrite with tea_list. fsetdec. }
    simpl_alist in *. apply IH; auto.
    change_alist ((Γ1 ++ Γ2) ++ e ~ τ1).
    apply j_type_ctx_weak.
    + apply ok_type_ctx_one.
      specialize_cof H e. eapply j_type_ctx2; eassumption.
    + autorewrite with tea_rw_disj in *. intuition fsetdec.
    + assumption.
  - simpl_F. eapply j_app; eauto.
  - rename H0 into IH.
    simpl_F. apply j_univ with (L := L ∪ domset Δ).
    intros_cof IH. rewrite (subst_open_neq term) in IH.
    2:{ discriminate. }
    2:{ eapply j_ok_term; eassumption. }
    apply IH; [reflexivity|].
    eapply j_kind_ctx_weak.
    + apply ok_kind_ctx_one.
    + autorewrite with tea_rw_disj. fsetdec.
    + assumption.
  - simpl_F. apply j_inst.
    + assumption.
    + auto.
Qed.

Corollary j_type_ctx_subst1 : forall Δ Γ x τ2 t u τ1,
    (Δ ; Γ ++ x ~ τ2 ⊢ t : τ1) ->
    (Δ ; Γ ⊢ u : τ2) ->
    (Δ ; Γ ⊢ subst term KTerm x u t : τ1).
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
      pick fresh e for (L ∪ freeset term KTerm t0).
      rewrite (open_spec_eq term) with (x := e); [| fsetdec].
      eapply j_type_ctx_subst1; eauto.
      apply hyp. fsetdec.
  - inversion 1.
  - inversion 1; subst.
    + eauto using Judgment.
    + inverts j.
      pick fresh e for (L ∪ freeset term KType t0 ∪ freeset typ KType τ2).
      rewrite (open_spec_eq term) with (x := e); [|fsetdec].
      rewrite (open_spec_eq typ) with (x := e); [|fsetdec].
      change (@nil (atom * typ LN))
        with (envmap (subst typ KType e τ1) []).
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
