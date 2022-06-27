From Tealeaves Require Import
     Functors.List
     LN.Leaf LN.Atom LN.AtomSet LN.AssocList
     LN.Multisorted.Operations
     LN.Multisorted.Theory.

From Multisorted Require Import
     Classes.DTM
     Theory.DTMContainer.

From Coq Require Import
     Sorting.Permutation.

From Tealeaves.Examples Require Import
     SystemF.Language
     SystemF.Rewriting
     SystemF.Contexts.

Implicit Types (x : atom).

Import SetlikeFunctor.Notations.
Import DTMContainer.Notations.
Import List.ListNotations.
Import LN.AssocList.Notations.

(** * Odds and Ends *)
(******************************************************************************)
Lemma permutation_fact : forall A (l1 l2 l3 : list A),
    Permutation ((l1 ++ l2) ++ l3)
                ((l1 ++ l3) ++ l2).
Proof.
  intros. simpl_alist. apply Permutation_app. auto.
  apply Permutation_app_comm.
Qed.

Lemma rw_subst_type13 {x y} {τ'} :
  x <> y ->
  subst typ KType x τ' (ty_v (Fr y)) = ty_v (Fr y).
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
  eauto using j_kind_ctx_perm, permutation_fact.
Qed.

Hint Resolve ok_kind_ctx_app1 : sysf_ctx.

(** *** Weakening *)
(******************************************************************************)
Theorem weak_j_kind_ctx : forall Δ1 Δ2 Γ t τ,
    ok_kind_ctx Δ2 ->
    disjoint Δ1 Δ2 ->
    (Δ1 ; Γ ⊢ t : τ) ->
    (Δ1 ++ Δ2 ; Γ ⊢ t : τ).
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


Lemma rw_subst_term_var {x y} {τ} :
  x <> y ->
  subst term KType x τ (tm_var (Fr y)) = tm_var (Fr y).
Proof.
  autorewrite with sysf_rw. cbn. compare values x and y.
Qed.

(** *** Substitution *)
(******************************************************************************)
Theorem subst_j_kind_ctx : forall Δ1 x Δ2 Γ t τ τ',
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
    assert (rw : subst term (KType : K) x τ' (tm_abs τ1 t) =
                 (tm_abs (subst typ KType x τ' τ1) (subst term (KType : K) x τ' t))) by admit.
    rewrite rw. clear rw.
    apply j_abs with (L := L ∪ {{ x }}).
    intros_cof IH.
    rewrite (subst_open_neq term) in IH
      by (discriminate + apply rw_lc_KTerm_type).
    rewrite rw_subst_term_var in IH; [ |fsetdec].
    rewrite envmap_app in IH. auto.
  - assert (rw : subst term KType x τ' (tm_app t1 t2) =
                 tm_app (subst term KType x τ' t1) (subst term KType x τ' t2)) by admit.
    rewrite rw; clear rw.
    eapply j_app.
    + autorewrite with sysf_rw in IHj1; eauto.
    + eauto.
  - rename H0 into IH. simpl_F.
    assert (rw : subst term KType x τ' (tm_tab t) =
                 tm_tab (subst term KType x τ' t)) by admit.
    rewrite rw; clear rw.
    apply j_univ with (L := L ∪ {{x}}).
    intros_cof IH. simpl_alist in *.
    assert (x <> e) by fsetdec.
    rewrite (subst_open_eq term) in IH.
    2:{ now inverts Hok. }
    rewrite (subst_open_eq typ) in IH.
    2:{ now inverts Hok. }
    rewrite rw_subst_type13 in IH; auto.
    apply IH.
    + change_alist ((Δ1 ++ Δ2) ++ e ~ tt).
      auto using ok_type_weak_r.
    + reflexivity.
  - simpl_F. rewrite (subst_open_eq typ); auto.
    2:{ clear IHj j. eapply ok_type_lc; eauto. }
    apply j_inst; auto with sysf_ctx.
Admitted.

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
    pick fresh e for L.
    (*
    pick fresh e for (L ∪ concatAtoms (envmap (freeset typ KType) Γ)).
     *)
    specialize_cof IH e.
    apply (ok_type_ctx_stren1) with (x := e).
    + assumption.
    + admit.
Admitted.

(** *** Tactical corollaries *)
(******************************************************************************)
Corollary j_type_ctx1 : forall Δ Γ t τ x τ2,
    (Δ ; Γ ⊢ t : τ) ->
    (x, τ2) ∈ Γ ->
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
Theorem perm_j_type_ctx : forall Δ Γ1 Γ2 t τ,
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
    + symmetry in Hperm. erewrite List.perm_set_eq; eauto.
  - econstructor; eauto using Permutation_app_tail.
Qed.

Corollary perm_j_type_ctx_iff : forall Δ Γ1 Γ2 t τ,
    Permutation Γ1 Γ2 ->
    (Δ ; Γ1 ⊢ t : τ) <->
    (Δ ; Γ2 ⊢ t : τ).
Proof.
  introv Hperm. assert (Permutation Γ2 Γ1) by now symmetry.
  split; eauto using perm_j_type_ctx.
Qed.

Corollary perm_j_type_ctx_1 : forall Δ Γ1 Γ2 x τ2 t τ1,
    (Δ ; (Γ1 ++ x ~ τ2) ++ Γ2 ⊢ t : τ1) <->
    (Δ ; (Γ1 ++ Γ2) ++ x ~ τ2 ⊢ t : τ1).
Proof.
  intros. apply perm_j_type_ctx_iff.
  apply permutation_fact.
Qed.

(** *** Weakening *)
(******************************************************************************)
Theorem weak_j_type_ctx : forall Δ Γ1 Γ2 t τ,
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
      intros_cof IH; auto. rewrite <- perm_j_type_ctx_1.
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
Theorem subst_j_kind_ctx_1 : forall Δ x Γ t τ τ2,
    ok_type Δ τ2 ->
    (Δ ++ x ~ tt ; Γ ⊢ t : τ) ->
    (Δ ; envmap (subst typ KType x τ2) Γ ⊢ subst term KType x τ2 t : subst typ KType x τ2 τ).
Proof.
  introv jτ jt. change_alist (Δ ++ x ~ tt ++ []) in jt.
  change_alist (Δ ++ []) in jτ. change_alist (Δ ++ []).
  auto using subst_j_kind_ctx.
Qed.

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
  - cc. autorewrite with sysf_rw. (*split.
    + eapply in_j_type_ctx2 in H. eapply ok_type_lc; eauto.
    + auto.
  - now autorewrite with sysf_rw in IHj1.
  - cc. autorewrite with sysf_rw.
    rewrite open_lc_gap_eq_var; eauto.
  - autorewrite with sysf_rw in IHj.
    rewrite <- open_lc_gap_eq_iff_1; eauto.
    eapply ok_type_lc; eauto.
*)
Admitted.

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
  (* now autorewrite with sysf_rw. *)
      admit.
  - rewrite ok_type_univ in IHj. destruct IHj.
    unfold ok_type in *; split.
    + unfold scoped in *.
      rewrite (freeset_open_upper typ). fsetdec.
    + unfold locally_closed.
      rewrite (open_lc_gap_eq_iff typ) in H1;
        eauto. tauto.
Admitted.

(** ** Properties in t of <<(Δ ; Γ ⊢ t : τ>> *)
(******************************************************************************)

(** *** <<t>> is always locally closed w.r.t. term variables *)
(******************************************************************************)
Lemma j_lc_KTerm_term : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    locally_closed term KTerm t.
Proof.
  introv j. induction j.
  - now simpl_F.
  - cc. simpl_F.
    rewrite open_lc_gap_eq_iff_1; eauto.
    now simpl_F.
  - now simpl_F.
  - rename H0 into IH. cc.
    autorewrite with sysf_rw.
    rewrite (open_lc_gap_neq_var).
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
  - now simpl_F.
  - cc. simpl_F. split.
    + apply in_j_type_ctx2 in H. eapply ok_type_lc; eauto.
    + rename Fr into fresh.
      change (tm_var (Fr e)) with (mret SystemF KTerm (Fr e)) in H0.
      rewrite <- (open_lc_gap_neq_var (H := I2) _ KTerm) in H0.
      2:{ discriminate. }
      auto.
  - now simpl_F.
  - rename H0 into IH. cc.
    autorewrite with sysf_rw.
    rewrite (open_lc_gap_eq_var).
    + exact IH.
    + auto.
  - simpl_F. intuition (auto using lc_term_type).
    eapply ok_type_lc; eauto.
Qed.

(** *** <<t>> is always well-scoped w.r.t. type variables *)
(******************************************************************************)
Lemma j_sc_KType_term : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    scoped_env term KType t Δ.
Proof.
  introv j. induction j; unfold scoped_env, scoped in *.
  - rewrite rw_freeset_KType_term12. fsetdec.
  - simpl_F. cc.
    assert (freeset typ KType τ1 ⊆ domset Δ).
    { apply in_j_type_ctx2 in H. apply H. }
    rewrite <- (freeset_open_lower) in H0.
    fsetdec.
  - simpl_F. fsetdec.
  - simpl_F. cc. admit.
  - simpl_F.
    assert (freeset typ KType τ1 ⊆ domset Δ) by apply H.
    fsetdec.
Admitted.

(** *** <<t>> is always well-scoped w.r.t. term variables *)
(******************************************************************************)
Lemma j_sc_KTerm_term : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    scoped_env term KTerm t Γ.
Proof.
  introv j. induction j; unfold scoped_env, scoped in *.
  - rewrite rw_freeset_KTerm_term12. admit.
  - simpl_F. cc.
    rewrite rw_freeset_KTerm_type.
    rewrite <- (freeset_open_lower_eq) in H0.
    admit.
  - simpl_F. fsetdec.
  - simpl_F. cc. admit.
  - simpl_F.
    rewrite rw_freeset_KTerm_type. fsetdec.
Admitted.

(** *** <<t>> is always well-formed *)
(******************************************************************************)
Lemma j_ok_tm_tm : forall Δ Γ t τ,
    (Δ ; Γ ⊢ t : τ) ->
    ok_term Δ Γ t.
Proof.
  intros. unfold ok_term.
  intuition (eauto using j_sc_KTerm_term, j_sc_KType_term,
             j_lc_KTerm_term, j_lc_KType_term).
Qed.

(** *** Substitution *)
(******************************************************************************)
Theorem subst_j_type_ctx : forall Δ Γ1 Γ2 x τ2 t u τ1,
    (Δ ; Γ1 ++ x ~ τ2 ++ Γ2 ⊢ t : τ1) ->
    (Δ ; Γ1 ++ Γ2 ⊢ u : τ2) ->
    (Δ ; Γ1 ++ Γ2 ⊢ subst term KTerm x u t : τ1).
Proof.
  introv jt ju. remember (Γ1 ++ x ~ τ2 ++ Γ2) as Γ.
  generalize dependent Γ2. induction jt; intros; subst.
  - simpl_F. unfold subst_loc. compare values x and x0.
    + enough (τ2 = τ) by congruence.
      eapply in_uniq_mid_eq.
      * inverts H0; eauto.
      * assumption.
    + constructor; eauto using ok_type_ctx_inv_mid, in_mid_neq.
  - rename H0 into IH.
    simpl_F. rewrite subst_KTerm_type.
    apply j_abs with (L := L ∪ {{ x }} ∪ domset Γ1 ∪ domset Γ2).
    intros_cof IH.
    rewrite subst_open_eq in IH.
    2:{ eapply j_lc_KTerm_term; eauto. }
    rewrite subst_fresh in IH.
    2:{ simpl_F. autorewrite with tea_list. fsetdec. }
    simpl_alist in *. apply IH; auto.
    change_alist ((Γ1 ++ Γ2) ++ e ~ τ1).
    apply weak_j_type_ctx.
    * apply ok_type_ctx_tm_one.
      specialize_cof H e. eapply in_j_type_ctx2; eauto.
    * autorewrite with tea_rw_disj in *. intuition fsetdec.
    * assumption.
  - simpl_F. eapply j_app; eauto.
  - rename H0 into IH.
    simpl_F. apply j_univ with (L := L).
    intros_cof IH. rewrite subst_open_neq in IH.
    2:{ discriminate. }
    2:{ eapply j_ok_tm_tm; eauto. }
    apply IH; eauto.
    eapply weak_j_kind_ctx.
    + admit.
    + admit.
    + admit.
  - simpl_F. rewrite subst_KTerm_type. apply j_inst.
    auto. apply IHjt. admit. auto.
Admitted.

Corollary subst_j_type_ctx_1 : forall Δ Γ x τ2 t u τ1,
    (Δ ; Γ ++ x ~ τ2 ⊢ t : τ1) ->
    (Δ ; Γ ⊢ u : τ2) ->
    (Δ ; Γ ⊢ subst term KTerm x u t : τ1).
Proof.
  introv jt ju. change_alist (Γ ++ x ~ τ2 ++ []) in jt.
  change_alist (Γ ++ []) in ju. change_alist (Γ ++ []).
  eauto using subst_j_type_ctx.
Qed.

(** * Progress and preservation *)
(******************************************************************************)
Theorem preservation_theorem : preservation.
Proof.
  introv j. generalize dependent t'.
  remember (@nil (atom * unit)) as Delta.
  remember (@nil (atom * typ leaf)) as Gamma.
  induction j; subst.
  - inversion 1.
  - inversion 1.
  - inversion 1; subst.
    + eauto using Judgment.
    + eauto using Judgment.
    + inverts j1. pick fresh e for (L ∪ freeset term KTerm t0).
      rewrite (open_spec_eq term) with (x := e); [| fsetdec].
      eapply subst_j_type_ctx_1; eauto.
      apply H4. fsetdec.
  - inversion 1.
  - inversion 1; subst.
    + eauto using Judgment.
    + inverts j.
      pick fresh e for (L ∪ freeset term KType t0 ∪ freeset typ KType τ2).
      rewrite (open_spec_eq) with (x := e); [|fsetdec].
      rewrite (open_spec_eq (F:=typ)) with (x := e); [|fsetdec].
      change (@nil (atom * typ leaf))
        with (subst (fun A : Type => alist typ A) KType e τ1 []).
      apply subst_j_kind_ctx_1; auto.
      apply H5. fsetdec.
Qed.

Theorem  progress_theorem : progress.
Proof.
  introv j. remember (@nil (atom * unit)) as Delta.
  remember (@nil (atom * typ leaf)) as Gamma.
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
