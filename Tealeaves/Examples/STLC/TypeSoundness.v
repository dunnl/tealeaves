From Tealeaves Require Export
  Examples.STLC.Syntax
  Examples.STLC.Simplification.

Export STLC.Syntax.Notations.

(** * Inversion lemmas *)
(******************************************************************************)
Lemma inversion11 : forall (A : typ) (x : atom) (Γ : ctx),
    Γ ⊢ tvar (Fr x) : A -> (x, A) ∈ Γ.
Proof.
  inversion 1; auto.
Qed.

Lemma inversion12 : forall (A : typ) (n : nat) (Γ : ctx),
    Γ ⊢ tvar (Bd n) : A -> False.
Proof.
  inversion 1; auto.
Qed.

(* This is somewhat weak because L should really be (dom Γ) *)
Lemma inversion21 : forall (A B : typ) (e : term LN) (Γ : ctx),
    (Γ ⊢ λ A e : B) ->
    exists C, B = A ⟹ C /\ exists L, forall (x : atom), ~ AtomSet.In x L -> Γ ++ x ~ A ⊢ e '(tvar (Fr x)) : C.
Proof.
  introv J.
  inversion J; subst.
  exists τ2. split; auto; exists L; auto.
Qed.

(** Inversion principle for [abs] where we may assume the abstraction has arrow type *)
Lemma inversion22 : forall (A B : typ) (e : term LN) (Γ : ctx),
    (Γ ⊢ λ A e : A ⟹ B) ->
    exists L, forall (x : atom), ~ AtomSet.In x L -> Γ ++ x ~ A ⊢ e '(tvar (Fr x)) : B.
Proof.
  introv J. apply inversion21 in J.
  destruct J as [C [H1 H2]].
  assert (B = C) by (inversion H1; auto); subst.
  assumption.
Qed.

Lemma inversion3 : forall (A : typ) (Γ : ctx) (t1 t2 : term LN),
    (Γ ⊢ [t1]@[t2] : A) ->
    exists B, (Γ ⊢ t1 : B ⟹ A) /\ (Γ ⊢ t2 : B).
Proof.
  introv J; inversion J; subst.
  exists A0. split; auto.
Qed.

(** * Misc lemmas *)
(******************************************************************************)
Theorem j_ctx_wf : forall Γ (t : term LN) (A : typ),
    Γ ⊢ t : A -> uniq Γ.
Proof.
  introv J. induction J.
  - assumption.
  - specialize_freshly H0.
    now autorewrite with tea_rw_uniq in H0.
  - assumption.
Qed.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun s : AtomSet.t => s) in
  let B := gather_atoms_with (fun x : atom => {{ x }}) in
  let C := gather_atoms_with (fun t : term LN => freeset t) in
  let D := gather_atoms_with (fun Γ : alist typ => domset Γ) in
  constr:(A ∪ B ∪ C ∪ D).

Theorem j_wf : forall Γ (t : term LN) (A : typ),
    Γ ⊢ t : A -> scoped t (domset Γ).
Proof.
  introv J. induction J.
  - unfold scoped. rewrite term_freeset12.
    intro y. rewrite AtomSet.singleton_spec. intro; subst.
    rewrite in_domset_iff. eauto.
  - rename H0 into IH; rename H into premise.
    specialize_freshly IH.
    unfold scoped in *.
    rewrite term_freeset2.
    assert (step1 : freeset t ⊆ freeset (t '(tvar (Fr e))))
      by apply freeset_open_lower.
    assert (step2 : forall x, x ∈@ (freeset t) -> x ∈@ (domset (Γ ++ e ~ τ1)))
      by fsetdec.
    intros x xin. assert (x <> e) by fsetdec.
    specialize (step2 x xin). rewrite domset_app in step2.
    cbn in step2. fsetdec.
  - unfold scoped in *. rewrite term_freeset3. fsetdec.
Qed.

Theorem is_bound_or_free_monotone : forall (k w1 w2 : nat) (l : LN),
    w1 < w2 ->
    is_bound_or_free k (w1, l) ->
    is_bound_or_free k (w2, l).
Proof.
  cbn. unfold_ops @Monoid_op_plus.
  introv Hlt Hyp. destruct l.
  + easy.
  + cbn in *. lia.
Qed.

Theorem lc_lam : forall (L : AtomSet.t) (t : term LN) (X : typ),
    (forall x : atom, ~ x ∈@ L -> locally_closed (t '(tvar (Fr x)))) ->
    locally_closed (λ X t).
Proof.
  introv hyp1. unfold locally_closed in *.
  rewrite term_lc_gap2. specialize_freshly hyp1.
  rewrite (open_lc_gap_eq_var_1). eauto.
Qed.

Theorem j_lc : forall Γ t A,
    Γ ⊢ t : A -> locally_closed t.
Proof.
  introv J. induction J.
  - now rewrite term_lc12.
  - pick fresh y excluding L and apply lc_lam; auto.
  - now rewrite term_lc3.
Qed.

Theorem weakening : forall Γ1 Γ2 Γ' (t : term LN) (A : typ),
    uniq Γ' ->
    disjoint Γ' (Γ1 ++ Γ2) ->
    (Γ1 ++ Γ2 ⊢ t : A) ->
    (Γ1 ++ Γ' ++ Γ2 ⊢ t : A).
Proof.
  introv Huq Hdj J.
  remember (Γ1 ++ Γ2) as Γrem.
  generalize dependent Γ2.
  induction J; intros; subst.
  - apply j_var. autorewrite with tea_rw_uniq tea_rw_disj in *.
    rewrite disjoint_sym. preprocess. intuition.
    simpl_list in *. intuition.
  - rename H0 into IH. pick fresh y and apply j_abs.
    specialize_cof IH y. simpl_alist in *.
    apply IH; auto. autorewrite with tea_rw_disj in *.
    splits; try easy. fsetdec.
  - eauto using j_app.
Qed.

Corollary weakening_r : forall Γ1 (t : term LN) (A : typ),
    (Γ1 ⊢ t : A) ->
    forall Γ2, uniq Γ2 -> disjoint Γ1 Γ2 -> Γ1 ++ Γ2 ⊢ t : A.
Proof.
  intros.
  rewrite <- (List.app_nil_r Γ1) in H.
  rewrite <- (List.app_nil_r (Γ1 ++ Γ2)).
  rewrite <- List.app_assoc.
  apply weakening; auto. List.simpl_list.
  eauto with tea_alist.
Qed.

Theorem substitution : forall Γ1 Γ2 (x : atom) (t u : term LN) (A B : typ),
    (Γ1 ++ x ~ A ++ Γ2 ⊢ t : B) ->
    (Γ1 ⊢ u : A) ->
    (Γ1 ++ Γ2 ⊢ t '{x ~> u} : B).
Proof.
  introv Jt Ju.
  specialize (j_ctx_wf (Γ1 ++ x~A ++ Γ2)); intro Hwf.
  assert (locally_closed u) by (eauto using j_lc).
  remember (Γ1 ++ x ~ A ++ Γ2) as Γrem. generalize dependent Γ2.
  induction Jt; intros.
  - cbn. compare values x and x0.
    + assert (A0 = A) by eauto using binds_mid_eq; subst.
      autorewrite with tea_rw_uniq tea_rw_disj in *.
      apply weakening_r.
      * easy.
      * easy.
      * intuition (auto with tea_alist).
    + constructor; eauto using uniq_remove_mid, binds_remove_mid.
  - cbn. apply j_abs with (L := L ∪ domset Γ ∪ {{x}}).
    intros_cof H1.
    unfold preincr. reassociate ->. rewrite (extract_incr).
    change (binddt (subst_loc x u ∘ extract) t)
      with (t '{x ~> u}).
    change (@tvar) with (@ret term _).
    rewrite <- subst_open_var.
    + simpl_alist in *. eapply H1.
      * eauto using j_ctx_wf.
      * subst. now simpl_alist.
    + fsetdec.
    + auto.
  - cbn. eauto using j_app.
Qed.

Corollary substitution_r : forall Γ (x : atom) (t u : term LN) (A B : typ),
    (Γ ++ x ~ A ⊢ t : B) ->
    (Γ ⊢ u : A) ->
    (Γ ⊢ t '{x ~> u} : B).
Proof.
  introv Jt Ju.
  change_alist (Γ ++ x ~ A ++ nil) in Jt.
  change_alist (Γ ++ nil).
  eapply substitution; eauto.
Qed.

Inductive value : term LN -> Prop :=
  | value_abs : forall X t, value (λ X t).

Inductive beta_step : term LN -> term LN -> Prop :=
| beta_app_l : forall (t1 t2 t1' : term LN),
    beta_step t1 t1' ->
    beta_step ([t1]@[t2]) ([t1']@[t2])
| beta_app_r : forall (t1 t2 t2' : term LN),
    beta_step t2 t2' ->
    beta_step ([t1]@[t2]) ([t1]@[t2'])
| beta_beta : forall (X : typ) (t u : term LN),
    beta_step ([λ X t]@[u]) (t '(u)).

Theorem subject_reduction_step : forall (t t' : term LN) Γ A,
    Γ ⊢ t : A -> beta_step t t' -> Γ ⊢ t' : A.
Proof.
  intros t t' Γ A J step.
  generalize dependent t'.
  induction J.
  - intros; inversion step.
  - intros; inversion step.
  - intros; inversion step.
    + subst. apply j_app with (A := A); auto.
    + subst. apply j_app with (A := A); auto.
    + subst. apply inversion21 in J1.
      destruct J1 as [C [hyp1 [L hyp2]]].
      inversion hyp1; subst.
      specialize_freshly hyp2.
      assert (rw : t '(t2) = t '(tvar (Fr e)) '{e ~> t2}).
      { erewrite open_spec_eq. reflexivity.
        fsetdec. }
      rewrite rw. eapply substitution_r.
      exact hyp2. assumption.
Qed.

Theorem progress : forall (t : term LN) A,
    nil ⊢ t : A -> value t \/ (exists t', beta_step t t').
Proof.
  intros. remember [] as ctx.
  induction H.
  - subst. inversion H0.
  - left; constructor.
  - rename IHJudgment1 into IH1.
    rename IHJudgment2 into IH2.
    specialize (IH1 Heqctx); specialize (IH2 Heqctx).
    destruct IH1.
    + inversion H1; subst.
      right. exists (t '(t2)). constructor.
    + right. destruct H1. eexists.
      apply beta_app_l. eauto.
Qed.
