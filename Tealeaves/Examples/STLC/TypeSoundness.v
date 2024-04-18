From Tealeaves Require Export
  Examples.STLC.Syntax
  Examples.STLC.Simplification.

Export LN.Notations.
Export STLC.Syntax.Notations.
#[local] Open Scope set_scope.

Implicit Types (x: atom) (τ: typ)
  (t u: term LN) (n: nat) (v: LN) (Γ : ctx).

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun s : AtomSet.t => s) in
  let B := gather_atoms_with (fun x : atom => {{ x }}) in
  let C := gather_atoms_with (fun t : term LN => FV t) in
  let D := gather_atoms_with (fun Γ : alist typ => domset Γ) in
  constr:(A ∪ B ∪ C ∪ D).

(** * Inversion lemmas *)
(******************************************************************************)
Lemma inversion11 : forall (τ: typ) (x : atom) (Γ : ctx),
    Γ ⊢ tvar (Fr x) : τ -> (x, τ) ∈ Γ.
Proof.
  inversion 1; auto.
Qed.

Lemma inversion12 : forall (τ: typ) (n : nat) (Γ : ctx),
    Γ ⊢ tvar (Bd n) : τ -> False.
Proof.
  inversion 1; auto.
Qed.

(* This is somewhat weak because L should really be (dom Γ) *)
Lemma inversion21 : forall (τ B : typ) (e : term LN) (Γ : ctx),
    (Γ ⊢ λ τ e : B) ->
    exists C, B = τ ⟹ C /\ exists L, forall (x : atom),
        x `notin` L -> Γ ++ x ~ τ ⊢ e '(tvar (Fr x)) : C.
Proof.
  introv J.
  inversion J; subst.
  exists τ2. split; auto; exists L; auto.
Qed.

(** Inversion principle for [abs] where we may assume the abstraction has arrow type *)
Lemma inversion22 : forall (τ τ' : typ) (e : term LN) (Γ : ctx),
    Γ ⊢ λ τ e : τ ⟹ τ' ->
    exists L, forall (x : atom),
      x `notin` L ->
      Γ ++ x ~ τ ⊢ e '(x: term LN) : τ'.
Proof.
  introv J. apply inversion21 in J.
  destruct J as [C [H1 H2]].
  assert (τ' = C) by (inversion H1; auto); subst.
  assumption.
Qed.

Lemma inversion3 : forall (τ: typ) (Γ : ctx) (t1 t2 : term LN),
    (Γ ⊢ ⟨t1⟩ (t2) : τ) ->
    exists τ', (Γ ⊢ t1 : τ' ⟹ τ)
          /\ (Γ ⊢ t2 : τ').
Proof.
  introv J; inversion J; subst; eauto.
Qed.

(** * Misc lemmas *)
(******************************************************************************)
Theorem j_ctx_wf : forall Γ (t : term LN) (τ: typ),
    Γ ⊢ t : τ -> uniq Γ.
Proof.
  introv J; typing_induction.
  - assumption.
  - specialize_freshly IHbody.
    now autorewrite with tea_rw_uniq in IHbody.
  - assumption.
Qed.

Theorem j_wf : forall Γ (t : term LN) (τ: typ),
    Γ ⊢ t : τ -> FV t ⊆ domset Γ.
Proof.
  introv J. typing_induction.
  - simplify.
    apply in_in_domset in Hin.
    fsetdec.
  - specialize_freshly IHbody.
    simplify.
    assert (step1 : FV body ⊆ FV (body '(e: term LN)))
      by apply FV_open_lower.
    assert (step2 : forall x, x `in` FV body -> x `in` (domset (Γ ++ e ~ τ1)))
      by fsetdec.
    intros x xin.
    assert (x <> e) by fsetdec.
    specialize (step2 x xin).
    rewrite domset_app in step2.
    rewrite domset_one in step2.
    fsetdec.
  - simplify.
    fsetdec.
Qed.

Theorem lc_lam : forall (L : AtomSet.t) (t : term LN) (X : typ),
    (forall x : atom, ~ x `in` L -> LC (t '(x: term LN))) ->
    LC (λ X t).
Proof.
  introv HLC.
  simplify_LC.
  specialize_freshly HLC.
  change (fvar e) with (ret (Fr e)) in HLC.
  rewrite <- open_var_lcn_1 in HLC.
  assumption.
Qed.

Theorem j_lc : forall Γ t τ,
    Γ ⊢ t : τ -> LC t.
Proof.
  introv J. typing_induction.
  - simplify_LN. exact I.
  - pick fresh y excluding L and apply lc_lam.
    apply IHbody; auto.
  - simplify_LN. split; assumption.
Qed.

Theorem weakening : forall Γ1 Γ2 Γ' (t : term LN) (τ: typ),
    uniq Γ' ->
    disjoint Γ' (Γ1 ++ Γ2) ->
    (Γ1 ++ Γ2 ⊢ t : τ) ->
    (Γ1 ++ Γ' ++ Γ2 ⊢ t : τ).
Proof.
  introv Huq Hdj J.
  remember (Γ1 ++ Γ2) as Γrem.
  generalize dependent Γ2.
  typing_induction; intros Γ2 HeqΓ; subst.
  - apply j_var.
    { autorewrite with tea_rw_uniq tea_rw_disj in *.
      rewrite disjoint_sym.
      preprocess; intuition. }
    simpl_list in *.
    intuition.
  - pick fresh y and apply j_abs.
    specialize_cof IHbody y.
    simpl_alist in IHbody.
    simpl_alist.
    apply IHbody.
    { autorewrite with tea_rw_disj in *.
      splits; try easy. fsetdec. }
    { reflexivity. }
  - eauto using j_app.
Qed.

Corollary weakening_r : forall Γ1 (t : term LN) (τ: typ),
    (Γ1 ⊢ t : τ) ->
    forall Γ2, uniq Γ2 -> disjoint Γ1 Γ2 -> Γ1 ++ Γ2 ⊢ t : τ.
Proof.
  intros.
  rewrite <- (List.app_nil_r Γ1) in H.
  rewrite <- (List.app_nil_r (Γ1 ++ Γ2)).
  rewrite <- List.app_assoc.
  apply weakening; auto.
  List.simpl_list.
  eauto with tea_alist.
Qed.

Theorem substitution: forall Γ1 Γ2 x t u τ1 τ2,
    (Γ1 ++ x ~ τ1 ++ Γ2 ⊢ t : τ2) ->
    (Γ1 ⊢ u : τ1) ->
    Γ1 ++ Γ2 ⊢ t '{x ~> u} : τ2.
Proof.
  introv Jt Ju.
  specialize (j_ctx_wf (Γ1 ++ x ~ τ1 ++ Γ2)); intro Hwf.
  assert (LC u) by (eauto using j_lc).
  remember (Γ1 ++ x ~ τ1 ++ Γ2) as Γrem.
  generalize dependent Γ2.
  typing_induction_on Jt; intros Γ2 HeqΓ.
  - compare values x and x0.
    + simplify_subst.
      simpl_local.
      assert (τ = τ1) by eauto using binds_mid_eq; subst.
      apply weakening_r.
      { assumption. }
      { autorewrite with tea_rw_uniq tea_rw_disj in *.
        intuition. }
      { autorewrite with tea_rw_uniq tea_rw_disj in *.
        intuition. }
    + simplify_subst.
      simpl_local.
      apply j_var.
      { autorewrite with tea_rw_uniq tea_rw_disj in *.
        intuition. }
      { eauto using binds_remove_mid. }
  - simplify_subst.
    apply j_abs with (L := L ∪ domset Γ ∪ {{x}}).
    intros_cof IHbody.
    change (fvar e) with (ret (Fr e)).
    rewrite <- subst_open_var.
    + simpl_alist in *.
      eapply IHbody.
      * eauto using j_ctx_wf.
      * subst. now simpl_alist.
    + fsetdec.
    + auto.
  - simplify. eauto using j_app.
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
    beta_step (⟨t1⟩ (t2)) (⟨t1'⟩(t2))
| beta_app_r : forall (t1 t2 t2' : term LN),
    beta_step t2 t2' ->
    beta_step (⟨t1⟩(t2)) (⟨t1⟩(t2'))
| beta_beta : forall τ t u,
    beta_step (⟨λ τ t⟩(u)) (t '(u)).

Theorem subject_reduction_step : forall (t t' : term LN) Γ A,
    Γ ⊢ t : A -> beta_step t t' -> Γ ⊢ t' : A.
Proof.
  introv J Hstep.
  generalize dependent t'.
  typing_induction; intros t' Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep.
    + subst. eauto using j_app.
    + subst. eauto using j_app.
    + subst.
      apply inversion21 in J1.
      destruct J1 as [C [hyp1 [L hyp2]]].
      inversion hyp1; subst.
      specialize_freshly hyp2.
      rewrite (open_spec _ _ e).
      { eauto using substitution_r. }
      { fsetdec. }
Qed.

Theorem progress : forall (t : term LN) τ1,
    nil ⊢ t : τ1 -> value t \/ (exists t', beta_step t t').
Proof.
  introv J. remember [] as ctx.
  typing_induction; subst.
  - inversion Hin.
  - left. constructor.
  - specialize (IHJ1 eq_refl).
    specialize (IHJ2 eq_refl).
    destruct IHJ1.
    + right. inversion H; subst.
      exists (t '(t2)). constructor.
    + right.
      destruct H as [t1' Hstep'].
      eauto using beta_app_l.
Qed.
