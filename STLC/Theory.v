Require Import TeaLeaves.Internal.
Require Import TeaLeaves.Example.STLC.
Require Import TeaLeaves.Backend.LocallyNamelessTheorems.

Import Functor.
Import Monad.
Import ListableFunctor.Notations.
Import STLC.Notations.
Import Monoid.Notations.
Import LocallyNameless.LN.Monad.Notations.

Notation "'freeset'" := LN.Monad.freeset.
Notation "'locally_closed'" := LN.Monad.locally_closed.
Notation "'δ'" := (DecoratedFunctor.read).
Notation "'shift'" := ( DecoratedFunctor.shift).


Lemma inversion_var : forall (A : typ) (x : atom) (Γ : ctx),
    Γ ⊢ (Var (F x)) : A -> binds x A Γ.
Proof.
  inversion 1; auto.
Qed.

Lemma inversion_var_b : forall (A : typ) (n : nat) (Γ : ctx),
    Γ ⊢ (Var (B n)) : A -> False.
Proof.
  inversion 1; auto.
Qed.

(** TODO: This is somewhat weak because L should really be (dom Γ) *)
Lemma inversion_abs : forall (A B : typ) (e : term leaf) (Γ : ctx),
    (Γ ⊢ λ A ⋅ e : B) ->
    exists C, B = A ⇒ C /\ exists L, forall (x : atom), ~ AtomSet.In x L -> Γ ++ x ~ A ⊢ e '(Var (F x)) : C.
Proof.
  introv J.
  inversion J; subst.
  exists B0. split; auto; exists L; auto.
Qed.

(** Inversion principle for [abs] where we may assume the abstraction has arrow type *)
Lemma inversion_abs' : forall (A B : typ) (e : term leaf) (Γ : ctx),
    (Γ ⊢ λ A ⋅ e : A ⇒ B) ->
    exists L, forall (x : atom), ~ AtomSet.In x L -> Γ ++ x ~ A ⊢ e '(Var (F x)) : B.
Proof.
  introv J. apply inversion_abs in J.
  destruct J as [C [H1 H2]].
  assert (B = C) by (inversion H1; auto); subst.
  assumption.
Qed.

Lemma inversion_app : forall (A : typ) (Γ : ctx) (t1 t2 : term leaf),
    (Γ ⊢ [t1][t2] : A) ->
    exists B, (Γ ⊢ t1 : B ⇒ A) /\ (Γ ⊢ t2 : B).
Proof.
  introv J; inversion J; subst.
  exists A0. split; auto.
Qed.

Lemma in_abs_iff : forall (A : Type) t (x : A) (X : typ),
    (x ∈ λ X ⋅ t) <-> x ∈ t.
Proof.
  intros.
  reflexivity.
Qed.

Lemma in_freeset_abs_iff : forall (x : atom) (t : term leaf) (X : typ),
    In x (freeset (λ X ⋅ t)) <-> In x (freeset t).
Proof.
  intros.
  rewrite 2LN.in_freeset_F.
  apply in_abs_iff.
Qed.

Lemma freeset_abs_spec: forall (t : term leaf) (X : typ),
    freeset (λ X ⋅ t) [=] freeset t.
Proof.
  intros.
  unfold AtomSet.Equal.
  intros. apply in_freeset_abs_iff.
Qed.

Lemma in_read_abs_iff : forall t (l : leaf) (n : nat) (X : typ),
    (n, l) ∈ δ (λ X ⋅ t) <-> (n - 1, l) ∈ δ t /\ n <> 0.
Proof.
  introv.
  replace (δ (λ X ⋅ t) : term (nat * leaf)) with (λ X ⋅ shift 1 (δ t)).
  - rewrite in_abs_iff.
    (*
    rewrite in_shift_minus; try typeclasses eauto.
    split; intros [G1 G2]; split; auto; lia.
  - cbn. unfold shift. unfold Term.shift.
    f_equal. unfold fmap. *)
Admitted.

Lemma in_app_iff : forall (t1 t2 : term leaf) p,
    p ∈ ([t1][t2]) <-> p ∈ t1 \/ p ∈ t2.
Proof.
  introv. cbn.
  change (?x ++ ?y) with (x ● y).
  rewrite List.fold_op.
  reflexivity.
Qed.

Lemma in_freeset_app_iff : forall (t1 t2 : term leaf) (x : atom),
    In x (freeset ([t1][t2])) <-> In x (freeset t1) \/ In x (freeset t2).
Proof.
  intros.
  rewrite 3LN.in_freeset_F.
  apply in_app_iff.
Qed.

Lemma freeset_app_spec : forall (t1 t2 : term leaf),
    freeset ([t1][t2]) [=] freeset t1 ∪ freeset t2.
Proof.
  intros.
  intros y. rewrite AtomSet.union_spec. apply in_freeset_app_iff.
Qed.

Lemma in_read_app_iff : forall (t1 t2 : term leaf) p,
    p ∈ DecoratedFunctor.read ([t1][t2]) <-> p ∈ δ t1 \/ p ∈ δ t2.
Proof.
  introv. cbn.
  change (?x ++ ?y) with (x ● y).
  rewrite List.fold_op.
  reflexivity.
Qed.

Theorem j_ctx_wf : forall Γ (t : term leaf) (A : typ),
    Γ ⊢ t : A -> uniq Γ.
Proof.
  introv J. induction J.
  - assumption.
  - specialize_freshly H0. solve_uniq.
  - assumption.
Qed.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : AtomSet.t => x) in
  let B := gather_atoms_with (fun x : atom => AtomSet.singleton x) in
  let C := gather_atoms_with (fun x : term leaf => freeset x) in
  let D := gather_atoms_with (fun x : env typ => domset x) in
  constr:(A ∪ B ∪ C ∪ D).

Existing Instance LocallyNamelessModule_Monad.

Theorem j_wf : forall Γ (t : term leaf) (A : typ),
    Γ ⊢ t : A -> freeset t ⊆ domset Γ.
Proof.
  introv J. induction J.
  - apply binds_In in H0. cbn. fsetdec.
  - rename H0 into IH.
    rename H into premise.
    specialize_freshly IH.
    rewrite freeset_abs_spec.
    assert (step1 : freeset t ⊆ freeset (t '(Var (F e)))).
    { apply Theorems.freeset_open_lower. }
    assert (step2 : forall x, In x (freeset t) -> In x (domset (Γ ++ e ~ A))).
    { fsetdec. }
    intros x xin.
    assert (x <> e) by fsetdec.
    specialize (step2 x xin).
    rewrite dom_app in step2.
    cbn in step2. fsetdec.
  - rewrite freeset_app_spec.
    fsetdec.
Qed.
(*
Lemma in_open_var : forall (p : nat * leaf) (x : atom) (t : term),
    p ∈ δ (t '(Var (F x))) <-> exists (p1 : nat * leaf),
      p1 ∈ δ t /\ ((is_opened p1 /\ snd p = F x) \/ (~ is_opened p1 /\ p = p1)).
Proof.
  intros.
  rewrite in_dec_open_spec; try typeclasses eauto.
  split.
  - intros [p1 [p2 [G1 [G2 G3]]]].
    exists p1. splits; auto.
    destruct p1 as [p1_ctx [p1n | p1a]].
    + simpl in *. right. split; auto.

Admitted.
*)

Theorem lc_lam : forall (L : AtomSet.t) (t : term leaf) X,
    (forall x : atom, ~ AtomSet.In x L -> locally_closed (t '(Var (F x)))) ->
    locally_closed (λ X ⋅ t).
Proof.
  introv hyp.
  unfold LN.Monad.locally_closed in *.
  unfold LN.locally_closed in *.
  rewrite ListableFunctor.fa_iso in *.
  setoid_rewrite ListableFunctor.fa_iso in hyp.
  intros [pn pl] pIn.
  rewrite in_read_abs_iff in pIn.
  destruct pIn as [pIn pNz].
Admitted.

Theorem j_lc : forall Γ t A,
    Γ ⊢ t : A -> locally_closed t.
Proof.
  introv J. induction J.
  - cbv; intuition.
  - pick fresh y excluding L and apply lc_lam; auto.
  - unfold LN.Monad.locally_closed in *.
    unfold LN.locally_closed in *.
    cbn. rewrite List.fold_app.
    firstorder.
Qed.

Theorem weakening : forall Γ1 Γ2 Γ' (t : term leaf) (A : typ),
    uniq Γ' ->
    disjoint Γ' (Γ1 ++ Γ2) ->
    (Γ1 ++ Γ2 ⊢ t : A) ->
    (Γ1 ++ Γ' ++ Γ2 ⊢ t : A).
Proof.
  introv Huq Hdj J.
  remember (Γ1 ++ Γ2) as Γrem.
  generalize dependent Γ2.
  induction J; intros; subst.
  - apply j_var. solve_uniq.
    analyze_binds_uniq H0.
  - rename H0 into IH.
    pick fresh y and apply j_abs.
    specialize_cof IH y.
    simpl_alist in *.
    apply IH.
    (** TODO I shouldn't have to do this manually *)
    assert (LNotin : ~ AtomSet.In y (domset Γ')).
    { fsetdec. }
    solve_uniq. reflexivity.
  - eauto using j_app.
Qed.

Corollary weakening_r : forall Γ1 (t : term leaf) (A : typ),
    (Γ1 ⊢ t : A) ->
    forall Γ2, uniq Γ2 -> disjoint Γ1 Γ2 -> Γ1 ++ Γ2 ⊢ t : A.
Proof.
  intros.
  rewrite <- (List.app_nil_r Γ1) in H.
  rewrite <- (List.app_nil_r (Γ1 ++ Γ2)).
  rewrite app_assoc.
  apply weakening; auto.
Qed.

Theorem substitution : forall Γ1 Γ2 (x : atom) (t u : term leaf) (A B : typ),
    (Γ1 ++ x ~ A ++ Γ2 ⊢ t : B) ->
    (Γ1 ⊢ u : A) ->
    (Γ1 ++ Γ2 ⊢ t '{x ~> u} : B).
Proof.
  introv Jt Ju.
  specialize (j_ctx_wf (Γ1 ++ x~A ++ Γ2)); intro Hwf.
  assert (locally_closed u).
  { eauto using j_lc. }
  remember (Γ1 ++ x ~ A ++ Γ2) as Γrem.
  generalize dependent Γ2.
  induction Jt; intros.
  - Case "j_var".
    cbn. destruct_eq.
    + SCase "x = x0".
      assert (A0 = A).
      { subst. analyze_binds_uniq H1. }
      subst; apply weakening_r; auto.
      solve_uniq. solve_uniq.
    + SCase "x <> x0".
      subst. constructor.
      solve_uniq. analyze_binds H1.
  - cbn. apply j_abs with (L := L ∪ domset Γ ∪ {{x}}).
    intros_cof H1. change (join (fmap (subst_leaf x u) t)) with (t '{x ~> u}).
    replace (Var (A := leaf)) with (term.ret (A := leaf)).
    2:reflexivity.
    rewrite <- subst_open_var.
    + simpl_alist in *. eapply H1.
      (** TODO I shouldn't have to do this manually *)
      assert (~ AtomSet.In e (domset Γ)).
      { auto with set. }
      solve_uniq. subst. simpl_alist. reflexivity.
    + fsetdec.
    + auto.
  - cbn. eauto using j_app.
Qed.

Corollary substitution_r : forall Γ (x : atom) (t u : term) (A B : typ),
    (Γ ++ x ~ A ⊢ t : B) ->
    (Γ ⊢ u : A) ->
    (Γ ⊢ t '{x ~> u} : B).
Proof.
  introv Jt Ju.
  rewrite_alist (Γ ++ x ~ A ++ nil) in Jt.
  rewrite_alist (Γ ++ nil).
  eapply substitution; eauto.
Qed.

Inductive value : term -> Prop :=
  | value_abs : forall X t,
      value (λ X ⋅ t).

Inductive beta_step : term -> term -> Prop :=
| beta_app_l : forall (t1 t2 t1' : term),
    beta_step t1 t1' ->
    beta_step ([t1][t2]) ([t1'][t2])
| beta_app_r : forall (t1 t2 t2' : term),
    beta_step t2 t2' ->
    beta_step ([t1][t2]) ([t1][t2'])
| beta_beta : forall (X : typ) (t u : term),
    beta_step ([λ X ⋅ t][u]) (t '(u)).

Theorem subject_reduction_step : forall (t t' : term) Γ A,
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
    + subst. apply inversion_abs in J1.
      destruct J1 as [C [hyp1 [L hyp2]]].
      inversion hyp1; subst.
      specialize_freshly hyp2.
      assert (rw : t '(t2) = t '(Vf e) '{e ~> t2}).
      { eapply subst_intro; try typeclasses eauto.
        rewrite in_free_freeset. fsetdec. }
      rewrite rw. eapply substitution_r.
      exact hyp2. assumption.
Qed.

Theorem progress : forall (t : term) A,
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
