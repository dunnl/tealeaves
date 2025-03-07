From Coq Require Import
  Relations.Relations
  Classes.RelationClasses.
From Tealeaves Require Import
  Backends.DB.

Import DecoratedTraversableMonad.UsefulInstances.

#[local] Set Implicit Arguments.

Import DB.Notations.

Inductive lam (V : Type) :=
| tvar : V -> lam V
| abs  : lam V -> lam V
| app  : lam V -> lam V -> lam V.

Fixpoint binddt_lam (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f : nat * v1 -> G (lam v2)) (t : lam v1) : G (lam v2) :=
  match t with
  | tvar v    => f (0, v)
  | abs body  => pure (@abs v2) <⋆> binddt_lam (f ⦿ 1) body
  | app t1 t2 => pure (@app v2) <⋆> binddt_lam f t1 <⋆> binddt_lam f t2
  end.

#[export] Instance Return_STLC: Return lam := tvar.
#[export] Instance Binddt_STLC: Binddt nat lam lam := @binddt_lam.
#[export] Instance DTM_STLC: DecoratedTraversableMonad nat lam.
Proof.
  derive_dtm.
Qed.

#[export] Instance Map_STLC: Map lam
  := DerivedOperations.Map_Binddt nat lam lam.
#[export] Instance Mapd_STLC: Mapd nat lam
  := DerivedOperations.Mapd_Binddt nat lam lam.
#[export] Instance Traverse_STLC: Traverse lam
  := DerivedOperations.Traverse_Binddt nat lam lam.
#[export] Instance Mapdt_STLC: Mapdt nat lam
  := DerivedOperations.Mapdt_Binddt nat lam lam.
#[export] Instance Bind_STLC: Bind lam lam
  := DerivedOperations.Bind_Binddt nat lam lam.
#[export] Instance Bindd_STLC: Bindd nat lam lam
  := DerivedOperations.Bindd_Binddt nat lam lam.
#[export] Instance Bindt_STLC: Bindt lam lam
  := DerivedOperations.Bindt_Binddt nat lam lam.
#[export] Instance ToSubset_STLC: ToSubset lam
  := ToSubset_Traverse.
#[export] Instance ToBatch_STLC: ToBatch lam
  := DerivedOperations.ToBatch_Traverse.

Import Notations.

Implicit Types (s t u v : lam nat) (x y : nat)
  (σ τ : nat -> lam nat) (ρ : nat -> nat).
Generalizable Variables s t u v x y σ τ ρ.
Create HintDb churchrosser.

Declare Custom Entry lambda.

(* Import DB.DB.Notations. *) (* Tealeaves notations *)
Import DB.AutosubstShim.Notations. (* Autosubst-like notations *)

Module Notations.
  Notation "{| e |}" :=
    e (e custom lambda at level 99).
  Notation "t1 t2" :=
    (app t1 t2) (in custom lambda at level 1, left associativity).
  Notation "\, t" :=
    (abs t) (in custom lambda at level 90,
          t custom lambda at level 99, left associativity).
  Notation "( x )" :=
    x (in custom lambda, x at level 99).
  Notation "x" :=
    x (in custom lambda at level 0, x constr at level 0).
End Notations.

Import Notations.

(* One step of beta reduction *)
Inductive step : lam nat -> lam nat -> Prop :=
| step_beta : forall tbody targ, step (app (abs tbody) targ) (subst (targ .: ret) tbody)
| step_app_l : forall u1 u2 t, step u1 u2 -> step (app u1 t) (app u2 t)
| step_app_r : forall u t1 t2, step t1 t2 -> step (app u t1) (app u t2)
| step_lam : forall u1 u2, step u1 u2 -> step (abs u1) (abs u2).

Notation "s → t" := (step s t) (at level 50).

#[export] Hint Constructors step : churchrosser.

Definition steps : relation (lam nat) := clos_refl_trans _ step.

#[export] Instance: Reflexive steps.
Proof.
  unfold Reflexive. apply rt_refl.
Qed.

#[export] Instance: Transitive steps.
Proof.
  unfold Transitive. apply rt_trans.
Qed.

#[export] Hint Constructors clos_refl_trans : churchrosser.

Notation "t1 →* t2" := (steps t1 t2) (at level 50).

Lemma steps_app_l : forall s1 s2 t, steps s1 s2 -> steps (app s1 t) (app s2 t).
Proof.
  intros. induction H.
  - apply rt_step. apply step_app_l. assumption.
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Lemma steps_app_r : forall s t1 t2, steps t1 t2 -> steps (app s t1) (app s t2).
Proof.
  induction 1; unfold steps; eauto with churchrosser.
Qed.

Lemma steps_lam : forall t1 t2, steps t1 t2 -> steps (abs t1) (abs t2).
Proof.
  induction 1; unfold steps; eauto with churchrosser.
Qed.

#[export] Hint Resolve
  steps_app_r steps_lam steps_app_l : churchrosser.

Section rel_properties.

  Context
    (R1 R2 : relation (lam nat)).

  Definition GDiamond := forall t t1 t2,
      R1 t t1 ->
      R1 t t2 ->
      exists t3, R2 t1 t3 /\ R2 t2 t3.

  Definition Diamond := forall t t1 t2,
      R1 t t1 ->
      R1 t t2 ->
      exists t3, R1 t1 t3 /\ R1 t2 t3.

End rel_properties.

Definition local_confluence : Prop := GDiamond step steps.
Definition confluence : Prop := Diamond steps.

#[export] Hint Unfold confluence local_confluence Diamond GDiamond : core.

Reserved Notation "t1 ⇒ t2" (at level 50).

Inductive par : lam nat -> lam nat -> Prop :=
| par_refl :
  `(tvar x ⇒ tvar x)
| par_app :
  `(s1 ⇒ s2 ->
    t1 ⇒ t2 ->
    {| s1 t1 |} ⇒ {| s2 t2 |})
| par_abs :
  `(s1 ⇒ s2 ->
    {|\, s1|} ⇒ {|\, s2|})
| par_beta :
  `(s1 ⇒ s2 ->
    t1 ⇒ t2 ->
    {| (\, s1) t1 |} ⇒ subst (t2 .: ret) s2)
where "t1 ⇒ t2" := (par t1 t2).

#[export] Instance: Reflexive par.
Proof.
  intro t. induction t; auto using par.
Qed.

Definition pars : relation (lam nat) := clos_refl_trans _ par.

#[export] Instance: Reflexive pars.
Proof.
  unfold Reflexive. apply rt_refl.
Qed.

#[export] Instance: Transitive pars.
Proof.
  unfold Transitive. apply rt_trans.
Qed.

Notation "t1 ⇒* t2" := (pars t1 t2) (at level 50).

#[export] Hint Constructors par : churchrosser.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Relating →, →*, ⇒, and ⇒*
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

Lemma step_in_par : `(t1 → t2 -> t1 ⇒ t2).
Proof.
  intros ? ? Hstep. induction Hstep.
  - apply par_beta.
    + reflexivity.
    + reflexivity.
  - apply par_app.
    + assumption.
    + reflexivity.
  - apply par_app.
    + reflexivity.
    + assumption.
  - apply par_abs.
    assumption.
Qed.

Lemma par_in_steps : `(t1 ⇒ t2 -> t1 →* t2).
Proof.
  intros ? ? Hstep. induction Hstep.
  - reflexivity.
  - transitivity {| s1 t2 |}.
    + apply steps_app_r.
      assumption.
    + apply steps_app_l.
      assumption.
  - apply steps_lam.
    assumption.
  - transitivity {| (\, s1) t2 |}.
    + apply steps_app_r.
      assumption.
    + transitivity {| (\, s2) t2 |}.
      * apply steps_app_l.
        apply steps_lam.
        assumption.
      * apply rt_step. apply step_beta.
Qed.

Lemma pars_in_steps : `(t1 ⇒* t2 -> t1 →* t2).
Proof.
  induction 1. now apply par_in_steps.
  reflexivity. etransitivity; eauto.
Qed.

Lemma steps_in_pars : `(t1 →* t2 -> t1 ⇒* t2).
Proof.
  intros ? ? Hstep. induction Hstep.
  - apply rt_step. now apply step_in_par.
  - reflexivity.
  - etransitivity.
    + eassumption.
    + assumption.
Qed.

Goal `(t1 → t2 -> t1 ⇒ t2).
Proof.
  induction 1; now constructor.
Qed.

#[export] Hint Resolve step_in_par : churchrosser.

Goal `(t1 ⇒ t2 -> t1 →* t2).
Proof with (eauto with churchrosser).
  induction 1.
  - reflexivity.
  - etransitivity...
  - idtac...
  - etransitivity...
    etransitivity...
    unfold steps.
    etransitivity...
Qed.

Goal `(t1 →* t2 -> t1 ⇒* t2).
Proof.
  induction 1; unfold pars; eauto with churchrosser.
Qed.

Goal `(t1 ⇒* t2 -> t1 →* t2).
Proof with eauto with churchrosser.
  induction 1; unfold steps...
  apply pars_in_steps. unfold pars...
Qed.

Notation "σ1 ▷ σ2" := (forall x, σ1 x ⇒ σ2 x) (at level 50).

Tactic Notation "asimpl" := simplify_db_like_autosubst.

Lemma step_subst: forall s t,
    s ⇒ t -> forall σ, subst σ s ⇒ subst σ t.
Proof with auto using par.
  introv Hstep.
  induction Hstep; intros σ.
  - asimpl. reflexivity.
  - asimpl...
  - asimpl...
  - asimpl.
    replace (subst (subst σ t2 .: σ) s2) with
      (subst (subst σ t2 .: ret) (subst (up__sub σ) s2)) by now asimpl.
    apply par_beta; auto.
    asimpl...
Qed.

Lemma par_strong_rename : `(t1 ⇒ t2 -> rename ρ t1 ⇒ rename ρ t2).
Proof with auto with churchrosser.
  intros.
  rewrite rename_to_subst.
  generalize dependent ρ.
  induction H; intros.
  - reflexivity.
  - asimpl...
  - asimpl...
    eauto with churchrosser.
  - specialize
      (@par_beta
         (rename (up__ren ρ) s1)
         (rename (up__ren ρ) s2)
         (rename ρ t1)
         (rename ρ t2)).
    asimpl...
Qed.

Lemma par_subst_up : forall σ1 σ2, σ1 ▷ σ2 -> up__sub σ1 ▷ up__sub σ2.
Proof.
  intros. induction x.
  - reflexivity.
  - enough (rename (+1) (σ1 x) ⇒ rename (+1) (σ2 x)).
    asimpl.
    rewrite rename_to_subst in H0.
    cbn. auto.
    apply par_strong_rename.
    apply H.
Qed.

Lemma par_strong_subst s t σ1 σ2 :
  s ⇒ t -> σ1 ▷ σ2 -> s.[σ1] ⇒ t.[σ2].
Proof with auto using par.
  intros Hstep.
  generalize dependent σ1.
  generalize dependent σ2.
  induction Hstep; intros ? ? Hsub.
  - asimpl...
  - asimpl...
  - asimpl.
    apply par_abs.
    apply IHHstep.
    specialize (@par_subst_up _ _ Hsub).
    simplify_db_unfold_phase. auto.
  - asimpl.
    replace (s2.[t2.[σ2] .: σ2]) with (s2.[up__sub σ2].[t2.[σ2]/]).
    { apply par_beta.
      apply IHHstep1.
      specialize (@par_subst_up _ _ Hsub).
      simplify_db_unfold_phase; auto.
      auto. }
    { asimpl.
      reflexivity. }
Qed.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Normalization for ``par``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

Fixpoint normalize (t : lam nat) : lam nat :=
  match t with
  | tvar x => tvar x
  | abs s => abs (normalize s)
  | app (abs t1) t2 => (normalize t1).[normalize t2/]
  | app t1 t2 => app (normalize t1) (normalize t2)
  end.

Lemma par_triangle : forall (t1 t2 : lam nat), t1 ⇒ t2 -> t2 ⇒ normalize t1.
Proof.
  intros. generalize dependent t2. induction 1.
  - reflexivity.
  - cbn.
    destruct s1.
    + auto using par_app.
    + inversion H. subst.
      inversion IHpar1. subst.
      auto using par_beta.
    + auto using par_app.
  - cbn. auto using par_abs.
  - cbn. apply par_strong_subst.
    auto. now intros [|?].
Qed.

Theorem par_diamond : Diamond par.
Proof.
  unfold Diamond. intros ? ? ? H1 H2.
  exists (normalize t). intuition auto using par_triangle.
Qed.

Lemma strip_lemma : `(t ⇒ t1 -> t ⇒* t2 -> exists t3, t1 ⇒* t3 /\ t2 ⇒ t3).
Proof with auto using rt_step.
  intros ??? H1 Hstar. generalize dependent t1.
  induction Hstar; rename x into t; intros.
  - rename y into t2.
    destruct (par_diamond H1 H) as [t3 [? ?]].
    exists t3; unfold pars; split...
  - exists t1. split; [reflexivity| auto].
  - specialize (IHHstar1 t1 H1) as [t3 [? ?]].
    specialize (IHHstar2 t3 H0) as [t4 [? ?]].
    exists t4. split; [etransitivity; eauto| assumption].
Qed.

Theorem pars_diamond : Diamond pars.
Proof.
  unfold Diamond. intros ? ? ? Ht1 Ht2.
  generalize dependent t2. induction Ht1; intros.
  - rename x into t. rename y into t1.
    destruct (strip_lemma H Ht2) as [t3 [? ?]].
    exists t3. unfold pars in *. split; auto with churchrosser.
  - exists t2. unfold pars in *. split; auto with churchrosser.
  - destruct (IHHt1_1 t2 Ht2) as [t3 [? ?]].
    destruct (IHHt1_2 t3 H) as [t4 [? ?]].
    exists t4. split. assumption. etransitivity; eauto.
Qed.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Proving confluence of ``steps``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

Theorem confluence_proof : confluence.
Proof.
  unfold confluence. unfold Diamond. intros.
  assert (t ⇒* t1) by auto using steps_in_pars.
  assert (t ⇒* t2) by auto using steps_in_pars.
  destruct (pars_diamond (t := t) (t1 := t1) (t2 := t2) ltac:(auto) ltac:(auto))
    as [t3 [? ?]]. exists t3; split; now apply pars_in_steps.
Qed.

(*|
+++++++++++++++++++++
Beta equivalence
+++++++++++++++++++++

There are a couple ways to define the notion of :math:`\beta`-equivalence (a/k/a :math:`\beta`-conversion or :math:`\beta`-congruence). Just as ``steps`` was defined as the reflexive transitive closure of ``step``, ``beta_equiv`` can be defined as the reflexive *symmetric* transitive closure of ``step``, i.e. the smallest equivalence relation that contains ``step``.

As with ``steps``, the first thing we do after defining ``beta_equiv`` is prove that it is indeed reflexive, symmetric, and transitive, enabling the use of the correspondingly named tactics. We also give this relation a custom notation and add its constructors to our hint database.
|*)
Definition beta_equiv : relation (lam nat) := clos_refl_sym_trans _ step.

#[export] Instance: Reflexive beta_equiv.
Proof.
  unfold Reflexive. apply rst_refl.
Qed.

#[export] Instance: Symmetric beta_equiv.
Proof.
  unfold Symmetric. apply rst_sym.
Qed.

#[export] Instance: Transitive beta_equiv.
Proof.
  unfold Transitive. apply rst_trans.
Qed.

Notation "s ∼ t" := (beta_equiv s t) (at level 50).

#[export] Hint Constructors clos_refl_sym_trans : churchrosser.

(*|
Beta equivalence is also called a *congruence* relation, meaning an equivalence relation that is respected by a set of operations, in this case the constructors of ``(lam nat)``. By "respected by the constructors of ``(lam nat)``" I mean exactly the following three properties, much like ones we gave earlier for ``steps``.
|*)

Lemma beta_equiv_app_l : forall s1 s2 t, s1 ∼ s2 -> (app s1 t) ∼ (app s2 t).
Proof.
  induction 1; unfold beta_equiv; eauto with churchrosser.
Qed.

Lemma beta_equiv_app_r : `(t1 ∼ t2 -> {|s t1|} ∼ {|s t2|}).
Proof.
  induction 1; unfold beta_equiv; eauto with churchrosser.
Qed.

Lemma beta_equiv_lam : `(t1 ∼ t2 -> {|\, t1|} ∼ {|\, t2|}).
Proof.
  induction 1; unfold beta_equiv; eauto with churchrosser.
Qed.

#[export] Hint Resolve
  beta_equiv_app_r beta_equiv_lam beta_equiv_app_l : churchrosser.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Axiomatization of beta equivalence
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Instead of defining :math:`\beta`-equivalence as the equivalence closure of ``step``, another route is to define the relation inductively from a set of equational axioms, as shown below with ``beta_equiv_I``.
|*)

Reserved Notation "s ≃ t" (at level 50).

Inductive beta_equiv_I : lam nat -> lam nat -> Prop :=
| equ_refl  : `(s ≃ s)
| equ_sym   : `(s ≃ t ->
                t ≃ s)
| equ_trans : `(s ≃ t ->
                t ≃ u ->
                s ≃ u)
| equ_beta  : `({|(\, s) t|} ≃ s.[t/])
| equ_app_l : `(s1 ≃ s2 ->
                {|s1 t|} ≃ {|s2 t|})
| equ_app_r : `(t1 ≃ t2 ->
                {|s t1|} ≃ {|s t2|})
| equ_lam : `(s1 ≃ s2 ->
             {|\, s1|} ≃ {|\, s2|})
where "s ≃ t" := (beta_equiv_I s t).

#[export] Hint Constructors beta_equiv_I : churchrosser.

(*|
If you're following along in Barendregt, this definition of :math:`\beta`-congruence matches Barendregt's definition of the equational theory λ (Definition 2.1.4, pg. 23). In some sense this style of definition is simpler to think about (and to generalize to other calculi) because it does not require introducing an auxiliary relation like ``step``. This could be beneficial in situations where we know which terms we want to be *equal*, but it is not clear how to describe this equality in terms of *reduction* steps.

It is easy to show that our two definitions of beta conversion coincide.
|*)

Lemma beta_equiv_iff_beta_equiv_I : `(s ∼ t <-> s ≃ t).
Proof with auto with churchrosser.
  intros. split.
  - induction 1...
    + induction H...
    + eauto with churchrosser.
  - induction 1...
    + reflexivity.
    + symmetry...
    + etransitivity; eassumption.
    + unfold beta_equiv...
Qed.

(*|
++++++++++++++++++++++++++++++++++++
Corollaries of confluence
++++++++++++++++++++++++++++++++++++

Confluence is a pleasing technical property with a few useful corollaries. First, if we want to know whether two terms are beta-equivalent, by confluence it suffices to check whether the terms can be reduced to a common term. This is important because, at face value, deciding equivalence sounds much harder. Second, it implies that *if* a given lambda term ``t`` reduces to some irreducible term ``s``, this property unique defines ``s``. This is important because beta-reduction is non-deterministic, and the prior statement implies any reduction sequence that discovers a normal form for ``t`` must find the *same* normal form. In the context of *typed* lambda calculi that enjoy strong normalization (a separate topic), this fact implies it is decidable whether two terms are :math:`beta`-equivalent. In particular, this a crucial theoretical fact underlying how Coq itself decides whether two terms are *defintionally equal*, a key aspect of Coq and theorem proving in general.

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Transitivity of common reduct
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

|*)

Definition have_common_reduct : lam nat -> lam nat -> Prop :=
  fun s t => exists u, s →* u /\ t →* u.

#[export] Instance: Transitive have_common_reduct.
Proof.
  unfold Transitive. intros s t v [st [? ?]] [tv [? ?]].
  enough (cut : have_common_reduct st tv).
  - unfold have_common_reduct in *.
    destruct cut as [u [? ?]].
    exists u. split; etransitivity; eassumption.
  - unfold have_common_reduct.
    destruct (@confluence_proof t st tv ltac:(auto) ltac:(auto))
      as [u [? ?]]. exists u. tauto.
Qed.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Specification for beta conversion
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following specification theorem for :math:`\beta`-conversion states that two terms are :math:`\beta`-equivalent exactly when they share a common reduct. The non-obvious case of this proof is exactly showing the transitivity of the ``have_common_reduct`` relation. This case is unfolded below to show the proof state before invoking transitivity.

|*)

Theorem beta_conversion_spec : `(have_common_reduct s t <-> s ∼ t).
Proof with intuition eauto with churchrosser.
  intros. split. destruct 1 as [st [? ?]].
  - transitivity st.
    + apply clos_rt_clos_rst.
      fold steps. assumption.
    + symmetry. unfold steps.
      apply clos_rt_clos_rst.
      fold steps. assumption.
  - intros. induction H.
    + (*inclusion of step *)
      exists y. unfold steps...
    + (* reflexivity *)
      exists x. unfold steps...
    + (* symmetry *)
      match goal with
      | H : have_common_reduct x y |- _ => destruct H as [z [? ?]]
      end. exists z. tauto.
    + (* .unfold *)
      etransitivity; eassumption.
Qed.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Uniqueness of normal forms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

Definition beta_normal (t : lam nat) : Prop :=
  not (exists s, t → s).

Definition has_normal_form (t s : lam nat) : Prop :=
  t →* s /\ beta_normal s.

Lemma normal_step_eq :
  `(beta_normal t ->
    t →* s ->
    t = s).
Proof.
  intros t s Hnorm Hstep. induction Hstep.
  - contradiction Hnorm. eauto.
  - reflexivity.
  - fold steps in *. specialize (IHHstep1 Hnorm). subst.
    apply IHHstep2. apply Hnorm.
Qed.

Theorem unf : forall t s1 s2,
    has_normal_form t s1 ->
    has_normal_form t s2 ->
    s1 = s2.
Proof.
  unfold has_normal_form.
  intros ??? [t_step_s1 s1_normal] [t_step_s2 s2_normal].
  destruct (@confluence_proof t s1 s2 t_step_s1 t_step_s2)
    as [s [s1_step_s s2_step_s]].
  assert (s1 = s) by auto using normal_step_eq.
  assert (s2 = s) by auto using normal_step_eq.
  congruence.
Qed.

Lemma step_to_normal_form : forall t s,
    t ∼ s ->
    beta_normal s ->
    t →* s.
Proof.
  intros ?? Heq normal_s.
  rewrite <- beta_conversion_spec in Heq; rename Heq into Hcr.
  destruct Hcr as [u [Htu Hsu]].
  assert (s = u) by auto using normal_step_eq.
  subst.
  assumption.
Qed.

Theorem normal_form_forward : forall t t' s,
    t →* t' ->
    has_normal_form t  s ->
    has_normal_form t' s.
Proof.
  unfold has_normal_form.
  intros ??? t_step_t' [t_step_s s_normal].
  split.
  - apply step_to_normal_form.
    + transitivity t.
      * symmetry.
        eapply clos_rt_clos_rst; fold steps.
        assumption.
      * eapply clos_rt_clos_rst; fold steps.
        assumption.
    + assumption.
  - assumption.
Qed.

Theorem normal_forward_equiv : forall t t',
    t →* t' ->
    t ∼ t'.
Proof.
  intros.
  apply clos_rt_clos_rst.
  assumption.
Qed.

Theorem transfer_normal_form : forall t t' s,
    t ∼ t' ->
    has_normal_form t  s ->
    has_normal_form t' s.
Proof.
  unfold has_normal_form.
  intros ??? t_equiv_t' [t_step_s normal_s].
  split; auto.
  apply step_to_normal_form; auto.
  apply normal_forward_equiv in t_step_s.
  etransitivity; [symmetry|]; eauto.
Qed.
