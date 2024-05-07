From Coq Require Import
  Relations.Relations
  Classes.RelationClasses.
From Tealeaves Require Import
  Prelude.
From Autosubst Require Import
  Autosubst.

#[local] Set Implicit Arguments.

Inductive lam : Type :=
| tvar (x : var)
| abs (s : {bind lam})
| app (s t : lam).

#[export] Instance Ids_term : Ids lam. derive. Defined.
#[export] Instance Rename_lam : Rename lam. derive. Defined.
#[export] Instance Subst_lam : Subst lam. derive. Defined.

Check ids : var -> lam.
Check rename : (var -> var) -> lam -> lam.
Check subst : (var -> lam) -> lam -> lam.

#[export] Instance SubstLemmas_term : SubstLemmas lam. derive. Qed.

Implicit Types (s t u v : lam) (x y : nat)
  (σ τ : nat -> lam) (ρ : nat -> nat).

Generalizable Variables s t u v x y σ τ ρ.

Create HintDb churchrosser.

Declare Custom Entry lambda.

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

(*
Module Notations.
  Notation "'λ'" := (lam) (at level 45).
  Notation "⟨ t ⟩ ( u )" := (app t u) (at level 80, t at level 40, u at level 40).
End Notations.
 *)

Import Notations.

(*|
++++++++++++++++++++++
Beta reduction
++++++++++++++++++++++

Beta reduction and derived relations.
|*)

(* One step of beta reduction *)
Inductive step : lam -> lam -> Prop :=
| step_beta : forall tbody targ, step (app (abs tbody) targ) (subst (targ .: ids) tbody)
| step_app_l : forall u1 u2 t, step u1 u2 -> step (app u1 t) (app u2 t)
| step_app_r : forall u t1 t2, step t1 t2 -> step (app u t1) (app u t2)
| step_lam : forall u1 u2, step u1 u2 -> step (abs u1) (abs u2).

Print relation.

Check step : relation lam.

Notation "s → t" := (step s t) (at level 50).

#[export] Hint Constructors step : churchrosser.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The multi-step reduction relation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Beta reduction and derived relations.
|*)

Definition steps : relation lam := clos_refl_trans _ step.

(*|
The first thing we do after defining ``steps`` is prove the relation is indeed reflexive and transitive, registering ``pars`` as an instance as the ``Reflexive`` and ``Transitive`` typeclasses. Providing these instances allows us to use the ``reflexivity`` and ``transitivity`` tactics when proving goals of the form ``pars t1 t2``. For whatever reason, the standard library module that defines the closure operator ``clos_refl_trans`` does not provide these typeclass instances for us, which is why we have to do it ourselves. I don't think there's a fundamental reason the standard library *couldn't* provide these instances for any relation defined with ``clos_refl_trans``, but it happens not to. [#f1]_
|*)

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

(*|
Something you may find slightly surprising is that it is not immediately obvious (at least to Coq) that we have multi-step versions of the left and right reduction rules for ``App`` and the rule for ``Lam``. We prove these below. The first proof we make very explicit, while the other two are automated. We add these "derived constructors" to our hint database.
|*)

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

(*|
**Aside**: You could give an inductive definition of ``steps``, similar to that for ``step``, such that these "derived" constructors would be actual constructors. In that case, the tedious detail would be to verify that ``steps`` really is the reflexive transitive closure of ``step``. We'll see an example later of the two different styles in the context of beta equivalence.
|*)

(*|
+++++++++++++++++++++++++++++++
Confluence properties
+++++++++++++++++++++++++++++++
|*)

Section rel_properties.

  Context
    (R1 R2 : relation lam).

  Definition GDiamond := forall t t1 t2,
      R1 t t1 ->
      R1 t t2 ->
      exists t3, R2 t1 t3 /\ R2 t2 t3.

  Definition Diamond := forall t t1 t2,
      R1 t t1 ->
      R1 t t2 ->
      exists t3, R1 t1 t3 /\ R1 t2 t3.

End rel_properties.

(*|
Inside the ``Section``, ``R1`` and ``R2`` are variables that can be referred to. When the section is closed,
``GDiamond`` and ``Diamond`` are generalized so that ``R1`` and ``R2`` become *arguments* to the definitions. (Except that ``R2`` does not become an argument to ``Diamond``, since its definition doesn't mention ``R2``.)
|*)

Definition local_confluence : Prop := GDiamond step steps.

Definition confluence : Prop := Diamond steps.

#[export] Hint Unfold confluence local_confluence Diamond GDiamond : core.

Lemma local_confluence_proof : local_confluence.
Proof.
  autounfold.
  introv Hstep1.
  induction Hstep1; introv Hstep2.
  - exists (subst (targ .: ids) tbody).
    split. reflexivity.
Abort.

Lemma local_confluence_proof : local_confluence.
Proof with (intuition auto with churchrosser).
  autounfold. induction t.
  - intros t1 t2 H1 H2.
    inversion H1.
  - intros s1 s2 H1 H2.
    inversion H1;
      inversion H2;
      subst.
    + destruct (IHt u2 u3 ltac:(auto) ltac:(auto)).
      exists ({|\, x|})...
Abort.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~
Parallel reduction
~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

Reserved Notation "t1 ⇒ t2" (at level 50).

(* One step of parallel beta reduction *)
Inductive par : lam -> lam -> Prop :=
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
    {| (\, s1) t1 |} ⇒ subst (t2 .: ids) s2)
where "t1 ⇒ t2" := (par t1 t2).

#[export] Instance: Reflexive par.
Proof.
  intro t. induction t; auto using par.
Qed.

Definition pars : relation lam := clos_refl_trans _ par.

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

(*|
The same proofs, automated
------------------------------

Here is how I would ordinarily write these proofs (sometimes after writing proofs like the ones shown above and abstracting out the common patterns).

|*)

Goal `(t1 → t2 -> t1 ⇒ t2).
Proof.
  induction 1; now constructor.
Qed.

#[export] Hint Resolve step_in_par : churchrosser.

Goal `(t1 ⇒ t2 -> t1 →* t2).
Proof with (info_eauto with churchrosser).
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

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Substitutivity principles for ``par``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

Notation "σ1 ▷ σ2" := (forall x, σ1 x ⇒ σ2 x) (at level 50).

Lemma par_sub : `(t ⇒ t' -> s ⇒ s' ->
                  subst (s .: ids) t ⇒ subst (s' .: ids) t').
Proof.
  induction 1; intros.
  - asimpl.
    now destruct x.
  - asimpl.
    apply par_app; auto.
  - asimpl.
    apply par_abs.
    admit.
  - asimpl.
Abort.

Lemma step_subst s t :
  s ⇒ t -> forall σ, subst σ s ⇒ subst σ t.
Proof with auto using par.
  induction 1; intros.
  - asimpl.
    reflexivity.
  - asimpl.
    auto using par.
  - asimpl.
    apply par_abs.
    auto.
  - asimpl.
    replace (s2.[t2.[σ] .: σ]) with (s2.[up σ].[t2.[σ]/]) by now asimpl.
    + apply par_beta.
      auto. auto.
Qed.

Lemma par_strong_rename : `(t1 ⇒ t2 -> rename ρ t1 ⇒ rename ρ t2).
Proof with auto with churchrosser.
  intros. generalize dependent ρ.
  induction H; intros.
  - reflexivity.
  - asimpl.
    specialize (IHpar1 ρ).
    specialize (IHpar2 ρ).
    asimpl in *.
    auto using par.
  - autorewrite with autosubst.
    cbn.
    autosubst_unfold.
    cbn.
    unfold _bind, ren, scomp, hcomp.
    fsimpl.
          autosubst_unfold_up;
          autorewrite with autosubst;
    asimpl.
    autosubst_unfold.
    Set Printing All.
    reassociate <- near (subst (ret ∘ lift 1)).
    simplify_db.
    specialize (IHpar (up__ren ρ)).
    unfold up__ren in *.
    normalize_rename_to_subst_in_all.
    unfold compose in IHpar.
    apply par_abs.
    simplify_db.
    admit.
  - simplify_db.
    rewrite (@rename_to_subst) in IHpar1.
    specialize
      (par_beta
         (rename (up__ren ρ) s1)
         (rename (up__ren ρ) s2)
         (rename ρ t1)
         (rename ρ t2)
         ltac:(auto) ltac:(auto)).
    asimpl. trivial.
Qed.

Lemma par_subst_up : forall σ1 σ2, σ1 ▷ σ2 -> ⇑ σ1 ▷ ⇑ σ2.
Proof.
  intros. induction x.
  - reflexivity.
  - enough (rename (+1) (σ1 x) ⇒ rename (+1) (σ2 x)).
    asimpl in *. assumption.
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
  - cbn...
  - cbn...
  - cbn. apply par_lam.
    apply IHHstep. now apply par_subst_up.
  - asimpl.
    replace (s2.[t2.[σ2] .: σ2]) with (s2.[up σ2].[t2.[σ2]/]) by autosubst...
    apply par_beta.
    apply IHHstep1. now apply par_subst_up.
    apply IHHstep2. assumption.
Qed.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Normalization for ``par``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

Fixpoint normalize (t : term) : term :=
  match t with
  | tvar x => tvar x
  | abs s => abs (normalize s)
  | App (Lam t1) t2 => (normalize t1).[normalize t2/]
  | App t1 t2 => App (normalize t1) (normalize t2)
  end.

Lemma par_triangle : forall (t1 t2 : term), t1 ⇒ t2 -> t2 ⇒ normalize t1.
Proof.
  intros. generalize dependent t2. induction 1.
  - reflexivity.
  - cbn. destruct s1.
    + auto using par_app.
    + auto using par_app.
    + inversion H. subst.
      inversion IHpar1. subst.
      auto using par_beta.
  - cbn. auto using par_lam.
  - cbn. apply par_strong_subst; auto.
    intros x. destruct x.
    + asimpl. assumption.
    + asimpl. reflexivity.
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
    destruct (par_diamond t t1 t2 H1 H) as [t3 [? ?]].
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
    destruct (strip_lemma t t1 t2 H Ht2) as [t3 [? ?]].
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
  destruct (pars_diamond t t1 t2 ltac:(auto) ltac:(auto))
    as [t3 [? ?]]. exists t3; split; now apply pars_in_steps.
Qed.

(*|
+++++++++++++++++++++
Beta equivalence
+++++++++++++++++++++

There are a couple ways to define the notion of :math:`\beta`-equivalence (a/k/a :math:`\beta`-conversion or :math:`\beta`-congruence). Just as ``steps`` was defined as the reflexive transitive closure of ``step``, ``beta_equiv`` can be defined as the reflexive *symmetric* transitive closure of ``step``, i.e. the smallest equivalence relation that contains ``step``.

As with ``steps``, the first thing we do after defining ``beta_equiv`` is prove that it is indeed reflexive, symmetric, and transitive, enabling the use of the correspondingly named tactics. We also give this relation a custom notation and add its constructors to our hint database.
|*)
Definition beta_equiv : relation term := clos_refl_sym_trans _ step.

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
Beta equivalence is also called a *congruence* relation, meaning an equivalence relation that is respected by a set of operations, in this case the constructors of ``term``. By "respected by the constructors of ``term``" I mean exactly the following three properties, much like ones we gave earlier for ``steps``.
|*)

Lemma beta_equiv_app_l : forall s1 s2 t, s1 ∼ s2 -> (App s1 t) ∼ (App s2 t).
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
~~~~~~~~~~~~~~~~~~~~~~~
Example: Fixed points
~~~~~~~~~~~~~~~~~~~~~~~
|*)
From Coq Require Import Setoid.

Definition tvar_nat : nat -> term := tvar.
Coercion tvar_nat : nat >-> term.
Check 0 : term.
Compute 0 : term.

Add Parametric Relation : term beta_equiv as help.

Theorem fixed_points : forall t, exists s, {| t s |} ∼ s.
Proof.
  intros. exists (let W := {|\,t (0 0)|} in {|W W|}).
  cbn zeta. symmetry.
Abort.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Axiomatization of beta equivalence
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Instead of defining :math:`\beta`-equivalence as the equivalence closure of ``step``, another route is to define the relation inductively from a set of equational axioms, as shown below with ``beta_equiv_I``.
|*)

Reserved Notation "s ≃ t" (at level 50).

Inductive beta_equiv_I : term -> term -> Prop :=
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

Definition have_common_reduct : term -> term -> Prop :=
  fun s t => exists u, s →* u /\ t →* u.

#[export] Instance: Transitive have_common_reduct.
Proof.
  unfold Transitive. intros s t v [st [? ?]] [tv [? ?]].
  enough (cut : have_common_reduct st tv).
  - unfold have_common_reduct in *.
    destruct cut as [u [? ?]].
    exists u. split; etransitivity; eassumption.
  - unfold have_common_reduct.
    destruct (confluence_proof t st tv ltac:(auto) ltac:(auto))
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

Definition beta_normal (t : term) : Prop :=
  not (exists s, t → s).

Definition has_normal_form (t s : term) : Prop :=
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
  destruct (confluence_proof t s1 s2 t_step_s1 t_step_s2)
    as [s [s1_step_s s2_step_s]].
  assert (s1 = s) by auto using normal_step_eq.
  assert (s2 = s) by auto using normal_step_eq.
  congruence.
Qed.

(*|
 We proved that ``t ∼ s`` is equivalent to ``t`` and ``s`` sharing a common reduct. Generally, this does not imply ``t →* s`` or ``s →* t``. However, when ``s`` is normal (hence it cannot be reduced at all), then we must have ``t →* s``. That is, if ``t`` has a
|*)

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
(*|
Given ``t →* t'``, if ``t'`` has normal form ``s`` then so does ``t`` by transitivity of ``steps``. The converse does not need to hold in general, but we can prove it for the lambda calculus by confluence.
|*)

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

Theorem transfer_normal_form : forall t t' s,
    t ∼ t' ->
    has_normal_form t  s ->
    has_normal_form t' s.
Proof.
  unfold has_normal_form.
  intros ??? t_equiv_t' [t_step_s normal_s].
  split.
  -

  destruct (confluence_proof t s1 s2 t_step_s1 t_step_s2)
    as [s [s1_step_s s2_step_s]].
  assert (s1 = s) by auto using normal_step_eq.
  assert (s2 = s) by auto using normal_step_eq.
  congruence.
Qed.

(*|
It is especially desirable in the context of typed lambda calculi that are strongly normalizing, such as Coq's underlying type theory, but pure untyped lambda calculus is not even weakly normalizing.

|*)

(*|

+++++++++++++++++
Conclusion
+++++++++++++++++

The common modern proof (as opposed to the original proof by Church and Rosser) is due essentially to a paper (CITE), with a number of improvements.

.. rubric:: Footnotes

.. [#f1] One reason these instances might not be included in the standard library is that *using* them would require Coq's typeclass resolution mechanism to unfold the definition of ``pars`` to see that it was defined with ``clos_refl_trans.`` Generally one does *not* want resolution to unfold most definitions automatically when trying to infer a typeclass instance, probably mostly for reasons of efficiency.
|*)
