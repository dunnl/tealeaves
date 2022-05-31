From Tealeaves Require Import
     Functors.List
     LN.Leaf LN.Atom LN.AtomSet LN.AssocList
     LN.Multisorted.Operations.

From Multisorted Require Import
     Classes.DTM.

From Coq Require Import
     Sorting.Permutation.

From Tealeaves.Examples Require Import
     SystemF.Language.

Implicit Types (x : atom).

Import List.ListNotations.
Import LN.AssocList.Notations.

Create HintDb sysf_ctx.

(** * Tactical support *)
(******************************************************************************)
Ltac burst :=
  rewrite_strat
    outermost
    (choice (hints tea_rw_dom)
            (choice (hints tea_rw_range)
                    (choice (hints tea_rw_disj)
                            (choice (hints tea_rw_uniq)
                                    (hints tea_list))))).

Tactic Notation "burst" "in" hyp(H) :=
  rewrite_strat
    outermost
    (choice (hints tea_rw_dom)
            (choice (hints tea_rw_range)
                    (choice (hints tea_rw_disj)
                            (choice (hints tea_rw_uniq)
                                    (hints tea_list))))) in H.

Tactic Notation "bursts" :=
  repeat match goal with
         | H : _ |- _ => burst in H
         end; repeat burst.

(** * Infrastructural lemmas for contexts and well-formedness predicates *)
(******************************************************************************)

(** ** Reasoning principle for scope (<<scoped>>) *)
(******************************************************************************)
Section scope_lemmas.

  Context
    (S : Type -> Type)
    `{DTPreModule (list K) S T (mn_op := Monoid_op_list) (mn_unit := Monoid_unit_list)}
    `{! DTM (list K) T}.

  Theorem perm_scoped : forall (t : S leaf) (X : Type) (γ1 γ2 : alist X) (k : K),
      Permutation γ1 γ2 ->
      scoped S k t (domset γ1) ->
      scoped S k t (domset γ2).
  Proof.
    introv Hperm. unfold scoped. rewrite (perm_domset); eauto.
  Qed.

  Theorem perm_scoped_iff : forall (t : S leaf) (X : Type) (γ1 γ2 : alist X) (k : K),
      Permutation γ1 γ2 ->
      scoped S k t (domset γ1) <->
      scoped S k t (domset γ2).
  Proof.
    intros. assert (Permutation γ2 γ1) by now symmetry.
    split; eauto using perm_scoped.
  Qed.

  Lemma weak_scoped_app_l : forall (t : S leaf) (X : Type) (γ1 γ2 : alist X) (k : K),
      scoped S k t (domset γ1) ->
      scoped S k t (domset (γ1 ++ γ2)).
  Proof.
    intros. unfold scoped in *.
    autorewrite with tea_rw_dom. fsetdec.
  Qed.

  Lemma weak_scoped_app_r : forall (t : S leaf) (X : Type) (γ1 γ2 : alist X) (k : K),
      scoped S k t (domset γ2) ->
      scoped S k t (domset (γ1 ++ γ2)).
  Proof.
    intros. unfold scoped in *.
    autorewrite with tea_rw_dom. fsetdec.
  Qed.

  Lemma strengthen_scoped : forall (t : S leaf) (X : Type) (γ1 γ2 : alist X) (k : K) (x : atom) (x' : X),
      scoped S k t (domset (γ1 ++ x ~ x' ++ γ2)) ->
      ~ x ∈@ (freeset S k t) ->
      scoped S k t (domset (γ1 ++ γ2)).
  Proof.
    introv hyp hnotin. unfold scoped in *.
    autorewrite with tea_rw_dom in *. fsetdec.
  Qed.

  Lemma sub_scoped :
    forall (t1 : S leaf) (k : K) (t2 : T k leaf)
      (X : Type) (γ1 γ2 : alist X) (x : atom) (x' : X),
      scoped S k t1 (domset (γ1 ++ x ~ x' ++ γ2)) ->
      scoped (T k) k t2 (domset (γ1 ++ γ2)) ->
      scoped S k (subst S k x t2 t1) (domset (γ1 ++ γ2)).
  Proof.
    introv hyp1 hyp2. unfold scoped in *. autorewrite with tea_rw_dom in *.
    etransitivity.
    (*
      apply freeset_subst_upper_eq. fsetdec.
     *)
  Abort.

  Lemma sub_scoped_1 :
    forall (t1 : S leaf) (k : K) (t2 : T k leaf)
      (X : Type) (γ1 γ2 : alist X) (x : atom) (x' : X),
      scoped S k t1 (domset (γ1 ++ x ~ x')) ->
      scoped (T k) k t2 (domset γ1) ->
      scoped S k (subst S k x t2 t1) (domset γ1).
  Proof.
    (*
    introv hyp1 hyp2. change_alist (γ ++ x ~ tt ++ []) in hyp1.
    change_alist (γ ++ []) in hyp2.
    change_alist (γ ++ []).
    eauto using sub_scoped.
     *)
  Abort.

End scope_lemmas.

(** ** Contexts of type variables (<<ok_tyv>>) *)
(******************************************************************************)
Lemma perm_ok_tyv : forall Δ1 Δ2,
    ok_tyv Δ1 ->
    Permutation Δ1 Δ2 ->
    ok_tyv Δ2.
Proof.
  unfold ok_tyv. intros. rewrite <- uniq_perm; eauto.
Qed.

#[export] Hint Immediate perm_ok_tyv : sysf_ctx.

Corollary perm_ok_tyv_iff : forall Δ1 Δ2,
    Permutation Δ1 Δ2 ->
    ok_tyv Δ1 <-> ok_tyv Δ2.
Proof.
  unfold ok_tyv. intros. now rewrite uniq_perm.
Qed.

Lemma ok_tyv_nil : forall x,
    ok_tyv [].
Proof.
  intros. unfold ok_tyv in *.
  now bursts.
Qed.

#[export] Hint Resolve ok_tyv_nil : sysf_ctx.

Lemma ok_tyv_one : forall x,
    ok_tyv (x ~ tt).
Proof.
  intros. unfold ok_tyv in *.
  now bursts.
Qed.

#[export] Hint Resolve ok_tyv_one : sysf_ctx.

Lemma ok_tyv_app_iff : forall Δ1 Δ2,
    ok_tyv (Δ1 ++ Δ2) <->
    ok_tyv Δ1 /\ ok_tyv Δ2 /\ disjoint Δ1 Δ2.
Proof.
  intros. unfold ok_tyv in *.
  now bursts.
Qed.

Lemma ok_tyv_app_1 : forall Δ1 Δ2,
    ok_tyv Δ1 /\ ok_tyv Δ2 /\ disjoint Δ1 Δ2 ->
    ok_tyv (Δ1 ++ Δ2).
Proof.
  intros. unfold ok_tyv in *.
  now bursts.
Qed.

#[export] Hint Resolve ok_tyv_app_1 : sysf_ctx.

Lemma ok_tyv_mid_1: forall Δ1 Δ2 Δ3,
    ok_tyv (Δ1 ++ Δ2 ++ Δ3) ->
    ok_tyv Δ2.
Proof.
  intros. unfold ok_tyv in *.
  now bursts.
Qed.

Lemma ok_tyv_mid_2 : forall Δ1 Δ2 Δ3,
    ok_tyv (Δ1 ++ Δ2 ++ Δ3) ->
    ok_tyv (Δ1 ++ Δ3).
Proof.
  intros. unfold ok_tyv in *.
  bursts. now rewrite disjoint_sym.
Qed.

Lemma ok_tyv_app_l : forall Δ1 Δ2,
    ok_tyv (Δ1 ++ Δ2) ->
    ok_tyv Δ1.
Proof.
  intros. unfold ok_tyv in *.
  now bursts.
Qed.

Lemma ok_tyv_app_r : forall Δ1 Δ2,
    ok_tyv (Δ1 ++ Δ2) ->
    ok_tyv Δ2.
Proof.
  intros. unfold ok_tyv in *.
  now bursts.
Qed.

#[export] Hint Immediate ok_tyv_mid_1 ok_tyv_mid_2 : sysf_ctx.
#[export] Hint Immediate ok_tyv_app_l ok_tyv_app_r : sysf_ctx.

(** ** Well-scoped types in context Δ *)
(** A type is well-scoped in a type-variable environment when all of
    its free variables (which are always type variables) are declared
    in the context. Such a type may or may not be locally
    closed. Well-scopedness is preserved under permutation, weakening,
    and strengthening. It also satisfies a substitution lemma. *)
(******************************************************************************)
(*
(** The <<scoped_type>> predicate supports permutation in Δ. *)
Lemma perm_scoped_type : forall Δ1 Δ2 τ,
    Permutation Δ1 Δ2 ->
    scoped_type Δ1 τ <->
    scoped_type Δ2 τ.
Proof.
  intros. unfold scoped_type. apply perm_scoped_iff; auto.
Qed.

(** The <<scoped_type>> predicate supports weakening in Δ. *)
Lemma weak_scoped_type_r : forall Δ1 Δ2 τ,
    scoped_type Δ1 τ ->
    scoped_type (Δ1 ++ Δ2) τ.
Proof.
  intros. unfold scoped_type in *.
  now apply weak_scoped_app_l.
Qed.

Lemma weak_scoped_type_l : forall Δ1 Δ2 τ,
    scoped_type Δ2 τ ->
    scoped_type (Δ1 ++ Δ2) τ.
Proof.
  intros. unfold scoped_type in *.
  now apply weak_scoped_app_r.
Qed.

(** The <<scoped_type>> predicate supports strengthening in Δ for fresh variables. *)
Lemma stren_scoped_type : forall Δ1 Δ2 x τ,
    scoped_type (Δ1 ++ x ~ tt ++ Δ2) τ ->
    ~ x ∈@ (freeset typ KType τ) ->
    scoped_type (Δ1 ++ Δ2) τ.
Proof.
  introv hyp hnotin. unfold scoped_type in *.
  eapply stren_scoped; eauto.
Qed.

Corollary stren_scoped_type_1 : forall Δ x τ,
    scoped_type (Δ ++ x ~ tt) τ ->
    ~ x ∈@ (freeset typ KType τ) ->
    scoped_type Δ τ.
Proof.
  introv H1 H2. change_alist (Δ ++ x ~ tt ++ []) in H1.
  change_alist (Δ ++ []). eauto using stren_scoped_type.
Qed.

(** The <<scoped_type>> predicate supports substitution w.r.t. in Δ. *)
Lemma sub_scoped_type : forall Δ1 Δ2 x τ1 τ2,
    scoped_type (Δ1 ++ x ~ tt ++ Δ2) τ1 ->
    scoped_type (Δ1 ++ Δ2) τ2 ->
    scoped_type (Δ1 ++ Δ2) (subst typ KType x τ2 τ1).
Proof.
  intros. apply sub_scoped; auto.
Qed.

Corollary sub_scoped_type_1 : forall Δ x τ1 τ2,
    scoped_type (Δ ++ x ~ tt) τ1 ->
    scoped_type Δ τ2 ->
    scoped_type Δ (subst typ KType x τ2 τ1).
Proof.
  introv H1 H2. change_alist (Δ ++ x ~ tt ++ []) in H1.
  change_alist (Δ ++ []) in H2. change_alist (Δ ++ []).
  auto using sub_scoped_type.
Qed.

#[export] Hint Resolve weak_scoped_type_l weak_scoped_type_r perm_scoped_type
 stren_scoped_type stren_scoped_type_1 sub_scoped_type sub_scoped_type_1 : tea_sysf.
 *)

(** ** Well-formed type expressions (<<ok_type>>) *)
(******************************************************************************)
Corollary ok_type_lc : forall Δ τ,
    ok_type Δ τ ->
    locally_closed typ KType τ.
Proof.
  unfold ok_type. tauto.
Qed.

#[export] Hint Resolve ok_type_lc : sysf_ctx.

Lemma perm_ok_type : forall Δ1 Δ2 τ,
    Permutation Δ1 Δ2 ->
    ok_type Δ1 τ <->
    ok_type Δ2 τ.
Proof.
  intros. unfold ok_type. rewrite (perm_scoped_iff _ _); eauto.
  reflexivity.
Qed.

Lemma perm_ok_type_1 : forall Δ1 Δ2 τ,
    ok_type Δ1 τ ->
    Permutation Δ1 Δ2 ->
    ok_type Δ2 τ.
Proof.
  intros. rewrite <- perm_ok_type; eauto.
Qed.

#[export] Hint Immediate perm_ok_type_1 : sysf_ctx.

(** The <<ok_type>> predicate supports weakening in Δ. *)
(* TODO: Understand how to prevent
    auto using weak_scoped_app_l diverges. *)
Lemma weak_ok_type_r : forall Δ1 Δ2 τ,
    ok_type Δ1 τ ->
    ok_type (Δ1 ++ Δ2) τ.
Proof.
  unfold ok_type.
  intros. split.
  - Check weak_scoped_app_l typ.
    apply (weak_scoped_app_l typ).
  - tauto.
  intuition (eauto using (weak_scoped_app_l typ)).
Qed.

Lemma weak_ok_type_l : forall Δ1 Δ2 τ,
    ok_type Δ2 τ ->
    ok_type (Δ1 ++ Δ2) τ.
Proof.
  unfold ok_type. intuition (auto using (weak_scoped_app_r (F:=typ))).
Qed.

#[export] Hint Resolve weak_ok_type_l weak_ok_type_r : sysf_ctx.

(** The <<ok_type>> predicate supports strengthening in Δ for fresh variables. *)
Lemma stren_ok_type : forall Δ1 Δ2 x τ,
    ok_type (Δ1 ++ x ~ tt ++ Δ2) τ ->
    ~ x ∈@ (freeset typ KType τ) ->
    ok_type (Δ1 ++ Δ2) τ.
Proof.
  introv [? ?] ?. unfold ok_type.
  eauto using (stren_scoped (F:=typ)).
Qed.

Corollary stren_ok_type_1 : forall Δ x τ,
    ok_type (Δ ++ x ~ tt) τ ->
    ~ x ∈@ (freeset typ KType τ) ->
    ok_type Δ τ.
Proof.
  introv H1 H2. change_alist (Δ ++ x ~ tt ++ []) in H1.
  change_alist (Δ ++ []). eauto using stren_ok_type.
Qed.

#[export] Hint Immediate stren_ok_type stren_ok_type_1 : sysf_ctx.

(** The <<ok_type>> predicate supports substitution w.r.t. in Δ. *)
Lemma sub_ok_type : forall Δ1 Δ2 x τ1 τ2,
    ok_type (Δ1 ++ x ~ tt ++ Δ2) τ1 ->
    ok_type (Δ1 ++ Δ2) τ2 ->
    ok_type (Δ1 ++ Δ2) (subst typ KType x τ2 τ1).
Proof.
  unfold ok_type. introv [? ?] [? ?]. split.
  - auto using (sub_scoped (F:=typ)).
  - auto using (subst_lc_eq (F:=typ)).
Qed.

#[export] Hint Resolve sub_ok_type : sysf_ctx.

Corollary sub_ok_type_1 : forall Δ x τ1 τ2,
    ok_type (Δ ++ x ~ tt) τ1 ->
    ok_type Δ τ2 ->
    ok_type Δ (subst typ KType x τ2 τ1).
Proof.
  introv H1 H2. change_alist (Δ ++ x ~ tt ++ []) in H1.
  change_alist (Δ ++ []) in H2. change_alist (Δ ++ []).
  auto using sub_ok_type.
Qed.

#[export] Hint Resolve sub_ok_type_1 : sysf_ctx.

(** * Term variable contexts *)
(** Contexts of <<free term variable, type>> assigments), used to declare free term
    variables and their associated typee. *)
(******************************************************************************)

(** A term-variable context <<Γ>> is well formed in type-variable
    context <<Δ>> when it is duplicate-free and each type is well
    formed in <<Δ>>. The [ok_tmv] judgment is preserved under
    permutation of <<Γ>>, and preserved under permutation, weakening,
    strengthening, and substitution in <<Δ>>.*)

(** ** Structural properties of <<Δ>> in <<ok_tmv Δ Γ>>. *)
Corollary binds_ok_tmv : forall Δ Γ x τ,
    ok_tmv Δ Γ ->
    (x, τ) ∈ Γ ->
    ok_type Δ τ.
Proof.
  introv ? Hin. unfold ok_tmv, ok_type in *.
  apply binds_in_range in Hin. firstorder.
Qed.

#[export] Hint Immediate binds_ok_tmv : sysf_ctx.

(** The <<ok_tmv>> predicate supports permutation in Δ. *)
Theorem perm_ok_tmv : forall Δ1 Δ2 Γ,
    ok_tmv Δ1 Γ ->
    Permutation Δ1 Δ2 ->
    ok_tmv Δ2 Γ.
Proof.
  introv [? ?] ?. unfold ok_tmv.
  split; eauto using perm_ok_type_1 with tea_alist.
Qed.

#[export] Hint Immediate perm_ok_tmv : sysf_ctx.

Corollary perm_ok_tmv_iff : forall Δ1 Δ2 Γ,
    Permutation Δ1 Δ2 ->
    ok_tmv Δ1 Γ <-> ok_tmv Δ2 Γ.
Proof.
  introv Hperm. unfold ok_tmv, ok_type.
  assert (lemma : forall τ, scoped_env typ KType τ Δ1 <->
                            scoped_env typ KType τ Δ2).
  { intros. now rewrite perm_scoped_iff. }
  (* todo : figure out why <<perm_scoped_iff>> won't rewrite by itself. *)
  setoid_rewrite lemma. firstorder.
Qed.

(** The <<ok_tmv>> predicate supports weakening in <<Δ>>. *)

#[local] Set Firstorder Depth 4.

Lemma weak_ok_tmv : forall Δ1 Δ2 Γ,
    ok_tmv Δ1 Γ ->
    ok_tmv (Δ1 ++ Δ2) Γ.
Proof.
  introv [huniq hok1]. unfold ok_tmv in *.
  firstorder using weak_ok_type_r.
Qed.

#[export] Hint Resolve weak_ok_tmv : sysf_ctx.

(** The <<ok_tmv>> predicate supports strengthening in <<Δ>> for fresh variables. *)
Lemma stren_ok_tmv : forall Δ1 Δ2 x Γ,
    ok_tmv (Δ1 ++ x ~ tt ++ Δ2) Γ ->
    ~ x ∈@ freeset (fun A => alist typ A) KType Γ ->
    ok_tmv (Δ1 ++ Δ2) Γ.
Proof.
  introv [hunit hok] hfresh. rewrite nin_freeset_iff in hfresh.
  unfold ok_tmv. split; [trivial |].
  intros τ hin; specialize (hok τ hin).
  intuition (eauto using stren_ok_type).
Qed.

Corollary stren_ok_tmv_1 : forall Δ x Γ,
    ok_tmv (Δ ++ x ~ tt) Γ ->
    ~ x ∈@ freeset (fun A => alist typ A) KType Γ ->
    ok_tmv Δ Γ.
Proof.
  introv hyp1 hyp2. change_alist (Δ ++ x ~ tt ++ []) in hyp1.
  change_alist (Δ ++ []). eauto using stren_ok_tmv.
Qed.

(** The <<ok_tmv>> predicate supports substitution w.r.t. <<Δ>> *)
Lemma sub_ok_tmv : forall Δ1 Δ2 x Γ τ,
    ok_tmv (Δ1 ++ x ~ tt ++ Δ2) Γ ->
    ok_type (Δ1 ++ Δ2) τ ->
    locally_closed typ KType τ ->
    ok_tmv (Δ1 ++ Δ2) (subst (fun A => alist typ A) KType x τ Γ).
Proof.
  introv [hunit hok] Hscope lc. unfold ok_tmv. split.
  - now rewrite <- uniq_subst.
  - intros τ2 τ2in. rewrite in_range_subst in τ2in.
    destruct τ2in as [τ2_inv [hin ?]]; subst.
    specialize (hok τ2_inv hin).
    auto using sub_ok_type.
Qed.

#[export] Hint Resolve sub_ok_tmv : sysf_ctx.

(** ** Structural properties of <<Γ>> in <<ok_tmv Δ Γ>>. *)

(** <<ok_tmv Δ Γ>> supports permutation in Γ. *)
Lemma perm_tm_ok_tmv : forall Δ Γ1 Γ2,
    ok_tmv Δ Γ1 ->
    Permutation Γ1 Γ2 ->
    ok_tmv Δ Γ2.
Proof.
  introv [huniq hok]. unfold ok_tmv in *. split.
  - rewrite uniq_perm; eauto. now symmetry.
  - intros τ hin; specialize (hok τ).
    apply hok. rewrite perm_range; eauto.
Qed.

#[export] Hint Immediate perm_tm_ok_tmv : sysf_ctx.

Corollary perm_tm_ok_tmv_iff : forall Δ Γ1 Γ2,
    Permutation Γ1 Γ2 ->
    ok_tmv Δ Γ1 <-> ok_tmv Δ Γ2.
Proof.
  introv Hperm; split; intro.
  - eauto using perm_tm_ok_tmv.
  - symmetry in Hperm. eauto using perm_tm_ok_tmv.
Qed.

Lemma ok_tmv_tm_nil : forall Δ,
    ok_tmv Δ [].
Proof.
  intros. unfold ok_tmv in *. now bursts.
Qed.

#[export] Hint Resolve ok_tmv_tm_nil : sysf_ctx.

Lemma ok_tmv_tm_cons : forall Δ Γ x τ,
    ok_tmv Δ Γ ->
    ~ (x ∈@ domset Γ) ->
    ok_type Δ τ ->
    ok_tmv Δ (x ~ τ ++ Γ).
Proof.
  intros. unfold ok_tmv in *. bursts.
  splits.
  - intuition.
  - intros ? [?|?].
    + subst. auto.
    + firstorder.
Qed.

#[export] Hint Resolve ok_tmv_tm_cons : sysf_ctx.

Lemma ok_tmv_tm_one : forall Δ x τ,
    ok_type Δ τ ->
    ok_tmv Δ (x ~ τ).
Proof.
  intros. change (x ~ τ) with [(x, τ)].
  apply ok_tmv_tm_cons; auto using ok_tmv_tm_nil.
  fsetdec.
Qed.

#[export] Hint Resolve ok_tmv_tm_one : sysf_ctx.

Lemma ok_tmv_tm_app : forall Δ Γ1 Γ2,
    ok_tmv Δ (Γ1 ++ Γ2) <->
    ok_tmv Δ Γ1 /\ ok_tmv Δ Γ2 /\ disjoint Γ1 Γ2.
Proof.
  intros. unfold ok_tmv.
  setoid_rewrite in_range_iff.
  setoid_rewrite List.in_list_app.
  rewrite uniq_app_iff. firstorder.
Qed.

Lemma ok_tmv_inv_app_l : forall Δ Γ1 Γ2,
    ok_tmv Δ (Γ1 ++ Γ2) ->
    ok_tmv Δ Γ1.
Proof.
  introv [huniq hscope]. unfold ok_tmv in *.
  bursts. firstorder.
Qed.

#[export] Hint Immediate ok_tmv_inv_app_l : sysf_ctx.

Lemma ok_tmv_app_comm : forall {Δ Γ1 Γ2},
    ok_tmv Δ (Γ1 ++ Γ2) <->
    ok_tmv Δ (Γ2 ++ Γ1).
Proof.
  intros. unfold ok_tmv. bursts.
  rewrite disjoint_sym. firstorder.
Qed.

#[export] Hint Immediate ok_tmv_app_comm : sysf_ctx.

Corollary ok_tmv_inv_app_r : forall Δ Γ1 Γ2,
    ok_tmv Δ (Γ1 ++ Γ2) ->
    ok_tmv Δ Γ2.
Proof.
  introv hyp. rewrite ok_tmv_app_comm in hyp.
  eauto using ok_tmv_inv_app_l.
Qed.

#[export] Hint Immediate ok_tmv_inv_app_r : sysf_ctx.

Corollary ok_tmv_inv_mid : forall Δ Γ1 Γ2 Γ3,
    ok_tmv Δ (Γ1 ++ Γ2 ++ Γ3) ->
    ok_tmv Δ (Γ1 ++ Γ3).
Proof.
  introv hyp.
  change_alist ((Γ1 ++ Γ2) ++ Γ3) in hyp.
  rewrite ok_tmv_app_comm in hyp.
  change_alist ((Γ3 ++ Γ1) ++ Γ2) in hyp.
  apply ok_tmv_inv_app_l in hyp.
  now rewrite ok_tmv_app_comm in hyp.
Qed.

#[export] Hint Immediate ok_tmv_inv_mid : sysf_ctx.

(** * Well-formed terms, <<Δ ; Γ ⊢ t OK>> *)

(** ** Structural properties of <<Δ>> in <<Δ ; Γ ⊢ t OK>>. *)

(** ** Structural properties of <<Γ>> in <<Δ ; Γ ⊢ t : τ>>. *)
