From Tealeaves Require Import
     Functors.List
     LN.Leaf LN.Atom LN.AtomSet LN.AssocList
     LN.Multisorted.Operations
     LN.Multisorted.Theory.

From Multisorted Require Import
     Classes.DTM.

From Coq Require Import
     Sorting.Permutation.

From Tealeaves.Examples Require Import
     SystemF.Language
     SystemF.Rewriting.

Implicit Types (x : atom).

Import SetlikeFunctor.Notations.
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

(** * Structural lemmas for <<scoped>> *)
(** These lemmas are actually independent of System F. They could be
    incorporated into the locally nameless backend. *)
(******************************************************************************)
Section scope_lemmas.

  Context
    (S : Type -> Type)
    `{DTPreModule (list K) S T (mn_op := Monoid_op_list) (mn_unit := Monoid_unit_list)}
    `{! DTM (list K) T}.

  (** *** Permutation *)
  (******************************************************************************)
  Lemma scoped_perm : forall (k : K) (t : S leaf) (X : Type) (γ1 γ2 : alist X),
      Permutation γ1 γ2 ->
      scoped S k t (domset γ1) ->
      scoped S k t (domset γ2).
  Proof.
    introv Hperm. unfold scoped. rewrite (perm_domset); eauto.
  Qed.

  Theorem scoped_perm_iff : forall (k : K) (t : S leaf) (X : Type) (γ1 γ2 : alist X),
      Permutation γ1 γ2 ->
      scoped S k t (domset γ1) <->
      scoped S k t (domset γ2).
  Proof.
    intros. assert (Permutation γ2 γ1) by now symmetry.
    split; eauto using scoped_perm.
  Qed.

  Corollary scoped_perm_comm : forall (k : K) (t : S leaf) (X : Type) (γ1 γ2 : alist X),
      scoped S k t (domset (γ1 ++ γ2)) <->
      scoped S k t (domset (γ2 ++ γ1)).
  Proof.
    intros. apply scoped_perm_iff. apply Permutation_app_comm.
  Qed.

  (** *** Weakening *)
  (******************************************************************************)
  Lemma scoped_weak_l : forall (k : K) (t : S leaf) (X : Type) (γ1 γ2 : alist X),
      scoped S k t (domset γ1) ->
      scoped S k t (domset (γ1 ++ γ2)).
  Proof.
    intros. unfold scoped in *.
    autorewrite with tea_rw_dom. fsetdec.
  Qed.

  Lemma scoped_weak_mid : forall (k : K) (t : S leaf) (X : Type) (γ1 γ2 γ : alist X),
      scoped S k t (domset (γ1 ++ γ2)) ->
      scoped S k t (domset (γ1 ++ γ ++ γ2)).
  Proof.
    intros. unfold scoped in *.
    autorewrite with tea_rw_dom in *. fsetdec.
  Qed.

  Lemma scoped_weak_r : forall (k : K) (t : S leaf) (X : Type) (γ1 γ2 : alist X),
      scoped S k t (domset γ2) ->
      scoped S k t (domset (γ1 ++ γ2)).
  Proof.
    intros. unfold scoped in *.
    autorewrite with tea_rw_dom. fsetdec.
  Qed.

  (** *** Strengthening *)
  (******************************************************************************)
  Lemma scoped_stren_mid : forall (k : K) (t : S leaf) (X : Type) (γ1 γ2 : alist X) (x : atom) (x' : X),
      scoped S k t (domset (γ1 ++ x ~ x' ++ γ2)) ->
      ~ x ∈@ (freeset S k t) ->
      scoped S k t (domset (γ1 ++ γ2)).
  Proof.
    introv hyp hnotin. unfold scoped in *.
    autorewrite with tea_rw_dom in *. fsetdec.
  Qed.

  Corollary scoped_stren_l : forall (k : K) (t : S leaf) (X : Type) (γ : alist X) (x : atom) (x' : X),
      scoped S k t (domset (x ~ x' ++ γ)) ->
      ~ x ∈@ (freeset S k t) ->
      scoped S k t (domset γ).
  Proof.
    introv Hscope Hnotin. change γ with (nil ++ γ).
    eapply scoped_stren_mid; [apply Hscope | apply Hnotin].
  Qed.

  Corollary scoped_stren_r : forall (k : K) (t : S leaf) (X : Type) (γ : alist X) (x : atom) (x' : X),
      scoped S k t (domset (γ ++ x ~ x')) ->
      ~ x ∈@ (freeset S k t) ->
      scoped S k t (domset γ).
  Proof.
    introv Hscope Hnotin. replace γ with (γ ++ nil) by (now List.simpl_list).
    eapply scoped_stren_mid; [apply Hscope | apply Hnotin].
  Qed.

  (** *** Substitution *)
  (******************************************************************************)
  Lemma scoped_sub_eq_mid :
    forall (k : K) (t1 : S leaf) (t2 : T k leaf)
      (X : Type) (γ1 γ2 : alist X) (x : atom) (x' : X),
      scoped S k t1 (domset (γ1 ++ x ~ x' ++ γ2)) ->
      scoped (T k) k t2 (domset (γ1 ++ γ2)) ->
      scoped S k (subst S k x t2 t1) (domset (γ1 ++ γ2)).
  Proof.
    introv hyp1 hyp2. unfold scoped in *. autorewrite with tea_rw_dom in *.
    etransitivity. apply (freeset_subst_upper_eq S). fsetdec.
  Qed.

  Corollary scoped_sub_eq_r :
    forall (k : K) (t1 : S leaf) (t2 : T k leaf)
      (X : Type) (γ1 : alist X) (x : atom) (x' : X),
      scoped S k t1 (domset (γ1 ++ x ~ x')) ->
      scoped (T k) k t2 (domset γ1) ->
      scoped S k (subst S k x t2 t1) (domset γ1).
  Proof.
    introv hyp1 hyp2. change_alist (γ1 ++ x ~ x' ++ []) in hyp1.
    change_alist (γ1 ++ []) in hyp2.
    change_alist (γ1 ++ []).
    eapply scoped_sub_eq_mid; eauto.
  Qed.

  Corollary scoped_sub_eq_l :
    forall (k : K) (t1 : S leaf) (t2 : T k leaf)
      (X : Type) (γ1 : alist X) (x : atom) (x' : X),
      scoped S k t1 (domset (x ~ x' ++ γ1)) ->
      scoped (T k) k t2 (domset γ1) ->
      scoped S k (subst S k x t2 t1) (domset γ1).
  Proof.
    introv hyp1 hyp2. change_alist ([] ++ x ~ x' ++ γ1) in hyp1.
    change_alist ([] ++ γ1) in hyp2.
    change_alist ([] ++ γ1).
    eapply scoped_sub_eq_mid; eauto.
  Qed.

  Lemma scoped_sub_neq :
    forall (k1 k2 : K) (neq : k1 <> k2) (t1 : S leaf) (t2 : T k2 leaf)
      (X : Type) (γ : alist X) (x : atom),
      scoped S k1 t1 (domset γ) ->
      scoped (T k2) k1 t2 (domset γ) ->
      scoped S k1 (subst S k2 x t2 t1) (domset γ).
  Proof.
    introv hyp1 hyp2. unfold scoped in *. autorewrite with tea_rw_dom in *.
    etransitivity. apply (freeset_subst_upper_neq S); auto. fsetdec.
  Qed.

  (** *** Other *)
  (******************************************************************************)
  Lemma scoped_envmap :
    forall (k : K) (t1 : S leaf) (X Y : Type) (γ1 : alist X) (f : X -> Y),
      scoped S k t1 (domset γ1) ->
      scoped S k t1 (domset (envmap f γ1)).
  Proof.
    introv Hscope. unfold scoped in *.
    now rewrite domset_fmap.
  Qed.

End scope_lemmas.

(** * Infrastructural lemmas for contexts and well-formedness predicates *)
(******************************************************************************)

(** ** General properties of <<ok_kind_ctx>> *)
(******************************************************************************)
Lemma ok_kind_ctx_nil : forall x,
    ok_kind_ctx [].
Proof.
  intros. unfold ok_kind_ctx in *.
  now bursts.
Qed.

Lemma ok_kind_ctx_one : forall x,
    ok_kind_ctx (x ~ tt).
Proof.
  intros. unfold ok_kind_ctx in *.
  now bursts.
Qed.

Lemma ok_kind_ctx_app : forall Δ1 Δ2,
    ok_kind_ctx (Δ1 ++ Δ2) <->
    ok_kind_ctx Δ1 /\ ok_kind_ctx Δ2 /\ disjoint Δ1 Δ2.
Proof.
  intros. unfold ok_kind_ctx in *.
  now bursts.
Qed.

Lemma ok_kind_ctx_comm : forall Δ1 Δ2,
    ok_kind_ctx (Δ1 ++ Δ2) <->
    ok_kind_ctx (Δ1 ++ Δ2).
Proof.
  intros. unfold ok_kind_ctx. bursts.
  rewrite disjoint_sym. firstorder.
Qed.

Lemma ok_kind_ctx_perm1 : forall Δ1 Δ2,
    ok_kind_ctx Δ1 ->
    Permutation Δ1 Δ2 ->
    ok_kind_ctx Δ2.
Proof.
  unfold ok_kind_ctx. intros. rewrite <- uniq_perm; eauto.
Qed.

Corollary ok_kind_ctx_perm : forall Δ1 Δ2,
    Permutation Δ1 Δ2 ->
    ok_kind_ctx Δ1 <-> ok_kind_ctx Δ2.
Proof.
  unfold ok_kind_ctx. intros. now rewrite uniq_perm.
Qed.

#[export] Hint Resolve ok_kind_ctx_nil : sysf_ctx.
#[export] Hint Resolve ok_kind_ctx_one : sysf_ctx.
#[export] Hint Immediate ok_kind_ctx_perm1 : sysf_ctx.

(** ** Tactical support for <<ok_kind_ctx>> *)
(******************************************************************************)
Lemma ok_kind_ctx_app1 : forall Δ1 Δ2,
    ok_kind_ctx Δ1 /\ ok_kind_ctx Δ2 /\ disjoint Δ1 Δ2 ->
    ok_kind_ctx (Δ1 ++ Δ2).
Proof.
  intros. unfold ok_kind_ctx in *.
  now bursts.
Qed.

Lemma ok_kind_ctx_mid1: forall Δ1 Δ2 Δ3,
    ok_kind_ctx (Δ1 ++ Δ2 ++ Δ3) ->
    ok_kind_ctx Δ2.
Proof.
  intros. unfold ok_kind_ctx in *.
  now bursts.
Qed.

Lemma ok_kind_ctx_mid2 : forall Δ1 Δ2 Δ3,
    ok_kind_ctx (Δ1 ++ Δ2 ++ Δ3) ->
    ok_kind_ctx (Δ1 ++ Δ3).
Proof.
  intros. unfold ok_kind_ctx in *.
  bursts. now rewrite disjoint_sym.
Qed.

Lemma ok_kind_ctx_app_l : forall Δ1 Δ2,
    ok_kind_ctx (Δ1 ++ Δ2) ->
    ok_kind_ctx Δ1.
Proof.
  intros. unfold ok_kind_ctx in *.
  now bursts.
Qed.

Lemma ok_kind_ctx_app_r : forall Δ1 Δ2,
    ok_kind_ctx (Δ1 ++ Δ2) ->
    ok_kind_ctx Δ2.
Proof.
  intros. unfold ok_kind_ctx in *.
  now bursts.
Qed.

#[export] Hint Resolve ok_kind_ctx_app1 : sysf_ctx.
#[export] Hint Immediate ok_kind_ctx_mid1 ok_kind_ctx_mid2 : sysf_ctx.
#[export] Hint Immediate ok_kind_ctx_app_l ok_kind_ctx_app_r : sysf_ctx.

(** ** General properties of <<ok_type>> *)
(******************************************************************************)

(** A well-formed type is locally closed. *)
Lemma ok_type_lc : forall Δ τ,
    ok_type Δ τ ->
    locally_closed typ KType τ.
Proof.
  unfold ok_type. tauto.
Qed.

#[export] Hint Immediate ok_type_lc : sysf_ctx.
#[export] Hint Resolve ok_type_lc : sysf_ctx.

(** ** Structural properties of <<ok_type Δ τ>> in <<Δ>> *)
(******************************************************************************)

(** *** Permutation *)
(******************************************************************************)
Lemma ok_type_perm : forall Δ1 Δ2 τ,
    Permutation Δ1 Δ2 ->
    ok_type Δ1 τ <->
    ok_type Δ2 τ.
Proof.
  intros. unfold ok_type. now rewrite (scoped_perm_iff); eauto.
Qed.

Lemma ok_type_perm1 : forall Δ1 Δ2 τ,
    ok_type Δ1 τ ->
    Permutation Δ1 Δ2 ->
    ok_type Δ2 τ.
Proof.
  intros. rewrite <- ok_type_perm; eauto.
Qed.

(** *** Weakening *)
Lemma ok_type_weak_r : forall Δ1 Δ2 τ,
    ok_type Δ1 τ ->
    ok_type (Δ1 ++ Δ2) τ.
Proof.
  unfold ok_type.
  intros. split.
  - apply (scoped_weak_l typ). tauto.
  - tauto.
Qed.

Lemma ok_type_weak_l : forall Δ1 Δ2 τ,
    ok_type Δ2 τ ->
    ok_type (Δ1 ++ Δ2) τ.
Proof.
  unfold ok_type. intuition (auto using (scoped_weak_r typ)).
Qed.

(** *** Strengthening  *)
(******************************************************************************)
Lemma ok_type_stren : forall Δ1 Δ2 x τ,
    ok_type (Δ1 ++ x ~ tt ++ Δ2) τ ->
    ~ x ∈@ (freeset typ KType τ) ->
    ok_type (Δ1 ++ Δ2) τ.
Proof.
  introv [? ?] ?. unfold ok_type.
  eauto using (scoped_stren_mid typ).
Qed.

Corollary ok_type_stren1 : forall Δ x τ,
    ok_type (Δ ++ x ~ tt) τ ->
    ~ x ∈@ (freeset typ KType τ) ->
    ok_type Δ τ.
Proof.
  introv H1 H2. change_alist (Δ ++ x ~ tt ++ []) in H1.
  change_alist (Δ ++ []). eauto using ok_type_stren.
Qed.

(** *** Substitution *)
(******************************************************************************)
Lemma ok_type_sub : forall Δ1 Δ2 x τ1 τ2,
    ok_type (Δ1 ++ x ~ tt ++ Δ2) τ1 ->
    ok_type (Δ1 ++ Δ2) τ2 ->
    ok_type (Δ1 ++ Δ2) (subst typ KType x τ2 τ1).
Proof.
  unfold ok_type. introv [? ?] [? ?]. split.
  - pose (lemma := scoped_sub_eq_mid typ KType).
    eapply lemma; eassumption.
  - auto using (subst_lc_eq typ).
Qed.

Corollary ok_type_sub1 : forall Δ x τ1 τ2,
    ok_type (Δ ++ x ~ tt) τ1 ->
    ok_type Δ τ2 ->
    ok_type Δ (subst typ KType x τ2 τ1).
Proof.
  introv H1 H2. change_alist (Δ ++ x ~ tt ++ []) in H1.
  change_alist (Δ ++ []) in H2. change_alist (Δ ++ []).
  auto using ok_type_sub.
Qed.

#[export] Hint Immediate ok_type_perm1 : sysf_ctx.
#[export] Hint Resolve ok_type_weak_l ok_type_weak_r : sysf_ctx.
#[export] Hint Immediate ok_type_stren ok_type_stren1 : sysf_ctx.
#[export] Hint Resolve ok_type_sub : sysf_ctx.
#[export] Hint Resolve ok_type_sub1 : sysf_ctx.

(** ** General properties of <<ok_type_ctx>> *)
(******************************************************************************)
Lemma ok_type_ctx_nil : forall Δ,
    ok_type_ctx Δ [].
Proof.
  intros. unfold ok_type_ctx in *. now bursts.
Qed.

Lemma ok_type_ctx_cons : forall Δ Γ x τ,
    ok_type_ctx Δ Γ ->
    ~ (x ∈@ domset Γ) ->
    ok_type Δ τ ->
    ok_type_ctx Δ (x ~ τ ++ Γ).
Proof.
  intros. unfold ok_type_ctx in *. bursts.
  splits.
  - intuition.
  - intros ? [?|?].
    + subst. auto.
    + firstorder.
Qed.

Lemma ok_type_ctx_one : forall Δ x τ,
    ok_type Δ τ ->
    ok_type_ctx Δ (x ~ τ).
Proof.
  intros. change (x ~ τ) with [(x, τ)].
  apply ok_type_ctx_cons; auto using ok_type_ctx_nil.
  fsetdec.
Qed.

Lemma ok_type_ctx_app : forall Δ Γ1 Γ2,
    ok_type_ctx Δ (Γ1 ++ Γ2) <->
    ok_type_ctx Δ Γ1 /\ ok_type_ctx Δ Γ2 /\ disjoint Γ1 Γ2.
Proof.
  intros. unfold ok_type_ctx.
  setoid_rewrite in_range_iff.
  setoid_rewrite List.in_list_app.
  rewrite uniq_app_iff. firstorder.
Qed.

Lemma ok_type_ctx_app_comm : forall {Δ Γ1 Γ2},
    ok_type_ctx Δ (Γ1 ++ Γ2) <->
    ok_type_ctx Δ (Γ2 ++ Γ1).
Proof.
  intros. unfold ok_type_ctx. bursts.
  rewrite disjoint_sym. firstorder.
Qed.

Lemma ok_type_ctx_binds : forall Δ Γ x τ,
    ok_type_ctx Δ Γ ->
    (x, τ) ∈ Γ ->
    ok_type Δ τ.
Proof.
  introv Hok Hin. unfold ok_type_ctx, ok_type in *.
  apply Hok. erewrite (in_range_iff Γ); eauto.
Qed.

(** <<ok_type_ctx Δ Γ>> supports permutation in Γ. *)
Lemma ok_type_ctx_perm_gamma1 : forall Δ Γ1 Γ2,
    ok_type_ctx Δ Γ1 ->
    Permutation Γ1 Γ2 ->
    ok_type_ctx Δ Γ2.
Proof.
  introv [huniq hok]. unfold ok_type_ctx in *. split.
  - rewrite uniq_perm; eauto. now symmetry.
  - intros τ hin; specialize (hok τ).
    apply hok. rewrite perm_range; eauto.
Qed.

Corollary ok_type_ctx_perm_gamma : forall Δ Γ1 Γ2,
    Permutation Γ1 Γ2 ->
    ok_type_ctx Δ Γ1 <-> ok_type_ctx Δ Γ2.
Proof.
  introv Hperm; split; intro.
  - eauto using ok_type_ctx_perm_gamma1.
  - symmetry in Hperm. eauto using ok_type_ctx_perm_gamma1.
Qed.

#[export] Hint Resolve ok_type_ctx_nil : sysf_ctx.
#[export] Hint Resolve ok_type_ctx_cons : sysf_ctx.
#[export] Hint Resolve ok_type_ctx_one : sysf_ctx.
#[export] Hint Immediate ok_type_ctx_app_comm : sysf_ctx.
#[export] Hint Immediate ok_type_ctx_binds : sysf_ctx.
#[export] Hint Immediate ok_type_ctx_perm_gamma : sysf_ctx.

(** ** Tactical support for <<ok_type_ctx>> *)
(******************************************************************************)
Lemma ok_type_ctx_inv_app_l : forall Δ Γ1 Γ2,
    ok_type_ctx Δ (Γ1 ++ Γ2) ->
    ok_type_ctx Δ Γ1.
Proof.
  introv [huniq hscope]. unfold ok_type_ctx in *.
  bursts. firstorder.
Qed.

Corollary ok_type_ctx_inv_app_r : forall Δ Γ1 Γ2,
    ok_type_ctx Δ (Γ1 ++ Γ2) ->
    ok_type_ctx Δ Γ2.
Proof.
  introv hyp. rewrite ok_type_ctx_app_comm in hyp.
  eauto using ok_type_ctx_inv_app_l.
Qed.

Corollary ok_type_ctx_inv_mid : forall Δ Γ1 Γ2 Γ3,
    ok_type_ctx Δ (Γ1 ++ Γ2 ++ Γ3) ->
    ok_type_ctx Δ (Γ1 ++ Γ3).
Proof.
  introv hyp.
  change_alist ((Γ1 ++ Γ2) ++ Γ3) in hyp.
  rewrite ok_type_ctx_app_comm in hyp.
  change_alist ((Γ3 ++ Γ1) ++ Γ2) in hyp.
  apply ok_type_ctx_inv_app_l in hyp.
  now rewrite ok_type_ctx_app_comm in hyp.
Qed.

#[export] Hint Immediate ok_type_ctx_inv_app_l : sysf_ctx.
#[export] Hint Immediate ok_type_ctx_inv_app_r : sysf_ctx.
#[export] Hint Immediate ok_type_ctx_inv_mid : sysf_ctx.

(** ** Structural properties in <<Δ>> in <<ok_type_ctx Δ Γ>>. *)
(******************************************************************************)

(** *** Permutation *)
(******************************************************************************)
Theorem ok_type_ctx_perm1 : forall Δ1 Δ2 Γ,
    ok_type_ctx Δ1 Γ ->
    Permutation Δ1 Δ2 ->
    ok_type_ctx Δ2 Γ.
Proof.
  introv [? ?] ?. unfold ok_type_ctx.
  split; eauto using ok_type_perm1 with tea_alist.
Qed.

Corollary ok_type_ctx_perm : forall Δ1 Δ2 Γ,
    Permutation Δ1 Δ2 ->
    ok_type_ctx Δ1 Γ <-> ok_type_ctx Δ2 Γ.
Proof.
  introv Hperm. unfold ok_type_ctx, ok_type.
  split; intros.
  - eapply ok_type_ctx_perm1; eauto.
  - eapply ok_type_ctx_perm1; eauto.
    now apply Permutation_sym.
Qed.

#[local] Set Firstorder Depth 4.

(** *** Weakening *)
(******************************************************************************)
Lemma ok_type_ctx_weak_r : forall Δ1 Δ2 Γ,
    ok_type_ctx Δ1 Γ ->
    ok_type_ctx (Δ1 ++ Δ2) Γ.
Proof.
  introv [huniq hok1]. unfold ok_type_ctx in *.
  firstorder using ok_type_weak_r.
Qed.

(** *** Strengthening *)
(******************************************************************************)
Lemma ok_type_ctx_stren : forall Δ1 Δ2 x Γ,
    ok_type_ctx (Δ1 ++ x ~ tt ++ Δ2) Γ ->
    (forall t : typ leaf, t ∈ range Γ -> ~ x ∈@ freeset typ KType t) ->
    ok_type_ctx (Δ1 ++ Δ2) Γ.
Proof.
  introv [hunit hok] hfresh.
  unfold ok_type_ctx. split; [trivial |].
  intros τ hin; specialize (hok τ hin).
  eauto using ok_type_stren.
Qed.

Corollary ok_type_ctx_stren1 : forall Δ x Γ,
    ok_type_ctx (Δ ++ x ~ tt) Γ ->
    (forall t : typ leaf, t ∈ range Γ -> ~ x ∈@ freeset typ KType t) ->
    ok_type_ctx Δ Γ.
Proof.
  introv hyp1 hyp2. change_alist (Δ ++ x ~ tt ++ []) in hyp1.
  change_alist (Δ ++ []). eauto using ok_type_ctx_stren.
Qed.

Lemma ok_type_ctx_sub : forall Δ1 Δ2 x Γ τ,
    ok_type_ctx (Δ1 ++ x ~ tt ++ Δ2) Γ ->
    ok_type (Δ1 ++ Δ2) τ ->
    locally_closed typ KType τ ->
    ok_type_ctx (Δ1 ++ Δ2) (envmap (subst typ KType x τ) Γ).
Proof.
  introv [hunit hok] Hscope lc. unfold ok_type_ctx. split.
  - now apply uniq_fmap2.
  - intros τ2 τ2in.
    rewrite in_range_iff in τ2in.
    setoid_rewrite in_envmap_iff in τ2in.
    destruct τ2in as [y [τ2_inv [? ?]]]; subst.
    specialize (hok τ2_inv).
    apply ok_type_sub.
    + apply hok. rewrite in_range_iff. eauto.
    + auto.
Qed.

#[export] Hint Immediate ok_type_ctx_perm : sysf_ctx.
#[export] Hint Resolve ok_type_ctx_perm1 : sysf_ctx.
#[export] Hint Resolve ok_type_ctx_weak_r : sysf_ctx.
#[export] Hint Resolve ok_type_ctx_sub : sysf_ctx.

(** ** Structural properties of <<ok_term Δ Γ t>> in <<Δ>> *)
(******************************************************************************)

(** *** Permutation *)
(******************************************************************************)
Lemma ok_term_perm_delta : forall Δ1 Δ2 Γ t,
    Permutation Δ1 Δ2 ->
    ok_term Δ1 Γ t <->
    ok_term Δ2 Γ t.
Proof.
  intros. unfold ok_term.
  now rewrite scoped_perm_iff.
Qed.

(** *** Weakening *)
(******************************************************************************)
Lemma ok_term_weak_delta_r : forall Δ1 Δ2 Γ t,
    ok_term Δ1 Γ t ->
    ok_term (Δ1 ++ Δ2) Γ t.
Proof.
  unfold ok_term. intros.
  intuition (eauto using (scoped_weak_l term)).
Qed.

Lemma ok_term_weak_delta_l : forall Δ1 Δ2 Γ t,
    ok_term Δ2 Γ t ->
    ok_term (Δ1 ++ Δ2) Γ t.
Proof.
  unfold ok_term. intros.
  intuition (eauto using (scoped_weak_r term)).
Qed.

(** *** Strengthening  *)
(******************************************************************************)
Lemma ok_term_stren_delta : forall Δ1 Δ2 x Γ t,
    ok_term (Δ1 ++ x ~ tt ++ Δ2) Γ t ->
    ~ x ∈@ (freeset term KType t) ->
    ok_term (Δ1 ++ Δ2) Γ t.
Proof.
  introv Hok Hfresh. unfold ok_term in *.
  intuition. eapply (scoped_stren_mid term); eauto.
Qed.

(** *** Substitution *)
(******************************************************************************)
Lemma ok_term_sub_delta : forall Δ1 Δ2 x τ Γ t,
    ok_term (Δ1 ++ x ~ tt ++ Δ2) Γ t ->
    ok_type (Δ1 ++ Δ2) τ ->
    ok_term (Δ1 ++ Δ2) (envmap (subst typ KType x τ) Γ) (subst term KType x τ t).
Proof.
  introv Hokt Hokτ. unfold ok_term, ok_type in *.
  intuition.
  - eapply (scoped_sub_eq_mid term); eauto.
  - apply scoped_envmap.
    eapply (scoped_sub_neq term); eauto.
    + discriminate.
    + apply rw_scoped_KTerm_type.
  - eapply (subst_lc_neq term); auto.
    + discriminate.
    + now apply rw_lc_KTerm_type.
  - eapply (subst_lc_eq term); auto.
Qed.

(** ** Structural properties of <<ok_term Δ Γ t>> in <<Γ>> *)
(******************************************************************************)

(** *** Permutation *)
(******************************************************************************)
Lemma ok_term_perm_gamma : forall Δ Γ1 Γ2 t,
    Permutation Γ1 Γ2 ->
    ok_term Δ Γ1 t <->
    ok_term Δ Γ2 t.
Proof.
  intros. unfold ok_term.
  pose (lemma := scoped_perm_iff term (KTerm : K)).
  now rewrite lemma; eauto.
Qed.

(** *** Weakening *)
(******************************************************************************)
Lemma ok_term_weak_gamma_r : forall Δ Γ1 Γ2 t,
    ok_term Δ Γ1 t ->
    ok_term Δ (Γ1 ++ Γ2) t.
Proof.
  unfold ok_term. intros.
  intuition (eauto using (scoped_weak_l term)).
Qed.

Lemma ok_term_weak_gamma_l : forall Δ Γ1 Γ2 t,
    ok_term Δ Γ2 t ->
    ok_term Δ (Γ1 ++ Γ2) t.
Proof.
  unfold ok_term. intros.
  intuition (eauto using (scoped_weak_r term)).
Qed.

(** *** Strengthening  *)
(******************************************************************************)
Lemma ok_term_stren_gamma : forall Δ Γ1 Γ2 x τ t,
    ok_term Δ (Γ1 ++ x ~ τ ++ Γ2) t ->
    ~ x ∈@ (freeset term KTerm t) ->
    ok_term Δ (Γ1 ++ Γ2) t.
Proof.
  introv Hok Hfresh. unfold ok_term in *.
  intuition. eapply (scoped_stren_mid term); eauto.
Qed.

(** *** Substitution *)
(******************************************************************************)
Lemma ok_term_sub_gamma : forall Δ Γ1 Γ2 x τ u t,
    ok_term Δ (Γ1 ++ x ~ τ ++ Γ2) t ->
    ok_term Δ (Γ1 ++ Γ2) u ->
    ok_term Δ (Γ1 ++ Γ2) (subst term KTerm x u t).
Proof.
  introv Hokt Hoku. unfold ok_term, ok_type in *.
  intuition.
  - eapply (scoped_sub_neq term); auto.
    + discriminate.
  - eapply (scoped_sub_eq_mid term); eauto.
  - eapply (subst_lc_eq term); auto.
  - eapply (subst_lc_neq term); auto.
    + discriminate.
Qed.
