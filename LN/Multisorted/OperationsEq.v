From Tealeaves Require Export
     Util.Prelude
     Util.EqDec_eq LN.Atom LN.AtomSet LN.Leaf
     LN.Multisorted.Operations.

From Multisorted Require Import
     Classes.DTM
     Theory.DTMContainer
     Theory.DTMSchedule.

Import Monoid.Notations.
Import LN.AtomSet.Notations.
Import Classes.SetlikeFunctor.Notations.
Import Multisorted.Theory.DTMContainer.Notations.

#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.
#[local] Open Scope set_scope.

Section operation_specifications.

  Import Operations.Notations.

  Context
    (S : Type -> Type)
    `{DTPreModule (list K) S T (mn_op := Monoid_op_list) (mn_unit := Monoid_unit_list)}
    `{! DTM (list K) T}.

  Implicit Types (l : leaf) (w : list K) (t : S leaf) (x : atom).

  (** ** Identity and equality lemmas for operations *)
  (******************************************************************************)
  Lemma open_eq : forall k t (u1 u2 : T k leaf),
      (forall (w : list K) (l : leaf), (w, (k, l)) ∈md t -> open_loc k u1 (w, l) = open_loc k u2 (w, l)) ->
      t '(k | u1) = t '(k | u2).
  Proof.
    introv hyp. unfold open. apply kbindd_respectful. auto.
  Qed.

  Lemma open_id : forall k t u,
      (forall w l, (w, (k, l)) ∈md t -> open_loc k u (w, l) = mret T k l) ->
      t '(k | u) = t.
  Proof.
    intros. unfold open.
    now apply (kbindd_respectful_id k).
  Qed.

  Lemma subst_eq : forall k t x u1 u2,
      (forall l, (k, l) ∈m t -> subst_loc k x u1 l = subst_loc k x u2 l) ->
      t '{k | x ~> u1} = t '{k | x ~> u2}.
  Proof.
    introv hyp. unfold subst. apply kbind_respectful. auto.
  Qed.

  Lemma subst_id : forall k t x u,
      (forall l, (k, l) ∈m t -> subst_loc k x u l = mret T k l) ->
      t '{k | x ~> u} = t.
  Proof.
    intros. unfold subst.
    now apply kbind_respectful_id.
  Qed.

  Lemma close_eq : forall k t x y,
      (forall w l, (w, (k, l)) ∈md t -> close_loc k x (w, l) = close_loc k y (w, l)) ->
      '[k | x] t = '[k | y] t.
  Proof.
    intros. unfold close.
    now apply (kfmapd_respectful).
  Qed.

  Lemma close_id : forall k t x,
      (forall w l, (w, (k, l)) ∈md t -> close_loc k x (w, l) = l) ->
      '[k | x] t = t.
  Proof.
    intros. unfold close.
    now apply (kfmapd_respectful_id).
  Qed.

  (** ** Context-sensitive leaf analysis of operations *)
  (******************************************************************************)

  (** *** Opening *)
  (******************************************************************************)
  Lemma ind_open_iff_eq : forall k l w u t,
      (w, (k, l)) ∈md t '(k | u) <-> exists w1 w2 l1,
        (w1, (k, l1)) ∈md t /\ (w2, (k, l)) ∈md open_loc k u (w1, l1) /\ w = w1 ● w2.
  Proof.
    intros. unfold open.
    now rewrite (ind_kbindd_eq_iff S).
  Qed.

  Lemma ind_open_neq_iff : forall k j l w u t,
      k <> j ->
      (w, (k, l)) ∈md t '(j | u) <-> (w, (k, l)) ∈md t \/ exists w1 w2 l1,
          (w1, (j, l1)) ∈md t /\ (w2, (k, l)) ∈md open_loc j u (w1, l1) /\ w = w1 ● w2.
  Proof.
    intros. unfold open.
    now rewrite (ind_kbindd_neq_iff S); auto.
  Qed.

  (** *** Closing *)
  (******************************************************************************)
  Lemma ind_close_iff_eq : forall k l w x t,
      (w, (k, l)) ∈md '[k | x] t <-> exists l1,
        (w, (k, l1)) ∈md t /\ l = close_loc k x (w, l1).
  Proof.
    intros. unfold close.
    rewrite (ind_kfmapd_eq_iff S).
    easy.
  Qed.

  Lemma ind_close_neq_iff : forall k j l w x t,
      j <> k ->
      (w, (k, l)) ∈md '[j | x] t <-> (w, (k, l)) ∈md t.
  Proof.
    intros. unfold close.
    now rewrite (ind_kfmapd_neq_iff S).
  Qed.

  (** *** Substitution *)
  (******************************************************************************)
  Lemma ind_subst_iff_eq : forall k w l u t x,
      (w, (k, l)) ∈md t '{k | x ~> u} <-> exists w1 w2 l1,
        (w1, (k, l1)) ∈md t /\ (w2, (k, l)) ∈md subst_loc k x u l1 /\ w = w1 ● w2.
  Proof.
    intros. unfold subst.
    now rewrite (ind_kbind_eq_iff S).
  Qed.

  Lemma ind_subst_neq_iff : forall k j w l u t x,
      k <> j ->
      (w, (k, l)) ∈md t '{j | x ~> u} <-> (w, (k, l)) ∈md t \/ exists w1 w2 l1,
        (w1, (j, l1)) ∈md t /\ (w2, (k, l)) ∈md subst_loc j x u l1 /\ w = w1 ● w2.
  Proof.
    intros. unfold subst.
    now rewrite (ind_kbind_neq_iff S); auto.
  Qed.

  (** ** Context-agnostic leaf analysis of operations *)
  (******************************************************************************)

  (** *** Opening *)
  (******************************************************************************)
  Lemma in_open_eq_iff : forall k l u t,
      (k, l) ∈m t '(k | u) <-> exists w1 l1,
        (w1, (k, l1)) ∈md t /\ (k, l) ∈m open_loc k u (w1, l1).
  Proof.
    intros. unfold open.
    now rewrite (in_kbindd_eq_iff S).
  Qed.

  Lemma in_open_neq_iff : forall k j l u t,
      k <> j ->
      (k, l) ∈m t '(j | u) <-> (k, l) ∈m t \/ exists w1 l1,
          (w1, (j, l1)) ∈md t /\ (k, l) ∈m open_loc j u (w1, l1).
  Proof.
    intros. unfold open.
    now rewrite (in_kbindd_neq_iff S); auto.
  Qed.

  (** *** Closing *)
  (******************************************************************************)
  Lemma in_close_eq_iff : forall k l x t,
      (k, l) ∈m '[k | x] t <-> exists w l1,
        (w, (k, l1)) ∈md t /\ l = close_loc k x (w, l1).
  Proof.
    intros. unfold close.
    now rewrite (in_kfmapd_eq_iff S).
  Qed.

  Lemma in_close_neq_iff : forall k j l x t,
      k <> j ->
      (k, l) ∈m '[j | x] t <-> (k, l) ∈m t.
  Proof.
    intros. unfold close.
    now rewrite (in_kfmapd_neq_iff S); auto.
  Qed.

  (** *** Substitution *)
  (******************************************************************************)
  Lemma in_subst_eq_iff : forall k l u t x,
      (k, l) ∈m t '{k | x ~> u} <-> exists l1,
        (k, l1) ∈m t /\ (k, l) ∈m subst_loc k x u l1.
  Proof.
    intros. unfold subst.
    now rewrite (in_kbind_eq_iff S).
  Qed.

  Lemma in_subst_neq_iff : forall k j l u t x,
      j <> k ->
      (k, l) ∈m t '{j | x ~> u} <-> (k, l) ∈m t \/ exists l1,
        (j, l1) ∈m t /\ (k, l) ∈m subst_loc j x u l1.
  Proof.
    intros. unfold subst.
    now rewrite (in_kbind_neq_iff S).
  Qed.

  (** ** Properties of free variables *)
  (******************************************************************************)

  (** *** Specifications for [free] and [freeset] *)
  (******************************************************************************)
  Theorem in_free_iff : forall (k : K) (t : S leaf) (x : atom),
      x ∈ free S k t <-> (k, Fr x) ∈m t.
  Proof.
    intros. unfold free. rewrite (Tealeaves.Classes.SetlikeMonad.in_bind_iff list). split.
    - intros [l [lin xin]]. rewrite <- (in_iff_in_toklist) in lin.
      destruct l as [a|n].
      + cbv in xin. destruct xin as [?|[]].
        subst. assumption.
      + cbv in xin. destruct xin as [].
    - intros. exists (Fr x). rewrite <- (in_iff_in_toklist).
      split; [assumption| ].
      cbv. now left.
  Qed.

  Theorem in_free_iff_T : forall (k j : K) (t : T j leaf) (x : atom),
      x ∈ free (T j) k t <-> (k, Fr x) ∈m t.
  Proof.
    intros. unfold free. rewrite (Tealeaves.Classes.SetlikeMonad.in_bind_iff list). split.
    - intros [l [lin xin]]. rewrite <- (in_iff_in_toklist) in lin.
      destruct l as [a|n].
      + cbv in xin. destruct xin as [?|[]].
        subst. assumption.
      + cbv in xin. destruct xin as [].
    - intros. exists (Fr x). rewrite <- (in_iff_in_toklist).
      split; [assumption| ].
      cbv. now left.
  Qed.

  Theorem free_iff_freeset : forall (k : K) (t : S leaf) (x : atom),
      x ∈ free S k t <-> x ∈@ freeset S k t.
  Proof.
    intros. unfold freeset. rewrite <- in_atoms_iff.
    reflexivity.
  Qed.

  Theorem free_iff_freeset_T : forall (k j : K) (t : T j leaf) (x : atom),
      x ∈ free (T j) k t <-> x ∈@ freeset (T j) k t.
  Proof.
    intros. unfold freeset. rewrite <- in_atoms_iff.
    reflexivity.
  Qed.

  (** *** Opening *)
  (******************************************************************************)
  Local Notation "x @ < k , w > ∈ t" :=
    (tomsetd _ t (w, (k, x))) (k at level 5, w at level 5, at level 50) : tealeaves_multi_scope.

  Lemma free_open_eq_iff : forall k u t x,
      x ∈ free S k (t '(k | u)) <-> exists w l1,
        l1 @ <k, w> ∈ t /\ x ∈ free (T k) k (open_loc k u (w, l1)).
  Proof.
    intros. rewrite in_free_iff. setoid_rewrite in_free_iff_T.
    now rewrite in_open_eq_iff.
  Qed.

  Lemma free_open_neq_iff : forall k j u t x,
      k <> j ->
      x ∈ free S j (t '(k | u)) <-> x ∈ free S j t \/ exists w l1,
          (w, (k, l1)) ∈md t /\ x ∈ free (T k) j (open_loc k u (w, l1)).
  Proof.
    intros. rewrite 2(in_free_iff). setoid_rewrite in_free_iff_T.
    now rewrite in_open_neq_iff; auto.
  Qed.

  (** *** Closing *)
  (******************************************************************************)
  Lemma free_close_eq_iff : forall k t x y,
      y ∈ free S k ('[k | x] t) <-> exists w l1,
        l1 @ <k, w> ∈ t /\ Fr y = close_loc k x (w, l1).
  Proof.
    intros. rewrite in_free_iff.
    now rewrite in_close_eq_iff.
  Qed.

  Lemma free_close_neq_iff : forall k j t x,
      k <> j ->
      x ∈ free S j ('[k | x] t) <-> x ∈ free S j t.
  Proof.
    intros. rewrite 2(in_free_iff).
    now rewrite in_close_neq_iff; auto.
  Qed.

  (** *** Substitution *)
  (******************************************************************************)
  Lemma free_subst_eq_iff : forall k u t x y,
      y ∈ free S k (t '{k | x ~> u}) <-> exists l1,
        (k, l1) ∈m t /\ y ∈ free (T k) k (subst_loc k x u l1).
  Proof.
    intros. rewrite (in_free_iff). setoid_rewrite (in_free_iff_T).
    now rewrite (in_subst_eq_iff).
  Qed.

  Lemma free_subst_neq_iff : forall j k u t x y,
      k <> j ->
      y ∈ free S j (t '{k | x ~> u}) <-> y ∈ free S j t \/ exists l1,
        (k, l1) ∈m t /\ y ∈ free (T k) j (subst_loc k x u l1).
  Proof.
    intros. rewrite 2(in_free_iff). setoid_rewrite (in_free_iff_T).
    now rewrite (in_subst_neq_iff); auto.
  Qed.

End operation_specifications.
