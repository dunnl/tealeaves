From Tealeaves Require Export
  Examples.STLC.Syntax.

Import STLC.Syntax.Notations.
#[local] Notation "'P'" := pure.
#[local]  Notation "'BD'" := binddt.
#[local] Open Scope tealeaves_scope.

Ltac simplify := simplify_with_simplify_binddt term simplify_binddt_term_lazy.

(** ** Rewriting lemmas for <<tolist>>, <<toset>>, <<∈>> *)
(******************************************************************************)
Section term_container_rewrite.

  Variable
    (A : Type).

  Definition tolist_tvar_rw1: forall (x: A),
      tolist (tvar x) = [x] :=
    ltac:(simplify).

  Definition tolist_term_rw2: forall (X: typ) (t: term A),
      tolist (lam X t) = tolist t :=
    ltac:(simplify).

  Definition tolist_term_rw3: forall (t1 t2: term A),
      tolist (app t1 t2) = tolist t1 ++ tolist t2 :=
    ltac:(simplify).

  Definition toset_tvar_rw1: forall (x: A),
      element_of (tvar x) = {{x}}
    := ltac:(simplify).

  Definition toset_term_rw2: forall (X: typ) (t: term A),
      element_of (lam X t) = element_of t
    := ltac:(simplify).

  Definition toset_term_rw3: forall (t1 t2: term A),
      element_of (app t1 t2) = element_of t1 ∪ element_of t2
    := ltac:(simplify).

  Lemma in_term_rw1: forall (x y: A),
      x ∈ tvar y <-> x = y.
  Proof.
    simplify.
  Qed.

  Lemma in_term_rw2: forall (y: A) (X: typ) (t: term A),
    y ∈ (lam X t) <-> y ∈ t.
  Proof.
    simplify.
  Qed.

  Lemma in_term_3: forall (t1 t2: term A) (y: A),
      y ∈ (app t1 t2) <-> y ∈ t1 \/ y ∈ t2.
  Proof.
    simplify.
  Qed.

End term_container_rewrite.

(** ** Rewriting lemmas for <<free>>, <<freeset>> *)
(******************************************************************************)
Section term_free_rewrite.

  Variable (A : Type).

  Definition term_free11 : forall (b : nat),
      free (tvar (Bd b)) = []
    := ltac:(simplify).

  Definition term_in_free11 : forall (b : nat) (x : atom),
      x ∈ free (tvar (Bd b)) <-> False
    := ltac:(simplify).

  Definition term_free12 : forall (y : atom),
      free (tvar (Fr y)) = [y]
    := ltac:(simplify).

  Definition term_in_free12 : forall (y : atom) (x : atom),
      x ∈ free (tvar (Fr y)) <-> x = y
    := ltac:(simplify).

  Definition term_free2 : forall (t : term LN) (X : typ),
      free (lam X t) = free t
    := ltac:(simplify).

  Definition term_in_free2 : forall (x : atom) (t : term LN) (X : typ),
      x ∈ free (lam X t) <-> x ∈ free t
    := ltac:(simplify).

  Definition term_free3 : forall (x : atom) (t1 t2 : term LN),
      free (app t1 t2) = free t1 ++ free t2
    := ltac:(simplify).

  Definition term_in_free3 : forall (x : atom) (t1 t2 : term LN),
      x ∈ free (app t1 t2) <-> x ∈ free t1 \/ x ∈ free t2
    := ltac:(simplify).

  Definition term_in_freeset11 : forall (b : nat) (x : atom),
      AtomSet.In x (freeset (tvar (Bd b))) <-> False
    := ltac:(simplify).

  Definition term_in_freeset12 : forall (y : atom) (x : atom),
      AtomSet.In x (freeset (tvar (Fr y))) <-> x = y.
  Proof.
    simplify.
  Qed.

  Lemma term_in_freeset2 : forall (x : atom) (t : term LN) (X : typ),
      AtomSet.In x (freeset (lam X t)) <-> AtomSet.In x (freeset t).
  Proof.
    simplify.
  Qed.

  Lemma term_in_freeset3 : forall (x : atom) (t1 t2 : term LN),
      AtomSet.In x (freeset (app t1 t2)) <->
        AtomSet.In x (freeset t1) \/ AtomSet.In x (freeset t2).
  Proof.
    simplify.
  Qed.

  Open Scope set_scope.

  Lemma term_freeset11 : forall (b : nat) (x : atom),
      freeset (tvar (Bd b)) [=] ∅.
  Proof.
    intros. fsetdec.
  Qed.

  Lemma term_freeset12 : forall (y : atom),
      freeset (tvar (Fr y)) [=] {{ y }}.
  Proof.
    simplify.
  Qed.

  Lemma term_freeset2 : forall (t : term LN) (X : typ),
      freeset (lam X t) [=] freeset t.
  Proof.
    simplify.
  Qed.

  Lemma term_freeset3 : forall (t1 t2 : term LN),
      freeset (app t1 t2) [=] freeset t1 ∪ freeset t2.
  Proof.
    simplify.
  Qed.

End term_free_rewrite.

(** ** Rewriting lemmas for <<foldMapd>> *)
(******************************************************************************)
Section term_foldMapd_rewrite.

  Context {A M : Type} (f : nat * A -> M) `{Monoid M}.

  Lemma term_foldMapd1 : forall (a : A),
      foldMapd f (tvar a) = f (Ƶ, a).
  Proof.
    simplify.
  Qed.

  Lemma term_foldMapd2 : forall X (t : term A),
      foldMapd f (λ X t) = foldMapd (f ⦿ 1) t.
  Proof.
    simplify.
  Qed.

  Lemma term_foldMapd3 : forall (t1 t2 : term A),
      foldMapd f ([t1]@[t2]) = foldMapd f t1 ● foldMapd f t2.
  Proof.
    simplify.
  Qed.

End term_foldMapd_rewrite.

(** ** Rewriting lemmas for <<∈d>> *)
(******************************************************************************)
Section term_ind_rewrite.

  Lemma term_ind1 : forall (l1 l2 : LN) (n : nat),
      (n, l1) ∈d (tvar l2) <-> n = Ƶ /\ l1 = l2.
  Proof.
    simplify.
  Qed.

  Lemma term_ind2 : forall (t : term LN) (l : LN) (n : nat) (X : typ),
      (n, l) ∈d t = (S n, l) ∈d (λ X t).
  Proof.
    simplify.
  Qed.

  Lemma term_ind2_nZ : forall (t : term LN) (l : LN) (n : nat) (X : typ),
      (n, l) ∈d (λ X t) -> (n <> 0).
  Proof.
    introv.
    Ltac simplify_pass1 :=
      simplify_pass1_with_simplify_binddt term simplify_binddt_term_lazy.
    repeat simplify_pass1.
    repeat simplify_pass2.
    assert (Hgt: 1 > 0) by lia; generalize dependent Hgt.
    generalize 1 as m.
    induction t;
      intros m Hgt;
      repeat simplify_pass1;
      repeat simplify_pass2.
    - unfold preincr, compose, incr; cbn.
      rewrite pair_equal_spec.
      change (?m ● ?x) with (m + x)%nat. lia.
    - rewrite preincr_preincr.
      intro hyp.
      eapply IHt.
      2: eauto.
      change (?m ● ?x) with (m + x)%nat.
      lia.
    - intros [hyp|hyp]; eauto.
  Qed.

  Lemma term_ind2_nZ2: forall t n l,
      (@binddt nat term term Binddt_STLC (@const Type Type Prop)
        (@Map_const Prop) (@Pure_const Prop False) (@Mult_const Prop or) LN False
        (eq (n, l) ⦿ 1) t) -> n <> 0.
  Proof.
    introv.
    assert (Hgt: 1 > 0) by lia; generalize dependent Hgt.
    generalize 1 as m.
    induction t;
      intros m Hgt;
      simplify_pass1;
      repeat simplify_pass2.
    - unfold preincr, compose, incr; cbn.
      rewrite pair_equal_spec.
      change (?m ● ?x) with (m + x)%nat.
      lia.
    - rewrite preincr_preincr.
      intro hyp.
      eapply IHt.
      2: eauto.
      change (?m ● ?x) with (m + x)%nat.
      lia.
    - intros [hyp|hyp]; eauto.
  Qed.

  (*
  Lemma term_ind2_alt : forall (t : term LN) (l : LN) (n : nat) (X : typ),
      (n, l) ∈d (λ X t) = ((n - 1, l) ∈d t /\ n <> 0).
  Proof.
    intros.
    propext.
    - intro.
      specialize (term_ind2_nZ2 t l H).
      intro. destruct n.
      + false.
      + replace (S n - 1) with n by lia.
        apply term_ind2 in H.
    do 2 rewrite ind_to_foldMapd.
    simplify.
    simplify.
    simplify.
    simplify.
    simplify.
    simplify.
    simplify.
    simplify.
    simplify.
                  .

    - intro. destruct H as [H H'].
      destruct n.
      + false.
      + rewrite <- eq_pair_preincr.
        replace (S n - 1) with n in H by lia.
        assumption.
  Qed.
  *)

  Lemma term_ind3 : forall (t1 t2 : term LN) (n : nat) (l : LN),
      (n, l) ∈d ([t1]@[t2]) <-> (n, l) ∈d t1 \/ (n, l) ∈d t2.
  Proof.
    simplify.
  Qed.

End term_ind_rewrite.

(** ** Rewriting lemmas for <<open>> *)
(******************************************************************************)
Lemma open_term_rw2: forall (t1 t2: term LN) u,
    open u (app t1 t2) =
      app (open u t1) (open u t2).
Proof.
  simplify.
Qed.

Lemma open_term_rw3: forall τ (t: term LN) u,
    open u (λ τ t) =
      λ τ (bindd (open_loc u ⦿ 1) t).
Proof.
  simplify.
Qed.

(** ** Rewriting lemmas for <<subst>> *)
(******************************************************************************)
Lemma subst_term_rw2: forall (t1 t2: term LN) x u,
    subst x u (app t1 t2) =
      app (subst x u t1) (subst x u t2).
Proof.
  simplify.
Qed.

Lemma subst_term_rw3: forall τ (t: term LN) x u,
    subst x u (λ τ t) =
      λ τ (subst x u t).
Proof.
  simplify.
Qed.

(** ** Rewriting lemmas for <<locally_closed>> *)
(******************************************************************************)
Theorem term_lc_gap11 : forall (n : nat) (m : nat),
    locally_closed_gap m (tvar (Bd n)) <-> n < m.
Proof.
  simplify.
Qed.

Theorem term_lc_gap12 : forall (x : atom) (m : nat),
    locally_closed_gap m (tvar (Fr x)) <-> True.
Proof.
  simplify.
Qed.

Theorem term_lc_gap2 : forall (X : typ) (t : term LN) (m : nat),
    locally_closed_gap m (lam X t) <-> locally_closed_gap (S m) t.
Proof.
  simplify.
Qed.

Theorem term_lc_gap3 : forall (t1 t2 : term LN) (m : nat),
    locally_closed_gap m ([t1]@[t2]) <->
      locally_closed_gap m t1 /\ locally_closed_gap m t2.
Proof.
  simplify.
Qed.

Theorem term_lc11 : forall (n : nat),
    locally_closed (tvar (Bd n)) <-> False.
Proof.
  simplify.
Qed.

Theorem term_lc12 : forall (x : atom),
    locally_closed (tvar (Fr x)) <-> True.
Proof.
  simplify.
Qed.

Theorem term_lc2 : forall (X : typ) (t : term LN),
    locally_closed (lam X t) <-> locally_closed_gap 1 t.
Proof.
  simplify.
Qed.

Theorem term_lc3 : forall (t1 t2 : term LN),
    locally_closed ([t1]@[t2]) <-> locally_closed t1 /\ locally_closed t2.
Proof.
  simplify.
Qed.
