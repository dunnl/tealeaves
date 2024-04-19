From Tealeaves Require Export
  Examples.STLC.Syntax.

Import STLC.Syntax.Notations.

#[local] Open Scope tealeaves_scope.

(** ** Rewriting lemmas for <<LC>> *)
(******************************************************************************)
Theorem term_lcn11 : forall (n : nat) (m : nat),
    LCn m (tvar (Bd n)) <-> n < m.
Proof.
  intros. simplify_LC. reflexivity.
Qed.

Theorem term_lcn12 : forall (x : atom) (m : nat),
    LCn m (tvar (Fr x)) <-> True.
Proof.
  intros. simplify_LN. reflexivity.
Qed.

Theorem term_lcn2 : forall (X : typ) (t : term LN) (m : nat),
    LCn m (lam X t) <-> LCn (S m) t.
Proof.
  intros. simplify_LN. reflexivity.
Qed.

Theorem term_lcn3 : forall (t1 t2 : term LN) (m : nat),
    LCn m (⟨t1⟩(t2)) <->
      LCn m t1 /\ LCn m t2.
Proof.
  intros. simplify_LN. reflexivity.
Qed.

Theorem term_lc11 : forall (n : nat),
    LC (tvar (Bd n)) <-> False.
Proof.
  intros. simplify_LN. lia.
Qed.

Theorem term_lc12 : forall (x : atom),
    LC (tvar (Fr x)) <-> True.
Proof.
  intros. simplify_LN. reflexivity.
Qed.

Theorem term_lc2 : forall (X : typ) (t : term LN),
    LC (lam X t) <-> LCn 1 t.
Proof.
  intros. simplify_LN. reflexivity.
Qed.

Theorem term_lc3 : forall (t1 t2 : term LN),
    LC (⟨t1⟩ (t2)) <-> LC t1 /\ LC t2.
Proof.
  intros. simplify_LN. reflexivity.
Qed.

(** ** Rewriting lemmas for <<tolist>>, <<toset>>, <<∈>> *)
(******************************************************************************)
Section term_container_rewrite.

  Variable
    (A : Type).

  Lemma tolist_tvar_rw1: forall (x: A),
      tolist (tvar x) = [x].
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Lemma tolist_term_rw2: forall (X: typ) (t: term A),
      tolist (lam X t) = tolist t.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Lemma tolist_term_rw3: forall (t1 t2: term A),
      tolist (app t1 t2) = tolist t1 ++ tolist t2.
  Proof.
    intros. simplify. reflexivity.
  Qed.
  Lemma toset_tvar_rw1: forall (x: A),
      tosubset (tvar x) = {{x}}.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Lemma toset_term_rw2: forall (X: typ) (t: term A),
      tosubset (lam X t) = tosubset t.
  Proof.
    intros. simplify_tosubset. reflexivity.
  Qed.

  Lemma toset_term_rw3: forall (t1 t2: term A),
      tosubset (app t1 t2) = tosubset t1 ∪ tosubset t2.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Lemma in_term_rw1: forall (x y: A),
      x ∈ tvar y <-> x = y.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Lemma in_term_rw2: forall (y: A) (X: typ) (t: term A),
      y ∈ (lam X t) <-> y ∈ t.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Lemma in_term_3: forall (t1 t2: term A) (y: A),
      y ∈ (app t1 t2) <-> y ∈ t1 \/ y ∈ t2.
  Proof.
    intros. simplify. reflexivity.
  Qed.

End term_container_rewrite.

(** ** Rewriting lemmas for <<free>>, <<freeset>> *)
(******************************************************************************)
Section term_free_rewrite.

  Variable (A : Type).

  Definition term_free11 : forall (b : nat),
      free (tvar (Bd b)) = [].
  Proof.
    intros. simplify_LN. reflexivity.
  Qed.

  Definition term_in_free11 : forall (b : nat) (x : atom),
      x ∈ free (tvar (Bd b)) <-> False.
  Proof.
    intros. simplify_LN. reflexivity.
  Qed.

  Definition term_free12 : forall (y : atom),
      free (tvar (Fr y)) = [y].
  Proof.
    intros. simplify_LN. reflexivity.
  Qed.

  Definition term_in_free12 : forall (y : atom) (x : atom),
      x ∈ free (tvar (Fr y)) <-> x = y.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Definition term_free2 : forall (t : term LN) (X : typ),
      free (lam X t) = free t.
  Proof.
    intros. simplify_LN. reflexivity.
  Qed.

  Definition term_in_free2 : forall (x : atom) (t : term LN) (X : typ),
      x ∈ free (lam X t) <-> x ∈ free t.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Definition term_free3 : forall (x : atom) (t1 t2 : term LN),
      free (app t1 t2) = free t1 ++ free t2.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Definition term_in_free3 : forall (x : atom) (t1 t2 : term LN),
      x ∈ free (app t1 t2) <-> x ∈ free t1 \/ x ∈ free t2.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Definition term_in_FV11 : forall (b : nat) (x : atom),
      x `in` FV (tvar (Bd b)) <-> False.
  Proof.
    intros. simplify_FV. reflexivity.
  Qed.

  Definition term_in_FV12 : forall (y : atom) (x : atom),
      AtomSet.In x (FV (tvar (Fr y))) <-> x = y.
  Proof.
    intros. simplify_FV. reflexivity.
  Qed.

  Lemma term_in_FV2 : forall (x : atom) (t : term LN) (X : typ),
      AtomSet.In x (FV (lam X t)) <-> AtomSet.In x (FV t).
  Proof.
    intros. simplify_FV. reflexivity.
  Qed.

  Lemma term_in_FV3 : forall (x : atom) (t1 t2 : term LN),
      AtomSet.In x (FV (app t1 t2)) <->
        AtomSet.In x (FV t1) \/ AtomSet.In x (FV t2).
  Proof.
    intros. simplify_FV. reflexivity.
  Qed.

  Open Scope set_scope.

  Lemma term_FV11 : forall (b : nat) (x : atom),
      FV (tvar (Bd b)) [=] ∅.
  Proof.
    intros. simplify_FV. fsetdec.
  Qed.

  Lemma term_FV12 : forall (y : atom),
      FV (tvar (Fr y)) [=] {{ y }}.
  Proof.
    intros. simplify_FV. fsetdec.
  Qed.

  Lemma term_FV2 : forall (t : term LN) (X : typ),
      FV (lam X t) [=] FV t.
  Proof.
    intros. simplify_FV. fsetdec.
  Qed.

  Lemma term_FV3 : forall (t1 t2 : term LN),
      FV (app t1 t2) [=] FV t1 ∪ FV t2.
  Proof.
    intros. simplify_FV. fsetdec.
  Qed.

End term_free_rewrite.

(** ** Rewriting lemmas for <<foldMapd>> *)
(******************************************************************************)
Section term_foldMapd_rewrite.

  Context {A M : Type} (f : nat * A -> M) `{Monoid M}.

  Lemma term_foldMapd1 : forall (a : A),
      foldMapd f (tvar a) = f (Ƶ, a).
  Proof.
    intros. simplify_foldMapd. reflexivity.
  Qed.

  Lemma term_foldMapd2 : forall X (t : term A),
      foldMapd f (λ X t) = foldMapd (f ⦿ 1) t.
  Proof.
    intros. simplify_foldMapd. reflexivity.
  Qed.

  Lemma term_foldMapd3 : forall (t1 t2 : term A),
      foldMapd f (⟨t1⟩ (t2)) = foldMapd f t1 ● foldMapd f t2.
  Proof.
    intros. simplify_foldMapd. reflexivity.
  Qed.

End term_foldMapd_rewrite.

(** ** Rewriting lemmas for <<∈d>> *)
(******************************************************************************)
Section term_ind_rewrite.

  Lemma term_ind1 : forall (l1 l2 : LN) (n : nat),
      (n, l1) ∈d (tvar l2) <-> n = Ƶ /\ l1 = l2.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Ltac print_goal := match goal with
  | |- ?g => idtac g (* prints goal *)
  end.

  Lemma term_ind2 : forall (t : term LN) (l : LN) (n : nat) (X : typ),
      (n, l) ∈d t = (S n, l) ∈d (λ X t).
  Proof.
    intros. simplify_element_ctx_of. reflexivity.
  Qed.

  Lemma term_ind2_nZ : forall (t : term LN) (l : LN) (n : nat) (X : typ),
      (n, l) ∈d (λ X t) -> n <> 0.
  Proof.
    introv.
    destruct n.
    - simplify_element_ctx_of.
      rewrite exists_false_false.
      easy.
    - simplify_element_ctx_of.
      easy.
  Qed.

  Lemma term_ind3 : forall (t1 t2 : term LN) (n : nat) (l : LN),
      (n, l) ∈d (⟨t1⟩ (t2)) <-> (n, l) ∈d t1 \/ (n, l) ∈d t2.
  Proof.
    intros. simplify. reflexivity.
  Qed.

End term_ind_rewrite.

(** ** Rewriting lemmas for <<open>> *)
(******************************************************************************)
Lemma open_term_rw2: forall (t1 t2: term LN) u,
    open u (app t1 t2) = app (open u t1) (open u t2).
Proof.
  intros. simplify_open. reflexivity.
Qed.

Lemma open_term_rw3: forall τ (t: term LN) u,
    open u (λ τ t) = λ τ (bindd (open_loc u ⦿ 1) t).
Proof.
  intros. simplify_open. reflexivity.
Qed.

(** ** Rewriting lemmas for <<subst>> *)
(******************************************************************************)
Lemma subst_term_rw2: forall (t1 t2: term LN) x u,
    subst x u (app t1 t2) =
      app (subst x u t1) (subst x u t2).
Proof.
  intros. simplify_subst. reflexivity.
Qed.

Lemma subst_term_rw3: forall τ (t: term LN) x u,
    subst x u (λ τ t) =
      λ τ (subst x u t).
Proof.
  intros. simplify_subst. reflexivity.
Qed.
