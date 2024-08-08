From Tealeaves Require Export
  Examples.STLC.Syntax
  Simplification.Tests.Support.

Import STLC.Syntax.TermNotations.

(** ** Rewriting lemmas for <<LC>> *)
(******************************************************************************)
Theorem term_lcn11 : forall (n : nat) (m : nat),
    LCn m (tvar (Bd n)) <-> n < m.
Proof.
  intros. simplify_LN. reflexivity.
Qed.

Theorem term_lcn12 : forall (x : atom) (m : nat),
    LCn m (tvar (Fr x)) <-> True.
Proof.
  intros. simplify_LN. reflexivity.
Qed.

Theorem term_lcn2 : forall (X : typ) (t : term) (m : nat),
    LCn m (lam X t) <-> LCn (S m) t.
Proof.
  intros. simplify_LN. reflexivity.
Qed.

Theorem term_lcn3 : forall (t1 t2 : term) (m : nat),
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

Theorem term_lc2 : forall (X : typ) (t : term),
    LC (lam X t) <-> LCn 1 t.
Proof.
  intros. simplify_LN. reflexivity.
Qed.

Theorem term_lc3 : forall (t1 t2 : term),
    LC (⟨t1⟩ (t2)) <-> LC t1 /\ LC t2.
Proof.
  intros. simplify_LN. reflexivity.
Qed.

(** ** Rewriting lemmas for <<free>>, <<freeset>> *)
(******************************************************************************)
Section term_free_rewrite.

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

  Definition term_free2 : forall (t : term) (X : typ),
      free (lam X t) = free t.
  Proof.
    intros. simplify_LN. reflexivity.
  Qed.

  Definition term_in_free2 : forall (x : atom) (t : term) (X : typ),
      x ∈ free (lam X t) <-> x ∈ free t.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Definition term_free3 : forall (x : atom) (t1 t2 : term),
      free (app t1 t2) = free t1 ++ free t2.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Definition term_in_free3 : forall (x : atom) (t1 t2 : term),
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

  Lemma term_in_FV2 : forall (x : atom) (t : term) (X : typ),
      AtomSet.In x (FV (lam X t)) <-> AtomSet.In x (FV t).
  Proof.
    intros. simplify_FV. reflexivity.
  Qed.

  Lemma term_in_FV3 : forall (x : atom) (t1 t2 : term),
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

  Lemma term_FV2 : forall (t : term) (X : typ),
      FV (lam X t) [=] FV t.
  Proof.
    intros. simplify_FV. fsetdec.
  Qed.

  Lemma term_FV3 : forall (t1 t2 : term),
      FV (app t1 t2) [=] FV t1 ∪ FV t2.
  Proof.
    intros. simplify_FV. fsetdec.
  Qed.

End term_free_rewrite.


(** ** Rewriting lemmas for <<open>> *)
(******************************************************************************)
Lemma open_term_rw1: forall (v: LN) (u: term),
    open u (tvar v) = open_loc u (0, v).
Proof.
  intros. simplify_open. reflexivity.
Qed.

Lemma open_term_rw2: forall (t1 t2: term) u,
    open u (app t1 t2) = app (open u t1) (open u t2).
Proof.
  intros. simplify_open. reflexivity.
Qed.

Lemma open_term_rw3: forall τ (t: term) u,
    open u (λ τ t) = λ τ (bindd (open_loc u ⦿ 1) t).
Proof.
  intros. simplify_open. reflexivity.
Qed.

(** ** Rewriting lemmas for <<subst>> *)
(******************************************************************************)
Lemma subst_term_rw1: forall (v: LN) x u,
    subst x u (tvar v) = subst_loc x u v.
Proof.
  intros.
  simplify_subst.
  conclude.
Qed.

Lemma subst_term_rw2: forall (t1 t2: term) x u,
    subst x u (app t1 t2) =
      app (subst x u t1) (subst x u t2).
Proof.
  intros.
  simplify_subst.
  conclude.
Qed.

Lemma subst_term_rw3: forall τ (t: term) x u,
    subst x u (λ τ t) =
      λ τ (subst x u t).
Proof.
  intros.
  simplify_subst.
  conclude.
Qed.

Goal forall (v: LN) x u,
    v = Fr x ->
    subst x u (tvar v) = u.
Proof.
  intros.
  simplify_subst.
  conclude.
Qed.

Goal forall (v: LN) x u,
    v <> Fr x ->
    subst x u (tvar v) = tvar v.
Proof.
  intros.
  simplify_subst.
  conclude.
Qed.

Goal forall y x u,
    x = y ->
    subst x u (tvar (Fr y)) = u.
Proof.
  intros.
  simplify_subst.
  conclude.
Qed.

Goal forall y x u,
    x <> y ->
    subst x u (tvar (Fr y)) = tvar (Fr y).
Proof.
  intros.
  simplify_subst.
  conclude.
Qed.

Goal forall v y x u,
    y <> x ->
    v = x ->
    subst x u (app (ret (Fr v)) (ret (Fr y))) = app u (ret (Fr v)).
Proof.
  intros.
  rewrite subst_to_bind.
  rewrite bind_to_bindd.
  rewrite bindd_to_binddt.
  cbn [binddt Binddt_STLC binddt_Lam].
  cbn [binddt Binddt_STLC binddt_Lam].
  cbn [binddt Binddt_STLC binddt_Lam ret Return_STLC].
Abort.

Goal forall v y x u,
    y <> Fr x ->
    v = Fr x ->
    subst x u (app (tvar v) (tvar y)) = u.
Proof.
  intros.
  rewrite subst_to_bind.
  rewrite bind_to_bindd.
  rewrite bindd_to_binddt.
  cbn [binddt Binddt_STLC binddt_Lam].
Abort.
