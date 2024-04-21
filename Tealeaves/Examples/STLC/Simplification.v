From Tealeaves Require Export
  Examples.STLC.Syntax.

Import STLC.Syntax.Notations.

#[local] Open Scope tealeaves_scope.

Ltac assert_identical :=
    match goal with
    | |- ?x = ?x =>
        debug "Both sides identical:";
        print_goal
    | |- _ =>
        debug "LHS and RHS not syntactically identical:";
        print_goal;
        fail
    end.

Ltac assert_different :=
  assert_fails (idtac; assert_identical).
(* idtac prevents Ltac from evaluating assert_identical right here *)

Ltac conclude := now assert_identical.
Ltac reject := now assert_different.

(** * Simplification tests for categorical operations *)
(******************************************************************************)
Section categorical.

  Context (G: Type -> Type) `{Mult G} `{Map G} `{Pure G}
    `{Applicative G} (v1 v2: Type).

  Implicit Types (t body: Lam v1) (v: v1) (τ: typ).
  Generalizable Variables t v τ body.

  Section binddt.

    (* Interestingly, these goals won't be accepted even if we add
       Generalizable Variable f.
       Implicit Type (f: nat * v1 -> G (Lam v2)).
       I think because binddt is typechecked
       before the universal generalization of f
       affects anything *)
    Context (f: nat * v1 -> G (Lam v2)).

    Ltac test := intros; assert_different; simplify_binddt; conclude.
    Ltac test_fail := intros; simplify_binddt; reject.

    Goal `(binddt f (ret v) = f (Ƶ, v)).
    Proof.
      intros.
      assert_different.
      simplify_match_binddt_ret.
      conclude.
    Qed.

    Goal `(binddt f (ret v) = f (0, v)).
    Proof.
      intros.
      simplify_match_binddt_ret.
      reject.
    Qed.

    Goal `(binddt f (ret v) = f (Ƶ, v)).
    Proof.
      intros.
      simplify_binddt_core.
      reject.
    Qed.

    Goal `(binddt f (ret v) = f (0, v)).
    Proof.
      intros.
      simplify_binddt_core.
      conclude.
    Qed.

    Goal `(binddt f (ret v) = f (Ƶ, v)).
    Proof.
      intros.
      simplify_binddt.
      conclude.
    Qed.

    Goal `(binddt f (ret v) = f (0, v)).
    Proof.
      intros.
      simplify_binddt.
      reject.
    Qed.

    Goal `(binddt f (ret v) = binddt f (tvar v)).
    Proof.
      intros.
      assert_different.
      normalize_all_binddt_ret.
      conclude.
    Qed.

    Lemma lam_binddt_11:
      `(binddt f (ret v) = f (0, v)).
    Proof.
      try test.
      intros. cbn_binddt.
      conclude.
    Qed.

    Lemma lam_binddt_2:
      `(binddt f (app t1 t2) = pure (app (V:=v2)) <⋆> binddt f t1 <⋆> binddt f t2).
    Proof.
      test.
    Qed.

    Lemma lam_binddt_3:
      `(binddt f (lam τ body) = pure (lam τ) <⋆> binddt (f ⦿ 1) body).
    Proof.
      test.
    Qed.

  End binddt.

  Section bindd.

    Context (f: nat * v1 -> Lam v2).

    Goal `(bindd f (ret v) = f (Ƶ, v)).
    Proof.
      intros.
      simplify_bindd.
      conclude.
    Qed.

    Goal `(bindd f (tvar v) = f (Ƶ, v)).
    Proof.
      intros.
      simplify_bindd.
      conclude.
    Qed.

    Goal `(bindd f (ret v) = bindd f (tvar v)).
    Proof.
      dup. {
        intros.
        rewrite bindd_to_binddt.
        simplify_binddt.
        simplify_binddt.
        conclude.
      }
      intros.
      simplify_bindd.
      simplify_bindd.
      conclude.
    Qed.

    Lemma lam_bindd_11:
      `(bindd f (ret v) = f (Ƶ, v)).
    Proof.
      intros.
      simplify_bindd.
      conclude.
    Qed.

    Lemma lam_bindd_2:
      `(bindd f (app t1 t2) = app (V:=v2) (bindd f t1) (bindd f t2)).
    Proof.
      intros.
      simplify_bindd.
      conclude.
    Qed.

    Lemma lam_bindd_3:
      `(bindd f (lam τ body) = lam τ (bindd (f ⦿ 1) body)).
    Proof.
      intros.
      simplify_bindd.
      conclude.
    Qed.

  End bindd.

End categorical.


(** ** Rewriting lemmas for <<tolist>>, <<toset>>, <<∈>> *)
(******************************************************************************)
Section term_container_rewrite.

  Variable
    (A : Type).

  Lemma tolist_tvar_rw1: forall (x: A),
      tolist (tvar x) = [x].
  Proof.
    intros.
    unfold tolist.
    unfold Tolist_Traverse.
    simplify.
    Print tolist.
    reflexivity.
  Qed.

  Lemma tolist_term_rw2: forall (X: typ) (t: term),
      tolist (lam X t) = tolist t.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Lemma tolist_term_rw3: forall (t1 t2: term),
      tolist (app t1 t2) = tolist t1 ++ tolist t2.
  Proof.
    intros. simplify. reflexivity.
  Qed.
  Lemma toset_tvar_rw1: forall (x: A),
      tosubset (tvar x) = {{x}}.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Lemma toset_term_rw2: forall (X: typ) (t: term),
      tosubset (lam X t) = tosubset t.
  Proof.
    intros. simplify_tosubset. reflexivity.
  Qed.

  Lemma toset_term_rw3: forall (t1 t2: term),
      tosubset (app t1 t2) = tosubset t1 ∪ tosubset t2.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Lemma in_term_rw1: forall (x y: A),
      x ∈ tvar y <-> x = y.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Lemma in_term_rw2: forall (y: A) (X: typ) (t: Lam A),
      y ∈ (lam X t) <-> y ∈ t.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Lemma in_term_3: forall (t1 t2: Lam A) (y: A),
      y ∈ (app t1 t2) <-> y ∈ t1 \/ y ∈ t2.
  Proof.
    intros. simplify. reflexivity.
  Qed.

End term_container_rewrite.

(** ** Rewriting lemmas for <<foldMapd>> *)
(******************************************************************************)
Section term_foldMapd_rewrite.

  Context {A M : Type} (f : nat * A -> M) `{Monoid M}.

  Lemma term_foldMapd1 : forall (a : A),
      foldMapd f (tvar a) = f (Ƶ, a).
  Proof.
    intros. simplify_foldMapd. reflexivity.
  Qed.

  Lemma term_foldMapd2 : forall X (t : Lam A),
      foldMapd f (λ X t) = foldMapd (f ⦿ 1) t.
  Proof.
    intros. simplify_foldMapd. reflexivity.
  Qed.

  Lemma term_foldMapd3 : forall (t1 t2 : Lam A),
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

  Lemma term_ind2 : forall (t : term) (l : LN) (n : nat) (X : typ),
      (n, l) ∈d t = (S n, l) ∈d (λ X t).
  Proof.
    intros. simplify_element_ctx_of. reflexivity.
  Qed.

  Lemma term_ind2_nZ : forall (t : term) (l : LN) (n : nat) (X : typ),
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

  (* TODO: This is a good example for improving simplify execution times. *)
  Lemma term_ind3 : forall (t1 t2 : term) (n : nat) (l : LN),
      (n, l) ∈d (⟨t1⟩ (t2)) <-> (n, l) ∈d t1 \/ (n, l) ∈d t2.
  Proof.
    intros. simplify. reflexivity.
  Qed.

End term_ind_rewrite.

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
