From Tealeaves Require Export
  Examples.STLC.Syntax
  Simplification.Tests.Support.

Import STLC.Syntax.TermNotations.

(** * Simplification tests for derived operations *)
(******************************************************************************)

(** ** Rewriting lemmas for <<mapdReduce>> *)
(******************************************************************************)
Section term_mapdReduce_rewrite.

  Context {A M : Type} (f : nat * A -> M) `{Monoid M}.

  Lemma term_mapdReduce1 : forall (a : A),
      mapdReduce f (tvar a) = f (Ƶ, a).
  Proof.
    intros. simplify_mapdReduce. reflexivity.
  Qed.

  Lemma term_mapdReduce2 : forall X (t : Lam A),
      mapdReduce f (λ X t) = mapdReduce (f ⦿ 1) t.
  Proof.
    intros. simplify_mapdReduce. reflexivity.
  Qed.

  Lemma term_mapdReduce3 : forall (t1 t2 : Lam A),
      mapdReduce f (⟨t1⟩ (t2)) = mapdReduce f t1 ● mapdReduce f t2.
  Proof.
    intros. simplify_mapdReduce. reflexivity.
  Qed.

End term_mapdReduce_rewrite.

(** ** Rewriting lemmas for <<∈d>> *)
(******************************************************************************)
Section term_ind_rewrite.

  Lemma term_ind1 : forall (l1 l2 : LN) (n : nat),
      (n, l1) ∈d (tvar l2) <-> (n = Ƶ /\ l1 = l2).
  Proof.
    intros.
    simplify_LN.
    conclude.
  Qed.

  Lemma term_ind2 : forall (t : term) (l : LN) (n : nat) (X : typ),
      (n, l) ∈d t = (S n, l) ∈d (λ X t).
  Proof.
    intros.
    simplify_LN.
    conclude.
  Qed.

  Lemma term_ind2_nZ : forall (t : term) (l : LN) (n : nat) (X : typ),
      (n, l) ∈d (λ X t) -> n <> 0.
  Proof.
    introv.
    destruct n.
    - simplify_LN.
      rewrite exists_false_false.
      easy.
    - simplify_LN.
      easy.
  Qed.

  (* TODO: This is a good example for improving simplify execution times. *)
  Lemma term_ind3 : forall (t1 t2 : term) (n : nat) (l : LN),
      (n, l) ∈d (⟨t1⟩ (t2)) <-> (n, l) ∈d t1 \/ (n, l) ∈d t2.
  Proof.
    intros.
    simplify_LN.
    conclude.
  Qed.

End term_ind_rewrite.

(** ** Rewriting lemmas for <<mapReduce>> *)
(******************************************************************************)
Section term_mapReduce_rewrite.

  Context {A M : Type} (f : A -> M) `{Monoid M}.

  Lemma term_mapReduce1 : forall (a : A),
      mapReduce f (tvar a) = f a.
  Proof.
    intros.
    simplify_LN.
    conclude.
  Qed.

  Lemma term_mapReduce2 : forall X (t : Lam A),
      mapReduce f (λ X t) = mapReduce f t.
  Proof.
    intros.
    simplify_LN.
    conclude.
  Qed.

  Lemma term_mapReduce3 : forall (t1 t2 : Lam A),
      mapReduce f (⟨t1⟩ (t2)) = mapReduce f t1 ● mapReduce f t2.
  Proof.
    intros.
    simplify_LN.
    conclude.
  Qed.

End term_mapReduce_rewrite.

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
    simplify_LN.
    reflexivity.
  Qed.

  Lemma tolist_term_rw2: forall (X: typ) (t: term),
      tolist (lam X t) = tolist t.
  Proof.
    intros.
    simplify_LN.
    conclude.
  Qed.

  Lemma tolist_term_rw3: forall (t1 t2: term),
      tolist (app t1 t2) = tolist t1 ++ tolist t2.
  Proof.
    intros.
    simplify_LN.
    conclude.
  Qed.

  Lemma toset_tvar_rw1: forall (x: A),
      tosubset (tvar x) = {{x}}.
  Proof.
    intros.
    simplify_LN.
    fixme.
  Qed.

  Lemma toset_term_rw2: forall (X: typ) (t: term),
      tosubset (lam X t) = tosubset t.
  Proof.
    intros.
    simplify_LN.
    conclude.
  Qed.

  Lemma toset_term_rw3: forall (t1 t2: term),
      tosubset (app t1 t2) = tosubset t1 ∪ tosubset t2.
  Proof.
    intros.
    simplify_LN.
    conclude.
  Qed.

  Lemma in_term_rw1: forall (x y: A),
      x ∈ tvar y = (x = y).
  Proof.
    intros.
    simplify_LN.
    simpl_subset.
    conclude.
  Qed.

  Lemma in_term_rw2: forall (y: A) (X: typ) (t: Lam A),
      y ∈ (lam X t) = y ∈ t.
  Proof.
    intros.
    simplify_LN.
    conclude.
  Qed.

  Lemma in_term_3: forall (t1 t2: Lam A) (y: A),
      y ∈ (app t1 t2) = (y ∈ t1 \/ y ∈ t2).
  Proof.
    intros.
    simplify_LN.
    conclude.
  Qed.

End term_container_rewrite.
