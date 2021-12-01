From Tealeaves Require Import
     Util.Prelude
     Singlesorted.Classes.Monoid
     Singlesorted.Classes.SetlikeFunctor
     LN.Atom.

From Coq Require
     MSets.MSets.

(* set up notations *)
Import List.ListNotations.
Open Scope list_scope.
Import SetlikeFunctor.Notations.
Open Scope tealeaves_scope.

(** * Defining <<AtomSet>> via Coq MSets library *)
(******************************************************************************)
Module AtomSet <: Coq.MSets.MSetInterface.WSets :=
  Coq.MSets.MSetWeakList.Make Atom.

Module AtomSetProperties :=
  Coq.MSets.MSetProperties.WPropertiesOn Atom AtomSet.

Declare Scope set_scope.
Delimit Scope set_scope with set.
Local Open Scope set_scope.

(** ** Notations for operations on <<AtomSet>> *)
(******************************************************************************)
Module Notations.

  Notation "x ∈@ S" := (AtomSet.In x S) (at level 40) : set_scope.
  Notation "s [=] t" := (AtomSet.Equal s t) (at level 70, no associativity) : set_scope.
  Notation "s ⊆ t" := (AtomSet.Subset s t) (at level 70, no associativity) : set_scope.
  Notation "s ∩ t" := (AtomSet.inter s t) (at level 60, no associativity) : set_scope.
  Notation "s \\ t" := (AtomSet.diff s t) (at level 60, no associativity) : set_scope.
  Notation "s ∪ t" := (AtomSet.union s t) (at level 61, left associativity) : set_scope.
  Notation "'elements'" := (AtomSet.elements) (at level 60, no associativity) : set_scope.
  Notation "∅" := (AtomSet.empty) : set_scope.
  Notation "{{ x }}" := (AtomSet.singleton x) : set_scope.

End Notations.

Import Notations.

Tactic Notation "fsetdec" := AtomSetProperties.Dec.fsetdec.

Lemma in_singleton_iff : forall (x : atom) (y : atom),
    y ∈@ {{ x }} <-> y = x.
Proof.
  intros. fsetdec.
Qed.

Lemma in_elements_iff : forall (s : AtomSet.t) (x : atom),
    x ∈@ s <-> x ∈ elements s.
Proof.
  intros. rewrite <- AtomSet.elements_spec1. induction (elements s).
  - cbv. split; intro H; inversion H.
  - cbn. split; intro H; inversion H.
    + subst. now left.
    + subst. destruct H.
      subst. rewrite IHl in H1. now right.
      rewrite IHl in H1. now right.
    + subst. now left.
    + right. now rewrite IHl.
Qed.

(** ** The [atoms] operation *)
(******************************************************************************)
Fixpoint atoms (l : list atom) : AtomSet.t :=
  match l with
  | nil => ∅
  | x :: xs => AtomSet.add x (atoms xs)
  end.

(** ** Rewriting rules *)
(******************************************************************************)
Lemma atoms_nil : atoms nil = ∅.
Proof.
  reflexivity.
Qed.

Lemma atoms_cons : forall (x : atom) (xs : list atom),
    atoms (x :: xs) [=] {{ x }} ∪ atoms xs.
Proof.
  intros. cbn. fsetdec.
Qed.

Lemma atoms_one : forall (x : atom),
    atoms [x] [=] {{ x }}.
Proof.
  intros. cbn. fsetdec.
Qed.

Lemma atoms_app : forall (l1 l2 : list atom),
    atoms (l1 ++ l2) [=] atoms l1 ∪ atoms l2.
Proof.
  induction l1.
  - cbn. List.simpl_list. fsetdec.
  - cbn. introv. rewrite (IHl1 l2). fsetdec.
Qed.

Create HintDb tea_rw_atoms.
Hint Rewrite atoms_nil atoms_cons atoms_one atoms_app : tea_rw_atoms.

Lemma in_atoms_nil : forall x, x ∈@ atoms nil <-> False.
Proof.
  cbn. fsetdec.
Qed.

Lemma in_atoms_cons : forall (y : atom) (x : atom) (xs : list atom),
    y ∈@ atoms (x :: xs) <-> y = x \/ y ∈@ atoms xs.
Proof.
   intros. autorewrite with tea_rw_atoms. fsetdec.
Qed.

Lemma in_atoms_one : forall (y x : atom),
    y ∈@ atoms [x] <-> y = x.
Proof.
  intros. autorewrite with tea_rw_atoms. fsetdec.
Qed.

Lemma in_atoms_app : forall (x : atom) (l1 l2 : list atom),
    x ∈@ atoms (l1 ++ l2) <-> x ∈@ atoms l1 \/ x ∈@ atoms l2.
Proof.
   intros. autorewrite with tea_rw_atoms. fsetdec.
Qed.

Hint Rewrite atoms_nil atoms_cons atoms_one atoms_app : tea_rw_atoms.
Hint Rewrite in_atoms_nil in_atoms_cons in_atoms_one in_atoms_app : tea_rw_atoms.

Lemma in_atoms_iff : forall (l : list atom) (x : atom), x ∈@ atoms l <-> x ∈ l.
Proof.
  intros.
  induction l; autorewrite with tea_rw_atoms tea_list;
    try rewrite IHl; easy.
Qed.
