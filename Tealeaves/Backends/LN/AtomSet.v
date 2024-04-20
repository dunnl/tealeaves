From Tealeaves Require Import
  Classes.Categorical.ContainerFunctor
  LN.Atom.

From Coq Require
  MSets.MSets.

Import List.ListNotations.
Import ContainerFunctor.Notations.

(** * Definition of <<AtomSet>> type *)
(******************************************************************************)
Module AtomSet <: Coq.MSets.MSetInterface.WSets :=
  Coq.MSets.MSetWeakList.Make Atom.

Module AtomSetProperties :=
  Coq.MSets.MSetProperties.WPropertiesOn Atom AtomSet.

(** ** Notations for operations on <<AtomSet>> *)
(******************************************************************************)
Declare Scope set_scope.
Delimit Scope set_scope with set.
Open Scope set_scope.

Module Notations.

  Notation "x `∈@` S" := (AtomSet.In x S) (at level 40) : set_scope.
  Notation "x `in` S" := (AtomSet.In x S) (at level 40) : set_scope.
  Notation "x `notin` S" := (~ AtomSet.In x S) (at level 40) : set_scope.
  Notation "s [=] t" := (AtomSet.Equal s t) (at level 70, no associativity) : set_scope.
  Notation "s ⊆ t" := (AtomSet.Subset s t) (at level 70, no associativity) : set_scope.
  Notation "s ∩ t" := (AtomSet.inter s t) (at level 60, no associativity) : set_scope.
  Notation "s \\ t" := (AtomSet.diff s t) (at level 60, no associativity) : set_scope.
  Notation "s ∪ t" := (AtomSet.union s t) (at level 61, left associativity) : set_scope.
  Notation "'elements'" := (AtomSet.elements) (at level 60, no associativity) : set_scope.
  Notation "∅" := (AtomSet.empty) : set_scope.
  Notation "{{ x }}" := (AtomSet.singleton x) : set_scope.

  Tactic Notation "fsetdec" := AtomSetProperties.Dec.fsetdec.

End Notations.

Import Notations.

#[global] Instance Monoid_op_atoms: @Monoid_op AtomSet.t := AtomSet.union.
#[global] Instance Monoid_unit_atoms: @Monoid_unit AtomSet.t := AtomSet.empty.
#[global] Instance Monoid_atoms: Monoid AtomSet.t.
Proof.
  constructor; unfold transparent tcs; intros.
  (* TODO: Can't use existing monoid typeclass because
     the laws only hold up to AtomSet.Equal, not propositional equality. *)
Abort.

(** ** The [atoms] operation *)
(** <<atoms>> collects a list of atoms into an <<AtomSet>>. It is
    conceptually inverse to [AtomSet.elements], but there's no
    guarantee the operations won't disturb the order*)
(******************************************************************************)
Fixpoint atoms (l : list atom) : AtomSet.t :=
  match l with
  | nil => ∅
  | x :: xs => AtomSet.add x (atoms xs)
  end.

(** ** Rewriting rules *)
(******************************************************************************)
Create HintDb tea_rw_atoms.

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

#[export] Hint Rewrite atoms_nil atoms_cons atoms_one atoms_app : tea_rw_atoms.

Lemma in_atoms_nil : forall x, x `in` atoms nil <-> False.
Proof.
  cbn. fsetdec.
Qed.

Lemma in_atoms_cons : forall (y : atom) (x : atom) (xs : list atom),
    y `in` atoms (x :: xs) <-> y = x \/ y `in` atoms xs.
Proof.
   intros. autorewrite with tea_rw_atoms. fsetdec.
Qed.

Lemma in_atoms_one : forall (y x : atom),
    y `in` atoms [x] <-> y = x.
Proof.
  intros. autorewrite with tea_rw_atoms. fsetdec.
Qed.

Lemma in_atoms_app : forall (x : atom) (l1 l2 : list atom),
    x `in` atoms (l1 ++ l2) <-> x `in` atoms l1 \/ x `in` atoms l2.
Proof.
   intros. autorewrite with tea_rw_atoms. fsetdec.
Qed.

#[export] Hint Rewrite in_atoms_nil in_atoms_cons in_atoms_one in_atoms_app : tea_rw_atoms.

Lemma in_singleton_iff : forall (x : atom) (y : atom),
    y `in` {{ x }} <-> y = x.
Proof.
  intros. fsetdec.
Qed.

Lemma in_union_iff : forall (x : atom) (s1 s2 : AtomSet.t),
    x `in` (s1 ∪ s2) <-> x `in` s1 \/ x `in` s2.
Proof.
  intros. fsetdec.
Qed.

(** ** Relating <<AtomSet.t>> and <<list atom>> *)
(******************************************************************************)
Lemma in_elements_iff : forall (s : AtomSet.t) (x : atom),
    x `in` s <-> x ∈ elements s.
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

Lemma in_atoms_iff : forall (l : list atom) (x : atom), x ∈ l <-> x `in` atoms l.
Proof.
  intros. induction l.
  - easy.
  - autorewrite with tea_rw_atoms tea_list.
    now rewrite IHl.
Qed.
