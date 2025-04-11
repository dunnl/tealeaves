From Tealeaves Require Export
  Classes.EqDec_eq
  Misc.NaturalNumbers.

From Tealeaves Require Import
  Theory.TraversableFunctor.

Import List.ListNotations.
Import ContainerFunctor.Notations.
Import Monoid.Notations.

(** * Transparent Atoms *)
(**********************************************************************)
Module Type AtomModule  <: UsualDecidableType.

  Parameter name: Type.

  Definition t := name.

  Parameter eq_dec: forall x y: name, {x = y} + {x <> y}.

  Parameter fresh: list name -> name.

  Parameter fresh_not_in: forall l, ~ fresh l ∈ l.

  Parameter freshen: list name -> name -> name.

  Parameter freshen_spec1: forall (l: list name) (n: name),
      ~ (n ∈ l) -> freshen l n = n.

  Parameter freshen_spec2: forall (l: list name) (n: name),
      ~ freshen l n ∈ l.

  Parameter nat_of: name -> nat.

  #[export] Hint Resolve eq_dec: core.

  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

End AtomModule.

(** * Transparent Atoms Implementation Support *)
(**********************************************************************)

(*
(* Test if x is an element of l, returning a boolean *)
Fixpoint list_in (x: nat) (l: list nat): bool :=
  match l with
  | nil => false
  | y :: rest => (x ==b y) || list_in x rest
  end.
 *)

(** ** Least Strict Upper Bound of a [list] *)
(**********************************************************************)
(** Return one greater than the greatest element in a list *)
Definition Smax (l: list nat): nat :=
  S (foldMap (op := Monoid_op_max) (unit := Monoid_unit_max) id l).

(** <<Smax l>> is greater than every element *)
Lemma Smax_gt: forall l,
  forall (a: nat), a ∈ l -> a < Smax l.
Proof.
  intros.
  induction l.
  - inversion H.
  - rewrite element_of_list_cons in H.
    unfold Smax.
    rewrite foldMap_eq_foldMap_list.
    rewrite foldMap_list_cons.
    unfold transparent tcs.
    rewrite <- foldMap_eq_foldMap_list.
    unfold id.
    destruct H as [Case1 | Case2].
    + subst.
      lia.
    + apply IHl in Case2.
      rewrite PeanoNat.Nat.succ_max_distr.
      change ((S (foldMap (fun x: nat => x) l))) with (Smax l).
      lia.
Qed.

(** <<Smax l>> is not the list *)
Lemma Smax_not_in: forall l,
    ~ Smax l ∈ l.
Proof.
  intros.
  intro contra.
  apply Smax_gt in contra.
  lia.
Qed.

(** ** Testing Membership in a [list] *)
(**********************************************************************)
Fixpoint nat_inb (x: nat) (l: list nat): bool :=
  match l with
  | nil => false
  | y :: rest => (if x == y then true else false) || nat_inb x rest
  end.

Definition nat_freshb (x: nat) (l: list nat): bool :=
  negb (nat_inb x l).

Lemma nat_inb_iff: forall x l,
    nat_inb x l = true <-> x ∈ l.
Proof.
  intros. induction l.
  - cbn. intuition.
  - cbn.
    rewrite <- IHl.
    clear IHl.
    destruct (nat_inb x l).
    + rewrite Bool.orb_true_r. intuition.
    +  rewrite Bool.orb_false_r.
       destruct_eq_args x a; intuition.
Qed.

Corollary nat_inb_iff_false: forall x l,
    nat_inb x l = false <-> ~ (x ∈ l).
Proof.
  intros.
  rewrite <- nat_inb_iff.
  destruct (nat_inb x l);
    intuition.
Qed.

Corollary nat_freshb_iff: forall x l,
    nat_freshb x l = true <-> ~ (x ∈ l).
Proof.
  intros.
  unfold nat_freshb.
  remember (nat_inb x l).
  symmetry in Heqb.
  destruct b.
  - rewrite nat_inb_iff in Heqb.
    intuition.
  - rewrite nat_inb_iff_false in Heqb.
    intuition.
Qed.

Corollary nat_freshb_false_iff: forall x l,
    nat_freshb x l = false <-> (x ∈ l).
Proof.
  intros.
  unfold nat_freshb.
  remember (nat_inb x l).
  symmetry in Heqb.
  destruct b.
  - rewrite nat_inb_iff in Heqb.
    intuition.
  - rewrite nat_inb_iff_false in Heqb.
    intuition.
Qed.

(** ** Computing Maximum Element Not in [list] *)
(**********************************************************************)

(* Compute the maximum element not in a list. Computed slightly funny to be structurally recursive.
   We start with an element known not to be in the list. Then we test all smaller numbers to see if they are elements,  and track the smallest value known not to form an element as <<candidate>>
   <<current min>> is the smallest value *)

Fixpoint min_fresh_rec
  (gas: nat) (candidate: nat)
  (l: list nat): nat :=
  match gas with
  | 0 => if nat_freshb 0 l
        then 0
        else candidate
  | S g =>
      if nat_freshb g l
      then min_fresh_rec g g l
      else min_fresh_rec g candidate l
  end.

Lemma min_fresh_rec_invariant: forall gas candidate l,
    ~ (candidate ∈ l) ->
    ~ min_fresh_rec gas candidate l ∈ l.
Proof.
  intros.
  generalize dependent candidate.
  induction gas; intros.
  - cbn.
    remember (nat_freshb 0 l).
    symmetry in Heqb.
    destruct b.
    + apply nat_freshb_iff in Heqb.
      auto.
    + apply nat_freshb_false_iff in Heqb.
      assumption.
  - cbn.
    remember (nat_freshb gas l).
    symmetry in Heqb.
    destruct b.
    + apply IHgas.
      apply nat_freshb_iff in Heqb.
      assumption.
    + apply IHgas.
      assumption.
Qed.

Definition min_fresh (l: list nat): nat :=
  min_fresh_rec (Smax l) (Smax l) l.

Definition freshen (l: list nat) (n: nat): nat :=
  if nat_freshb n l then n
  else min_fresh l.

Lemma freshen_spec: forall (l: list nat) (n: nat),
    {~ n ∈ l /\ freshen l n = n} + {n ∈ l /\ freshen l n = min_fresh l}.
Proof.
  intros.
  remember (nat_freshb n l).
  symmetry in Heqb.
  unfold freshen.
  rewrite Heqb.
  destruct b.
  - left.
    apply nat_freshb_iff in Heqb; auto.
  - right.
    apply nat_freshb_false_iff in Heqb; auto.
Qed.

Compute min_fresh_rec 100 5 [0; 1; 2].
Compute min_fresh_rec 100 5 [0; 1; 3; 4].
Compute min_fresh_rec 100 5 [1; 2; 4; 6; 8].
Compute min_fresh_rec 100 5 [0; 1; 2; 4; 6; 8].

Compute min_fresh [].
Compute min_fresh [0].
Compute min_fresh [0; 1].
Compute min_fresh [0; 2].

Compute freshen [0; 2] 2.

Compute freshen [0; 2] 4.

(** ** Transparent Atoms Implementation *)
(**********************************************************************)
Module Name <: AtomModule.

  Definition name: Type := nat.
  Definition t := name.

  Definition eq_dec := PeanoNat.Nat.eq_dec.

  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

  Definition fresh := min_fresh.

  Lemma fresh_not_in: forall l, ~ fresh l ∈ l.
  Proof.
    intro l.
    unfold fresh.
    apply min_fresh_rec_invariant.
    apply Smax_not_in.
  Qed.

  Definition freshen := freshen.

  Lemma freshen_spec1: forall (l: list name) (n: name),
      ~ (n ∈ l) -> freshen l n = n.
  Proof.
    intros.
    destruct (freshen_spec l n).
    - intuition.
    - intuition.
  Qed.

  Lemma freshen_spec2: forall (l: list name) (n: name),
      ~ freshen l n ∈ l.
  Proof.
    intros.
    unfold freshen.
    destruct (freshen_spec l n).
    - destruct a as [H1 H2].
      rewrite H2; auto.
    - destruct a as [H1 H2].
      rewrite H2.
      apply min_fresh_rec_invariant.
      apply Smax_not_in.
  Qed.

  Definition nat_of: name -> nat := fun x => x.

End Name.

(** ** Shorthands and notations *)
(**********************************************************************)
Notation name := Name.name.
Notation atom := Name.name.
Notation fresh := Name.fresh.
Notation fresh_not_in := Name.fresh_not_in.

(* Automatically unfold Name.eq *)
#[global] Arguments Name.eq /.

#[export] Instance EqDec_name: @EqDec name eq eq_equivalence := Name.eq_dec.
