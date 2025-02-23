From Tealeaves Require Import
  Classes.EqDec_eq
  Backends.LN.Atom
  Misc.NaturalNumbers
  Theory.TraversableFunctor.

Import List.ListNotations.
Import ContainerFunctor.Notations.

(** * Transparent atoms *)
(******************************************************************************)

Module Type AtomModule  <: UsualDecidableType.

  Parameter name : Type.

  Definition t := name.

  Parameter eq_dec : forall x y : name, {x = y} + {x <> y}.

  Parameter fresh : list name -> name.

  Parameter fresh_not_in : forall l, ~ fresh l ∈ l.

  Parameter nat_of : name -> nat.

  #[export] Hint Resolve eq_dec : core.

  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

End AtomModule.

(** ** Implementation of atoms *)
(******************************************************************************)
Module Atom <: AtomModule.

  Definition name: Type := nat.

  Definition t := name.

  Definition eq_dec := PeanoNat.Nat.eq_dec.

  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

  Lemma max_lt_r : forall x y z,
      x <= z -> x <= max y z.
  Proof.
    induction x.
    - auto with arith.
    - induction y.
      + auto with arith.
      + cbn. induction z. lia. auto with arith.
  Defined.

  Lemma nat_list_max : forall (xs : list nat),
      { n : nat | forall x, List.In x xs -> x <= n }.
  Proof.
    induction xs as [ | x xs [y H] ].
    - exists 0. inversion 1.
    - exists (max x y). intros z J.
      cbn in J. destruct J as [K | K].
      + subst. auto with arith.
      + auto using max_lt_r.
  Defined.

  Lemma name_fresh_for_list :
    forall (xs : list nat), { n : nat | ~ n ∈ xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H].
    exists (S x). intros J. lapply (H (S x)). lia. trivial.
  Defined.

  Definition fresh (l : list name) : name  :=
    match name_fresh_for_list l with
      (exist _ x _) => x
    end.

  Lemma fresh_not_in : forall l, ~ fresh l ∈ l.
  Proof.
    intro l. unfold fresh.
    destruct name_fresh_for_list. auto.
  Qed.

  Definition nat_of := fun (x : name) => (x : nat).
End Atom.

(** ** Alternate implementation of atoms *)
(******************************************************************************)
Module SmartAtom <: AtomModule.

  Definition name: Type := nat.
  Definition t := name.

  Definition eq_dec := PeanoNat.Nat.eq_dec.

  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

  (* Test if x is an element of l, returning a boolean *)
  Fixpoint list_in (x : name) (l : list name) : bool :=
    match l with
    | nil => false
    | y :: rest => (x ==b y) || list_in x rest
    end.


  (*
  Lemma name_fresh_for_list :
    forall (xs : list nat), { n : nat | ~ n ∈ xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H].
    exists (S x). intros J. lapply (H (S x)). lia. trivial.
  Defined.
  *)


  Fixpoint name_inb (x : name) (l : list name) : bool :=
    match l with
    | nil => false
    | y :: rest => (if x == y then true else false) || name_inb x rest
    end.

  Lemma name_inb_iff: forall x l,
      name_inb x l = true <-> x ∈ l.
  Proof.
    intros. induction l.
    - cbn. intuition.
    - cbn.
      rewrite <- IHl.
      clear IHl.
      destruct (name_inb x l).
      + rewrite Bool.orb_true_r. intuition.
      +  rewrite Bool.orb_false_r.
         destruct_eq_args x a; intuition.
  Qed.

  Lemma name_inb_iff_false: forall x l,
      name_inb x l = false <-> ~ (x ∈ l).
  Proof.
    intros.
    rewrite <- name_inb_iff.
    destruct (name_inb x l);
      intuition.
  Qed.

  Fixpoint max_not_in_list_rec
    (gas: name) (current_min: name)
    (l : list name) : name :=
    match gas with
    | 0 => if name_inb 0 l
          then current_min
          else 0
    | S g => if name_inb g l
            then max_not_in_list_rec g current_min l
            else max_not_in_list_rec g g l
    end.


  Definition fresh (l : list name) : name :=
    let max := foldMap (op := Monoid_op_max) (unit := Monoid_unit_max) id l
    in max_not_in_list_rec (S max) (S max) l.

  Compute max_not_in_list_rec 100 5 [0; 1; 2].
  Compute max_not_in_list_rec 100 5 [0; 1; 3; 4].
  Compute max_not_in_list_rec 100 5 [1; 2; 4; 6; 8].
  Compute max_not_in_list_rec 100 5 [0; 1; 2; 4; 6; 8].

  Compute fresh [].
  Compute fresh [0].
  Compute fresh [0; 1].
  Compute fresh [0; 2].

  Lemma fresh_not_in : forall l, ~ fresh l ∈ l.
  Proof.
    intro l. unfold fresh.
    induction l.
    - cbn. easy.
    - cbn in *.
  Admitted.

  Definition nat_of := fun (x : name) => (x : nat).

End SmartAtom.

(** ** Shorthands and notations *)
(******************************************************************************)
Notation name := SmartAtom.name.
Notation fresh := SmartAtom.fresh.
Notation fresh_not_in := SmartAtom.fresh_not_in.

(* Automatically unfold SmartAtom.eq *)
#[global] Arguments SmartAtom.eq /.

#[export] Instance EqDec_atom : @EqDec name eq eq_equivalence := SmartAtom.eq_dec.
