From Tealeaves Require Export
  Classes.EqDec_eq
  Misc.NaturalNumbers.

From Tealeaves Require Import
  Theory.TraversableFunctor.

Import List.ListNotations.
Import ContainerFunctor.Notations.
Import Monoid.Notations.

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

(** ** Alternate implementation of atoms *)
(******************************************************************************)
Module Name <: AtomModule.

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
    (candidate: name) (current_min: name)
    (l : list name) : name :=
    match candidate with
    | 0 => if name_inb 0 l
          then current_min
          else 0
    | S next_candidate => if name_inb next_candidate l
            then max_not_in_list_rec next_candidate current_min l
            else max_not_in_list_rec next_candidate next_candidate l
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

  (*
  Lemma max_not_in_list_spec:
    forall (candidate: name) (current_min: name) (l: list name),
      current_min
      max_not_in_list_rec candidate current_min l


  Fixpoint max_not_in_list_rec
    (candidate: name) (current_min: name)
    (l : list name) : name :=
    *)

  Lemma fresh_not_in : forall l, ~ fresh l ∈ l.
  Proof.
    intro l.
    unfold fresh.
    induction l.
    - cbn.
      tauto.
    - rewrite foldMap_eq_foldMap_list.
      rewrite foldMap_list_cons.
      rewrite <- foldMap_eq_foldMap_list.
      change (id ?a) with a.
  Admitted.

  Definition nat_of := fun (x : name) => (x : nat).
End Name.

(** ** Shorthands and notations *)
(******************************************************************************)
Notation name := Name.name.
Notation atom := Name.name.
Notation fresh := Name.fresh.
Notation fresh_not_in := Name.fresh_not_in.

(* Automatically unfold Name.eq *)
#[global] Arguments Name.eq /.

#[export] Instance EqDec_name : @EqDec name eq eq_equivalence := Name.eq_dec.
