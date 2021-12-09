From Tealeaves Require Import
     Util.Prelude Util.EqDec_eq
     Functors.List.

Import SetlikeFunctor.Notations.
#[local] Open Scope tealeaves_scope.

(** This type has been borrowed from Metalib and lightly adapted for Tealeaves.
    https://github.com/plclub/metalib/blob/master/Metalib/MetatheoryAtom.v
 *)
Module Type ATOM <: UsualDecidableType.

  Parameter atom : Set.

  Definition t := atom.

  Parameter eq_dec : forall x y : atom, {x = y} + {x <> y}.

  Parameter atom_fresh_for_list :
    forall (xs : list t), {x : atom | ~ x ∈ xs}.

  Parameter fresh : list atom -> atom.

  Parameter fresh_not_in : forall l, ~ fresh l ∈ l.

  Parameter nat_of : atom -> nat.

  #[export] Hint Resolve eq_dec : core.

  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

End ATOM.

(** The implementation of the above interface is hidden for
    documentation purposes. *)
Module Atom : ATOM.

  (* begin hide *)
  Definition atom := nat.
  Definition t := atom.

  Definition eq_dec := PeanoNat.Nat.eq_dec.

  Lemma max_lt_r : forall x y z,
      x <= z -> x <= max y z.
  Proof.
    induction x. auto with arith.
    induction y. auto with arith.
    simpl. induction z. lia. auto with arith.
  Qed.

  Lemma nat_list_max : forall (xs : list nat),
      { n : nat | forall x, List.In x xs -> x <= n }.
  Proof.
    induction xs as [ | x xs [y H] ].
    (* case: nil *)
    exists 0. inversion 1.
    (* case: cons x xs *)
    exists (max x y). intros z J. simpl in J. destruct J as [K | K].
    subst. auto with arith.
    auto using max_lt_r.
  Qed.

  Lemma atom_fresh_for_list :
    forall (xs : list nat), { n : nat | ~ n ∈ xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H].
    exists (S x). intros J. lapply (H (S x)). lia. trivial.
  Qed.

  Definition fresh (l : list atom) :=
    match atom_fresh_for_list l with
      (exist _ x _) => x
    end.

  Lemma fresh_not_in : forall l, ~ fresh l ∈ l.
  Proof.
    intro l. unfold fresh.
    destruct atom_fresh_for_list. auto.
  Qed.

  Definition nat_of := fun (x : atom) => x.

  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

  (* end hide *)

End Atom.

Notation atom := Atom.atom.
Notation fresh := Atom.fresh.
Notation fresh_not_in := Atom.fresh_not_in.
Notation atom_fresh_for_list := Atom.atom_fresh_for_list.

(* Automatically unfold Atom.eq *)
Global Arguments Atom.eq /.

(** It is trivial to declare an instance of [EqDec] for [atom]. *)
Instance EqDec_atom : @EqDec atom eq eq_equivalence.
Proof.
  exact Atom.eq_dec.
Defined.
